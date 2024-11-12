pub mod consts;
pub mod expr;

use consts::*;
use expr::*;
use im::{HashMap, HashSet};
use sexp::*;
use std::cmp::max;
use std::env::{self};
use std::fs::File;
use std::io::prelude::*;
use std::sync::atomic::Ordering;

type Stack = HashMap<String, usize>;

fn expr_vars(e: &Expr) -> usize {
    match e {
        Expr::Num(_) => 0,
        Expr::Boolean(_) => 0,
        Expr::Var(_) => 0,
        Expr::Input => 0,
        Expr::Add1(e) => expr_vars(e),
        Expr::Sub1(e) => expr_vars(e),
        Expr::Negate(e) => expr_vars(e),
        Expr::IsNum(e) => expr_vars(e),
        Expr::IsBool(e) => expr_vars(e),
        Expr::Loop(e, _) => expr_vars(e),
        Expr::Print(e) => expr_vars(e),
        Expr::Break(e, _) => expr_vars(e),
        Expr::Set(_, e) => expr_vars(e),
        Expr::If(cond_exp, then_exp, else_exp, _) => max(
            expr_vars(cond_exp),
            max(expr_vars(then_exp), expr_vars(else_exp)),
        ),
        Expr::Block(es) => es.iter().map(|e| expr_vars(e)).max().unwrap(),
        Expr::Add(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::Sub(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::Mul(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::Greater(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::GreaterEq(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::Lesser(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::LesserEq(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::Eq(lexp, rexp) => max(expr_vars(rexp), 1 + expr_vars(lexp)),
        Expr::Let(bind_list, bind_exp) => {
            let mut list_var = vec![];
            for (idx, bind) in bind_list.iter().enumerate() {
                list_var.push(idx + expr_vars(&bind.1));
            }
            let bind_exp_var = bind_list.len() + expr_vars(bind_exp);
            return max(*list_var.iter().max().unwrap(), bind_exp_var);
        }
        Expr::CallFun(_, param_list) => {
            let mut param_var = vec![];
            for (idx, param) in param_list.iter().enumerate() {
                param_var.push(idx + expr_vars(&param));
            }
            return match param_var.iter().max() {
                Some(p) => *p,
                None => 0,
            };
        }
        Expr::Vec(elems) => {
            let mut elem_var = vec![];
            for (idx, elem) in elems.iter().enumerate() {
                elem_var.push(idx + expr_vars(elem));
            }
            let max_elem_var = match elem_var.iter().max() {
                Some(p) => *p,
                None => 0,
            };
            return max(max_elem_var, elems.len());
        }
        Expr::VecGet(vector, idx_exp) => {
            let vector_vars = expr_vars(vector);
            let idx_vars = expr_vars(idx_exp);
            return max(vector_vars, max(idx_vars, 2));
        }
        Expr::DefFun(_, _, _) => 0,
    }
}

fn get_heap_cell(start_label: &str, arity: usize, free_vars: Vec<i32>, x86_insts: &mut Vec<Op>) {
    x86_insts.push(Op::Mov(
        Imm::Register(Reg::Rax),
        Imm::UnsignedSize(free_vars.len() + 2),
    ));
    x86_insts.push(Op::Mov(Imm::ArgRef(Reg::R12, 0), Imm::Register(Reg::Rax)));
    x86_insts.push(Op::Lea(Reg::Rcx, start_label.to_string()));
    x86_insts.push(Op::Mov(Imm::ArgRef(Reg::R12, 1), Imm::Register(Reg::Rcx)));
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::UnsignedSize(arity)));
    x86_insts.push(Op::Mov(Imm::ArgRef(Reg::R12, 2), Imm::Register(Reg::Rcx)));

    for (idx, var) in free_vars.iter().enumerate() {
        if var < &0 {
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::Register(Reg::R12)));
            x86_insts.push(Op::Offset(Reg::Rcx, 5));
            x86_insts.push(Op::Mov(
                Imm::ArgRef(Reg::R12, idx + 3),
                Imm::Register(Reg::Rcx),
            ));
        } else {
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rcx),
                Imm::MemRef(Reg::Rbp, *var as usize),
            ));
            x86_insts.push(Op::Mov(
                Imm::ArgRef(Reg::R12, idx + 3),
                Imm::Register(Reg::Rcx),
            ));
        }
    }
    let increment: i64 = {
        if (8 * (free_vars.len() + 3)) % 16 == 0 {
            8 * (free_vars.len() + 3) as i64
        } else {
            (8 * (free_vars.len() + 3) as i64) + 8
        }
    };
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::Register(Reg::R12)));
    x86_insts.push(Op::Offset(Reg::R12, increment as i64));
    x86_insts.push(Op::Offset(Reg::Rax, 5));
}

fn compile_defn(defn: &Expr, env: &Stack, x86_insts: &mut Vec<Op>) {
    let (fname, params, fbody) = match defn {
        Expr::DefFun(name, args, body) => (name, args, body),
        _ => panic!("Invalid function definiton given"),
    };
    let anon_count = ANON_FN_COUNT.load(Ordering::Relaxed);
    let fname = match fname {
        None => {
            ANON_FN_COUNT.store(anon_count + 1, Ordering::Relaxed);
            format!("{}_{}", ANON_LABEL, anon_count)
        }
        Some(name) => name.to_string(),
    };
    let free_vars = free_vars(defn);
    let mut free_arr: Vec<i32> = vec![];
    let mut new_env = Stack::new();
    for free in free_vars.clone() {
        new_env = new_env.update(free.to_string(), new_env.len() + 1);
        if free == fname {
            free_arr.push(-1);
        } else {
            free_arr.push(*env.get(&free.to_string()).expect("Invalid variable given") as i32);
        }
    }

    let start_label = format!("{}_{}", START_LABEL, fname);
    let body_label = format!("{}_{}", BODY_LABEL, fname);
    let exit_label = format!("{}_{}", EXIT_LABEL, fname);
    let finish_label = format!("{}_{}", FINISH_LABEL, fname);

    x86_insts.push(Op::Jmp(finish_label.clone(), None)); // Jump to finish
    x86_insts.push(Op::AddLabel(start_label.clone())); // Add start label
    compile_entry(defn, x86_insts, params.len()); // Add stack setup

    for (idx, var) in free_vars.iter().enumerate() {
        // Move free variables to the stack
        x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::ArgRef(Reg::Rbp, 2)));
        get_fn_tuple(idx + 2, 5, x86_insts);
        let vpos = new_env.get(var).expect("Invalid variable provided");
        x86_insts.push(Op::Mov(
            Imm::MemRef(Reg::Rbp, *vpos),
            Imm::Register(Reg::Rax),
        ));
    }

    for (idx, param) in params.iter().enumerate() {
        // Move params to the stack
        let vpos = new_env.len() + 1;
        new_env = new_env.update(param.to_string(), vpos);
        x86_insts.push(Op::Mov(
            Imm::Register(Reg::Rax),
            Imm::ArgRef(Reg::Rbp, idx + 3),
        ));
        x86_insts.push(Op::Mov(
            Imm::MemRef(Reg::Rbp, vpos),
            Imm::Register(Reg::Rax),
        ));
    }

    x86_insts.push(Op::AddLabel(body_label));
    compile_expr(fbody, x86_insts, &new_env, new_env.len(), &fname);
    x86_insts.push(Op::AddLabel(exit_label));
    compile_exit(x86_insts);
    x86_insts.push(Op::AddLabel(finish_label));
    get_heap_cell(&start_label, params.len(), free_arr, x86_insts);
}

fn compile_expr(e: &Expr, x86_insts: &mut Vec<Op>, env: &Stack, sp: usize, curr_fun: &String) {
    match e {
        // Match each Expr value to an x86 Op code and add it to the Op code list
        Expr::Num(n) => {
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedLong(*n as i64)))
        }
        Expr::Boolean(bval) => {
            if *bval == true {
                x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedInt(TRUE)));
            } else if *bval == false {
                x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedInt(FALSE)));
            }
        }
        Expr::Var(v) => {
            let vpos = match env.get(v) {
                Some(p) => p,
                None => {
                    panic!("Unbound variable identifier {}", v);
                }
            };
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::MemRef(Reg::Rbp, *vpos),
            ));
        }
        Expr::Input => {
            if *curr_fun == MAIN_FUN {
                x86_insts.push(Op::Input);
            } else {
                panic!("Invalid. Cannot use input inside a function that is not the main function");
            }
        }
        Expr::Add1(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Inc)
        }
        Expr::Sub1(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Dec)
        }
        Expr::Negate(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Negate)
        }
        Expr::IsBool(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::CheckBool);
        }
        Expr::IsNum(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::CheckNum);
        }
        Expr::Print(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rdi), Imm::Register(Reg::Rax)));
            x86_insts.push(Op::Call(Some(SNEK_PRINT_FUN.to_string())));
        }
        Expr::Add(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::Plus(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Sub(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::Minus(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Mul(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::Times(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Greater(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::Greater(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Lesser(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::Lesser(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::GreaterEq(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::GreaterEq(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::LesserEq(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::LesserEq(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Eq(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun);
            x86_insts.push(Op::Eq(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Let(bind_list, exp) => {
            let mut new_env = env.clone();
            let mut new_sp = sp;
            for bind in bind_list.iter() {
                compile_expr(&bind.1, x86_insts, &new_env, new_sp, curr_fun); // Compile the binding
                                                                              // expression
                                                                              // Why are we compiling the bind
                                                                              // list with update environment,
                                                                              // because each subsequent binding
                                                                              // needs to know not to trample on
                                                                              // the ones that came before it.
                x86_insts.push(Op::Mov(
                    Imm::MemRef(Reg::Rbp, new_sp + 1), // Increment the variable count. sp always points to the
                    // last slot that was filled. And so var_pos points to
                    // the next slot that must be filled.
                    Imm::Register(Reg::Rax),
                ));
                new_env = new_env.update(bind.0.to_string(), new_sp + 1);
                new_sp = new_sp + 1; // Increment sp so that it points to the last slot that was
                                     // filled.
            }
            compile_expr(exp, x86_insts, &new_env, new_sp, curr_fun); // Compile the bound expression in
                                                                      // the context of the binding
                                                                      // expression.
        }
        Expr::Set(bind_var, exp) => {
            compile_expr(exp, x86_insts, env, sp, curr_fun);
            let vpos = match env.get(bind_var) {
                Some(p) => p,
                None => panic!("Unbound variable identifier {}", bind_var),
            };
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, *vpos),
                Imm::Register(Reg::Rax),
            ));
        }
        Expr::Block(exp_list) => {
            for exp in exp_list {
                compile_expr(exp, x86_insts, env, sp, curr_fun);
            }
        }
        Expr::If(cond, then_exp, else_exp, label) => {
            let else_label = format!("{}{}", ELSE_LABEL, label);
            let end_label = format!("{}{}", FI_LABEL, label);
            compile_expr(cond, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Cmp(Imm::Register(Reg::Rax), Imm::Boolean(false)));
            x86_insts.push(Op::Jmp(else_label.to_string(), Some(Cond::Eq)));
            compile_expr(then_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Jmp(end_label.to_string(), None));
            x86_insts.push(Op::AddLabel(else_label));
            compile_expr(else_exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::AddLabel(end_label));
        }
        Expr::Loop(exp, label) => {
            let loop_label = format!("{}{}", LOOP_LABEL, label);
            let end_label = format!("{}{}", POOL_LABEL, label);
            x86_insts.push(Op::AddLabel(loop_label.clone()));
            compile_expr(exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Jmp(loop_label.to_string(), None));
            x86_insts.push(Op::AddLabel(end_label));
        }

        Expr::Break(exp, label) => {
            let end_label = format!("{}{}", POOL_LABEL, label);
            compile_expr(exp, x86_insts, env, sp, curr_fun);
            x86_insts.push(Op::Jmp(end_label.to_string(), None));
        }
        Expr::CallFun(fname, arguments) => {
            let fpos = env.get(fname).expect("Invalid function called");
            for arg in arguments.iter() {
                compile_expr(arg, x86_insts, env, sp, curr_fun);
                x86_insts.push(Op::Push(Reg::Rax));
            }
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::MemRef(Reg::Rbp, *fpos),
            ));
            x86_insts.push(Op::Push(Reg::Rax));
            arity_check(arguments.len(), x86_insts);
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::MemRef(Reg::Rbp, *fpos),
            ));
            get_fn_tuple(0, 5, x86_insts);
            x86_insts.push(Op::Call(None));
            x86_insts.push(Op::Offset(Reg::Rsp, 8 * (arguments.len() + 1) as i64));
        }
        Expr::DefFun(_, _, _) => {
            compile_defn(e, env, x86_insts);
        }
        Expr::Vec(elems) => {
            for (idx, elem) in elems.iter().enumerate() {
                // Compiling each expr and storing it on
                // the stack as a local variable.
                compile_expr(elem, x86_insts, env, sp + idx + 1, curr_fun);
                x86_insts.push(Op::Mov(
                    Imm::MemRef(Reg::Rbp, sp + idx + 1),
                    Imm::Register(Reg::Rax),
                ));
            } // Store the length of the vec as element 0
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::UnsignedSize(elems.len()),
            ));
            x86_insts.push(Op::Mov(Imm::MemRef(Reg::R12, 0), Imm::Register(Reg::Rax)));
            // Move the elements from the stack onto the heap one by one.
            for (idx, _elem) in elems.iter().enumerate() {
                x86_insts.push(Op::Mov(
                    Imm::Register(Reg::Rax),
                    Imm::MemRef(Reg::Rbp, sp + idx + 1),
                ));
                x86_insts.push(Op::Mov(
                    Imm::ArgRef(Reg::R12, idx + 1),
                    Imm::Register(Reg::Rax),
                ));
            }
            // Move the heap address into rax and offset R12 by 8 * num elements
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::Register(Reg::R12)));
            x86_insts.push(Op::Offset(Reg::Rax, 1));
            x86_insts.push(Op::Offset(Reg::R12, 8 * (elems.len() + 1) as i64));
        }
        Expr::VecGet(vec_exp, idx_exp) => {
            compile_expr(vec_exp, x86_insts, env, sp, curr_fun);
            // Type check to make sure this is a vector.
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::Register(Reg::Rax)));
            x86_insts.push(Op::And(Reg::Rcx, Imm::UnsignedSize(7)));
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rdi),
                Imm::SignedInt(ErrCode::InvalidType as i32),
            ));
            x86_insts.push(Op::Cmp(Imm::Register(Reg::Rcx), Imm::UnsignedSize(1)));
            x86_insts.push(Op::Jmp(ERROR_LABEL.to_string(), Some(Cond::Neq)));
            x86_insts.push(Op::Offset(Reg::Rax, -1)); // Undo prog representation of pointers.
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            )); // Stash
                // the
                // vector
                // address
                // temporarily on stack.
            compile_expr(idx_exp, x86_insts, env, sp + 1, curr_fun);
            // Type check to make sure this is a number.
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::Register(Reg::Rax)));
            x86_insts.push(Op::And(Reg::Rcx, Imm::UnsignedSize(1)));
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rdi),
                Imm::SignedInt(ErrCode::InvalidType as i32),
            ));
            x86_insts.push(Op::Cmp(Imm::Register(Reg::Rcx), Imm::UnsignedSize(0)));
            x86_insts.push(Op::Jmp(ERROR_LABEL.to_string(), Some(Cond::Neq)));
            // Check if idx is within range of vec.
            // Unprog idx.
            x86_insts.push(Op::Sar(Reg::Rax, Imm::UnsignedSize(1)));
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 2),
                Imm::Register(Reg::Rax),
            )); // Temporarily stash idx on the stack.
                // Load vec address back in Rax.
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::MemRef(Reg::Rbp, sp + 1),
            ));
            // Get 0th element into Rcx
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::MemRef(Reg::Rax, 0)));
            // Load idx back into Rax
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::MemRef(Reg::Rbp, sp + 2),
            ));
            // Compare if idx is greater than or equal to size.
            x86_insts.push(Op::Cmp(Imm::Register(Reg::Rax), Imm::Register(Reg::Rcx)));
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rdi),
                Imm::SignedInt(ErrCode::OutOfBounds as i32),
            ));
            x86_insts.push(Op::Jmp(ERROR_LABEL.to_string(), Some(Cond::Ge)));
            // Increment the idx if valid because idx of 0 matches the size and elements start from
            // 1.
            x86_insts.push(Op::Offset(Reg::Rax, 1));
            // Copy idx to Rcx if valid
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::Register(Reg::Rax)));
            // Load vec address back into Rax
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::MemRef(Reg::Rbp, sp + 1),
            ));
            // Load vec offset idx + 1
            x86_insts.push(Op::Mov(
                Imm::Register(Reg::Rax),
                Imm::RegRef(Reg::Rax, Reg::Rcx, "+".to_string()),
            ));
        }
    }
}

fn arity_check(arity: usize, x86_insts: &mut Vec<Op>) {
    get_fn_tuple(1, 5, x86_insts);
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::UnsignedSize(arity)));
    x86_insts.push(Op::Cmp(Imm::Register(Reg::Rax), Imm::Register(Reg::Rcx)));
    x86_insts.push(Op::Mov(
        Imm::Register(Reg::Rdi),
        Imm::SignedInt(ErrCode::ArityMismatch as i32),
    ));
    x86_insts.push(Op::Jmp(ERROR_LABEL.to_string(), Some(Cond::Neq)));
}
fn get_fn_tuple(index: usize, tag: i32, x86_insts: &mut Vec<Op>) {
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::Register(Reg::Rax)));
    x86_insts.push(Op::And(Reg::Rcx, Imm::SignedInt(7)));
    x86_insts.push(Op::Cmp(Imm::Register(Reg::Rcx), Imm::SignedInt(tag)));
    x86_insts.push(Op::Mov(
        Imm::Register(Reg::Rdi),
        Imm::SignedInt(ErrCode::InvalidFunction as i32),
    ));
    x86_insts.push(Op::Jmp(ERROR_LABEL.to_string(), Some(Cond::Neq)));
    x86_insts.push(Op::Offset(Reg::Rax, (-1 * tag) as i64));
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rcx), Imm::ArgRef(Reg::Rax, 0))); // Move size into
                                                                                // RCX
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rdi), Imm::UnsignedSize(index))); // Move index into
                                                                                // rdi
    x86_insts.push(Op::Cmp(Imm::Register(Reg::Rdi), Imm::Register(Reg::Rcx))); // Check if RDI >
                                                                               // RCX
    x86_insts.push(Op::Mov(
        Imm::Register(Reg::Rdi),
        Imm::SignedInt(ErrCode::OutOfBounds as i32),
    ));
    x86_insts.push(Op::Jmp(ERROR_LABEL.to_string(), Some(Cond::Ge))); // If greater, then jump
    x86_insts.push(Op::Mov(
        Imm::Register(Reg::Rax),
        Imm::ArgRef(Reg::Rax, index + 1),
    ));
}

fn compare_type(memref: &Imm) -> String {
    let mov_1_arg = format!("mov rdi, rax");
    let src_str = get_imm_val(memref);
    let mov_2_arg = format!("mov rsi, {}", src_str);
    let call_str = format!("call __compare_type__");
    format!("{}\n{}\n{}", mov_1_arg, mov_2_arg, call_str)
}

fn is_num_check_exp(memref: &Imm) -> String {
    match memref {
        Imm::MemRef(base_reg, offset) => {
            let reg_name = get_reg_name(base_reg);
            let mov_str = format!("mov rcx, [{} - 8 * {}]", reg_name, offset);
            let inv_type_str = get_not_num_str();
            format!("{}\n{}", mov_str, inv_type_str)
        }
        Imm::Register(reg) => {
            let reg_name = get_reg_name(reg);
            let mov_str = format!("mov rcx, {}", reg_name);
            let inv_type_str = get_not_num_str();
            format!("{}\n{}", mov_str, inv_type_str)
        }
        _ => panic!("Invalid memory reference provided"),
    }
}

fn undo_prog_form(memref: &Imm) -> String {
    match memref {
        Imm::Register(reg) => {
            let reg_name = get_reg_name(reg);
            let mov_str = format!("mov rcx, {}", reg_name);
            let sar_str = format!("sar rcx, 0x1");
            let mov_back_str = format!("mov {}, rcx", reg_name);
            format!("{}\n{}\n{}", mov_str, sar_str, mov_back_str)
        }
        Imm::MemRef(base_reg, offset) => {
            let reg_name = get_reg_name(base_reg);
            let mov_str = format!("mov rcx, [{} - 8 * {}]", reg_name, offset);
            let sar_str = format!("sar rcx, 0x1");
            let mov_back_str = format!("mov [{} - 8 * {}], rcx", reg_name, offset);
            format!("{}\n{}\n{}", mov_str, sar_str, mov_back_str)
        }
        _ => panic!("Invalid memory reference provided"),
    }
}

fn get_reg_name(reg: &Reg) -> String {
    match reg {
        Reg::Rax => "rax".to_string(),
        Reg::Rcx => "rcx".to_string(),
        Reg::Rsp => "rsp".to_string(),
        Reg::Rdi => "rdi".to_string(),
        Reg::Rsi => "rsi".to_string(),
        Reg::Rbp => "rbp".to_string(),
        Reg::R12 => "r12".to_string(),
    }
}

fn get_imm_val(imm: &Imm) -> String {
    match imm {
        Imm::Register(reg) => get_reg_name(reg),
        Imm::SignedLong(n) => format!("{}", n),
        Imm::SignedInt(n) => format!("{}", n),
        Imm::UnsignedSize(n) => format!("{}", n),
        Imm::MemRef(base_reg, offset) => {
            let base_str = get_reg_name(base_reg);
            format!("[{} - 8 * {}]", base_str, offset)
        }
        Imm::Boolean(bval) => {
            if *bval == true {
                format!("{}", TRUE)
            } else {
                format!("{}", FALSE)
            }
        }
        Imm::ArgRef(base_reg, offset) => {
            let base_str = get_reg_name(base_reg);
            format!("[{} + 8 * {}]", base_str, offset)
        }
        Imm::RegRef(lreg, rreg, sign) => {
            let lreg_str = get_reg_name(lreg);
            let rreg_str = get_reg_name(rreg);
            format!("[{} {} 8 * {}]", lreg_str, sign, rreg_str)
        }
    }
}

fn get_overflow_str() -> String {
    let err_code = ErrCode::Overflow as i32;
    let mov_errcode = format!("mov rdi, {}", err_code);
    let zero_rcx = format!("mov rcx, 0");
    let seto_str = format!("seto cl");
    let cmp_str = format!("cmp rcx, 0x1");
    let jump_carry = format!("je {}", ERROR_LABEL);
    format!(
        "{}\n{}\n{}\n{}\n{}",
        mov_errcode, zero_rcx, seto_str, cmp_str, jump_carry
    )
}

fn get_not_num_str() -> String {
    let err_code = ErrCode::InvalidType as i32;
    let and_str = format!("and rcx, 0x1");
    let cmp_str = format!("cmp rcx, 0x1");
    let mov_errcode = format!("mov rdi, {}", err_code);
    let jump_equal = format!("je {}", ERROR_LABEL);
    format!("{}\n{}\n{}\n{}", and_str, cmp_str, mov_errcode, jump_equal)
}

fn get_jump_string(cond: &Option<Cond>) -> String {
    match cond {
        None => format!("jmp"),
        Some(c) => match c {
            Cond::Eq => format!("je"),
            Cond::Neq => format!("jne"),
            Cond::Ge => format!("jge"),
        },
    }
}

fn x86_instruction_string(instr: &Op) -> String {
    match instr {
        // Convert each x86 Opcode into its string format
        Op::Mov(dst, src) => {
            let dst_str = get_imm_val(dst);
            let src_str = get_imm_val(src);
            format!("mov {}, {}", dst_str, src_str)
        }
        Op::Inc => {
            let inv_typ_exp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let undo_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let overflow_str = get_overflow_str();
            let shl_str = format!("shl rax, 0x1");
            let inc_str = format!("inc rax");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_exp_str, undo_str, inc_str, overflow_str, shl_str, overflow_str
            )
        }
        Op::Dec => {
            let inv_typ_exp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let undo_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let overflow_str = get_overflow_str();
            let shl_str = format!("shl rax, 0x1");
            let dec_str = format!("dec rax");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_exp_str, undo_str, dec_str, overflow_str, shl_str, overflow_str
            )
        }
        Op::Negate => {
            let inv_typ_exp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let undo_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let overflow_str = get_overflow_str();
            let shl_str = format!("shl rax, 0x1");
            let neg_str = format!("neg rax");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_exp_str, undo_str, neg_str, overflow_str, shl_str, overflow_str
            )
        }
        Op::Call(fname) => {
            let fname = match fname {
                None => "rax",
                Some(name) => name,
            };
            format!("call {}", fname)
        }
        Op::Plus(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let undo_lexp_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let undo_rexp_str = undo_prog_form(r_off);
            let overflow_str = get_overflow_str();
            let src_str = get_imm_val(r_off);
            let add_str = format!("add rax, {}", src_str);
            let shl_str = format!("shl rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                undo_lexp_str,
                undo_rexp_str,
                add_str,
                overflow_str,
                shl_str,
                overflow_str
            )
        }
        Op::Minus(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let undo_lexp_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let undo_rexp_str = undo_prog_form(r_off);
            let overflow_str = get_overflow_str();
            let src_str = get_imm_val(r_off);
            let sub_str = format!("sub rax, {}", src_str);
            let shl_str = format!("shl rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                undo_lexp_str,
                undo_rexp_str,
                sub_str,
                overflow_str,
                shl_str,
                overflow_str
            )
        }
        Op::Times(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let undo_lexp_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let undo_rexp_str = undo_prog_form(r_off);
            let overflow_str = get_overflow_str();
            let src_str = get_imm_val(r_off);
            let mul_str = format!("imul rax, {}", src_str);
            let shl_str = format!("shl rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                undo_lexp_str,
                undo_rexp_str,
                mul_str,
                overflow_str,
                shl_str,
                overflow_str
            )
        }
        Op::CheckBool => {
            let and_str = format!("and rax, 0x3");
            let cmp_str = format!("cmp rax, 0x3");
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("sete al");
            let shl_str = format!("shl rax, 1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                and_str, cmp_str, zero_str, setcc_str, shl_str, or_str, shl_str, or_str
            )
        }
        Op::CheckNum => {
            let and_str = format!("and rax, 0x1");
            let xor_str = format!("xor rax, 0x1");
            let shl_str = format!("shl rax, 1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                and_str, xor_str, shl_str, or_str, shl_str, or_str
            )
        }
        Op::Input => {
            format!("mov rax, [rbp - 8]")
        }
        Op::Greater(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setg al"); // True is 1 False is 0
            let shl_str = format!("shl rax, 0x1"); // True is 2 False is 0
            let or_str = format!("or rax, 0x1"); // True is 3 False is 1. One more shift true is 6
                                                 // and false is 2. One more or, true is 7 and
                                                 // false is 3.
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                cmp_str,
                zero_str,
                setcc_str,
                shl_str,
                or_str,
                shl_str,
                or_str
            )
        }
        Op::Lesser(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setl al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                cmp_str,
                zero_str,
                setcc_str,
                shl_str,
                or_str,
                shl_str,
                or_str
            )
        }
        Op::GreaterEq(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setge al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                cmp_str,
                zero_str,
                setcc_str,
                shl_str,
                or_str,
                shl_str,
                or_str
            )
        }
        Op::LesserEq(r_off) => {
            let inv_typ_lexp_str = is_num_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = is_num_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setle al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str,
                inv_typ_rexp_str,
                cmp_str,
                zero_str,
                setcc_str,
                shl_str,
                or_str,
                shl_str,
                or_str
            )
        }
        Op::Eq(r_off) => {
            let check_type_str = compare_type(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("sete al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}",
                check_type_str, cmp_str, zero_str, setcc_str, shl_str, or_str, shl_str, or_str
            )
        }
        Op::Cmp(lval, rval) => {
            let lval_str = get_imm_val(lval);
            let rval_str = get_imm_val(rval);
            format!("cmp {}, {}", lval_str, rval_str)
        }
        Op::AddLabel(label) => {
            format!("{}:", label)
        }
        Op::Jmp(label, cond) => {
            let jmp_string = get_jump_string(cond);
            format!("{} {}", jmp_string, label)
        }
        Op::Push(reg) => {
            let reg_name = get_reg_name(reg);
            format!("push {}", reg_name)
        }
        Op::Pop(reg) => {
            let reg_name = get_reg_name(reg);
            format!("pop {}", reg_name)
        }
        Op::Ret => {
            format!("ret")
        }
        Op::Offset(reg, off) => {
            let reg_name = get_reg_name(reg);
            let offset_str = if *off > 0 {
                format!("add {}, {}", reg_name, off)
            } else {
                format!("sub {}, {}", reg_name, -off)
            };
            return offset_str;
        }
        Op::And(reg, imm) => {
            let reg_name = get_reg_name(reg);
            let imm_val = get_imm_val(imm);
            format!("and {}, {}", reg_name, imm_val)
        }
        Op::Sar(reg, imm) => {
            let reg_name = get_reg_name(reg);
            let imm_val = get_imm_val(imm);
            format!("sar {}, {}", reg_name, imm_val)
        }
        Op::Lea(reg, label) => {
            let reg_name = get_reg_name(reg);
            format!("lea {}, qword[rel {}]", reg_name, label)
        }
    }
}

fn dump_instruction_strings(x86_insts: Vec<Op>) -> String {
    // Iterate over the list of Op codes in the list and map each one to its string equivalent.
    //Once done, collect it and join into a \n separated string
    return x86_insts
        .iter()
        .map(|i| x86_instruction_string(i))
        .collect::<Vec<String>>()
        .join("\n");
}

fn prog_expr(defs: Vec<Expr>, expr: Box<Expr>) -> Expr {
    let mut defn_list: HashSet<String> = HashSet::new();
    let mut bind_list: Vec<(String, Expr)> = Vec::new();
    for defn in defs {
        if let Expr::DefFun(name, ..) = &defn {
            let fname = name.clone().expect("Invalid function name provided!");
            if defn_list.contains(&fname) {
                panic!("Invalid function definition provided! Duplicates found");
            } else {
                defn_list.insert(fname.clone());
                bind_list.push((fname, defn));
            }
        } else {
            panic!("Invalid function provided!");
        }
    }
    if bind_list.len() == 0 {
        *expr
    } else {
        Expr::Let(bind_list, expr)
    }
}

fn parse_prog(prog: Sexp, break_stack: &mut Vec<u64>) -> Expr {
    let Sexp::List(def_expr) = prog else {
        panic!("Invalid S Expression Provided")
    };
    if let [defns @ .., expr] = &def_expr[..] {
        let funs: Vec<Expr> = defns
            .iter()
            .map(|e| parse_fn(e.clone(), break_stack))
            .collect();
        let expr = Box::new(parse_expr(expr, break_stack));
        prog_expr(funs, expr)
    } else {
        panic!("Invalid program provided")
    }
}

fn read_file(file_name: String) -> String {
    let mut contents = String::new();
    let mut in_file = File::open(file_name).expect("Invalid file given:{file_name}");
    in_file
        .read_to_string(&mut contents)
        .expect("Invalid file given:{file_name}");
    return contents;
}

fn write_file(file_name: String, program: String) {
    let mut out_file = File::create(file_name).expect("Invalid output file given");
    out_file
        .write_all(program.as_bytes())
        .expect("Invalid output file");
}

fn free_vars(expr: &Expr) -> HashSet<String> {
    match expr {
        Expr::Num(_) | Expr::Input | Expr::Boolean(_) => HashSet::new(),
        Expr::Var(x) => HashSet::unit(x.to_string()),
        Expr::DefFun(_name, args, body) => {
            let fargs = args;
            let fbody = body;
            let mut free_body = free_vars(&fbody);
            for arg in fargs {
                free_body = free_body.without(arg);
            }
            return free_body;
        }
        Expr::Add1(e)
        | Expr::Sub1(e)
        | Expr::Negate(e)
        | Expr::Set(_, e)
        | Expr::Loop(e, _)
        | Expr::Break(e, _)
        | Expr::Print(e)
        | Expr::IsBool(e)
        | Expr::IsNum(e) => free_vars(&e),
        Expr::Eq(e1, e2)
        | Expr::Lesser(e1, e2)
        | Expr::Greater(e1, e2)
        | Expr::GreaterEq(e1, e2)
        | Expr::LesserEq(e1, e2)
        | Expr::Add(e1, e2)
        | Expr::Sub(e1, e2)
        | Expr::VecGet(e1, e2)
        | Expr::Mul(e1, e2) => {
            let free_e1 = free_vars(&e1);
            let free_e2 = free_vars(&e2);
            free_e1.union(free_e2)
        }
        Expr::If(e1, e2, e3, _) => {
            let free_e1 = free_vars(&e1);
            let free_e2 = free_vars(&e2);
            let free_e3 = free_vars(&e3);
            free_e1.union(free_e2.union(free_e3))
        }
        Expr::Vec(es) | Expr::Block(es) => {
            let mut free_es = HashSet::new();
            for e in es {
                let free_e = free_vars(&e);
                free_es = free_es.union(free_e);
            }
            return free_es;
        }
        Expr::CallFun(f, exprs) => {
            let mut free_exprs = HashSet::new();
            let free_f: im::HashSet<String> = HashSet::unit(f.to_string());
            for expr in exprs {
                let free_expr = free_vars(&expr);
                free_exprs = free_exprs.union(free_expr);
            }
            free_exprs = free_exprs.union(free_f);
            return free_exprs;
        }
        Expr::Let(binds, eval) => {
            let mut free_eval = free_vars(eval);
            let mut free_binds: im::HashSet<String> = HashSet::new();
            for bind in binds {
                let bind_name = &bind.0;
                let bind_expr = &bind.1;
                free_eval = free_eval.without(bind_name);
                let free_bind_expr = free_vars(bind_expr);
                free_binds = free_binds.union(free_bind_expr);
            }
            free_eval = free_eval.union(free_binds);
            return free_eval;
        }
    }
}

fn compile_entry(expr: &Expr, x86_insts: &mut Vec<Op>, env_len: usize) {
    let free_vars = free_vars(expr);
    let num_vars = match expr {
        Expr::DefFun(_name, _params, body) => expr_vars(body),
        _ => expr_vars(expr),
    };
    let total_space = free_vars.len() + num_vars + env_len;
    let total_space = -8 * total_space as i64;
    x86_insts.push(Op::Push(Reg::Rbp));
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rbp), Imm::Register(Reg::Rsp)));
    x86_insts.push(Op::Offset(Reg::Rsp, total_space));
}

fn compile_exit(x86_insts: &mut Vec<Op>) {
    x86_insts.push(Op::Mov(Imm::Register(Reg::Rsp), Imm::Register(Reg::Rbp)));
    x86_insts.push(Op::Pop(Reg::Rbp));
    x86_insts.push(Op::Ret);
}

fn compile_main_entry(expr: &Expr, x86_insts: &mut Vec<Op>) {
    x86_insts.push(Op::AddLabel(MAIN_FUN.to_string()));
    compile_entry(expr, x86_insts, 1);
    x86_insts.push(Op::Push(Reg::R12));
    x86_insts.push(Op::Mov(Imm::MemRef(Reg::Rbp, 1), Imm::Register(Reg::Rdi)));
    x86_insts.push(Op::Mov(Imm::Register(Reg::R12), Imm::Register(Reg::Rsi)));
}

fn compile_main_exit(x86_insts: &mut Vec<Op>) {
    x86_insts.push(Op::Pop(Reg::R12));
    compile_exit(x86_insts);
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let in_contents = read_file(args[1].clone());
    let mut break_stack = Vec::new();

    let prog_sexp = format!("({})", in_contents);
    let prog_sexp = parse(&prog_sexp).expect("Invalid S Expression Provided");
    let prog_expr = parse_prog(prog_sexp, &mut break_stack);

    let mut x86_insts: Vec<Op> = vec![];

    let mut main_stack = Stack::new(); // Main always takes an argument of input
    main_stack.insert(INPUT_LABEL.to_string(), 1);
    compile_main_entry(&prog_expr, &mut x86_insts);

    compile_expr(
        &prog_expr,
        &mut x86_insts,
        &main_stack,
        main_stack.len(),
        &MAIN_FUN.to_string(),
    );
    compile_main_exit(&mut x86_insts);

    let result = dump_instruction_strings(x86_insts);

    let asm_program = format!(
        "section .text
extern snek_error
extern snek_print
{}
global __main__
{}:
call snek_error
{}
",
        COMPARE_TYPES_FN, ERROR_LABEL, result
    );

    write_file(args[2].clone(), asm_program);
}
