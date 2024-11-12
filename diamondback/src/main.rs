use im::{HashMap, HashSet};
use sexp::Atom::*;
use sexp::*;
use std::cmp::max;
use std::env;
use std::fs::File;
use std::io::prelude::*;
use std::sync::atomic::{AtomicU64, Ordering};

static IF_LABEL_COUNT: AtomicU64 = AtomicU64::new(0);
static LOOP_LABEL_COUNT: AtomicU64 = AtomicU64::new(0);

static MAIN_FUN: &str = "__main__";
static BODY_LABEL: &str = "__body__";
static FI_LABEL: &str = "__fi__";
static ELSE_LABEL: &str = "__else__";
static LOOP_LABEL: &str = "__loop__";
static POOL_LABEL: &str = "__pool__";
static INPUT_LABEL: &str = "__input__";
static SNEK_PRINT_FUN: &str = "snek_print";
static ERROR_LABEL: &str = "__error__";

enum ErrCode {
    Overflow = 1,
    InvalidType = 2,
}

#[derive(Debug)]
enum Cond {
    Eq,
}

#[derive(Debug)]
enum Expr {
    // An enum of all possible syntax expressions.
    Num(i64),        // Num is a 63 bit integer
    Boolean(bool),   // Boolean is either true or false
    Var(String),     // Variable is just a name
    Input,           // Input takes an input from the runtime
    Add1(Box<Expr>), // Add1, Sub1 and Negate are expressions which can contain a sub expression
    Sub1(Box<Expr>),
    Negate(Box<Expr>), // IsBool and IsNum do type checking
    IsBool(Box<Expr>),
    IsNum(Box<Expr>),
    Print(Box<Expr>),
    Add(Box<Expr>, Box<Expr>), // Add, Sub and Mul take two operands
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Greater(Box<Expr>, Box<Expr>),
    Lesser(Box<Expr>, Box<Expr>),
    GreaterEq(Box<Expr>, Box<Expr>),
    LesserEq(Box<Expr>, Box<Expr>),
    Eq(Box<Expr>, Box<Expr>),
    Set(String, Box<Expr>), // Set bindings take a binding and update it to the expression value
    Let(Vec<(String, Expr)>, Box<Expr>), // Let bindings take a binding list and a bound expression
    Block(Vec<Expr>),       // Block takes a list of statements
    If(Box<Expr>, Box<Expr>, Box<Expr>, String),
    Loop(Box<Expr>, String),
    Break(Box<Expr>, String),
    CallFun(String, Vec<Expr>),
    DefFun(String, Box<Expr>, usize, i64),
}

#[derive(Debug)]
enum Reg {
    Rax,
    Rsp,
    Rdi,
    Rbp,
}

#[derive(Debug)]
enum Imm {
    // Imms can be Signed Ints or Memory References or Registers
    SignedInt(i64),
    MemRef(Reg, usize),
    Register(Reg),
    Boolean(bool),
    ArgRef(usize),
}

#[derive(Debug)]
enum Op {
    // An enum of all possible x86 op codes
    Input,
    Inc,
    Dec,
    Negate,
    CheckBool,
    CheckNum,
    Call(String),
    Mov(Imm, Imm), // Mov takes 2 immediate values
    Plus(Imm),     // Plus, Minus and Times take one immediate value and the other value is
    // explicitly the Rax register
    Minus(Imm),
    Times(Imm),
    Greater(Imm),
    Lesser(Imm),
    GreaterEq(Imm),
    LesserEq(Imm),
    Eq(Imm),
    Cmp(Imm, Imm),
    AddLabel(String),
    Jmp(String, Option<Cond>),
    Push(Reg),
    Pop(Reg),
    Ret,
    Offset(Reg, i64),
}

type Stack = HashMap<String, usize>;

fn is_duplicate(var_name: String, list: &mut Vec<(String, Expr)>) -> bool {
    // Check for a
    // duplicate binding
    for binding in list.iter() {
        if binding.0 == var_name {
            panic!("Duplicate binding found!");
        }
    }
    return false;
}

fn is_correct_call(
    fname: String,
    param_list: Vec<Sexp>,
    defn_map: &HashMap<String, (Sexp, Vec<String>)>,
) -> bool {
    let valid_fn = defn_map.contains_key(&fname);
    let valid_params = &defn_map
        .get(&fname)
        .expect("Invalid function provided. Please call a valid defined function")
        .1;
    let valid_params = valid_params.len() == param_list.len();
    return valid_fn && valid_params;
}

fn get_binding(
    bind_sexp: &Sexp,
    list: &mut Vec<(String, Expr)>,
    break_stack: &mut Vec<u64>,
    defn_map: &HashMap<String, (Sexp, Vec<String>)>,
) {
    // Split up the binding list
    // into var name + binding expr
    match bind_sexp {
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(var_name)), e]
                if is_duplicate(var_name.to_string(), list) == false
                    && check_valid(var_name) == true =>
            {
                list.push((var_name.to_string(), parse_expr(e, break_stack, defn_map)))
            }
            _ => panic!("Invalid let expression provided"),
        },
        _ => panic!("Invalid let expression provided"),
    }
}

fn parse_bind_list(
    sexp_bind_list: &Vec<Sexp>,
    break_stack: &mut Vec<u64>,
    defn_map: &HashMap<String, (Sexp, Vec<String>)>,
) -> Vec<(String, Expr)> {
    // Parse binding SExps into
    // binding Exprs
    let mut split_list: Vec<(String, Expr)> = vec![];
    for bind_sexp in sexp_bind_list.iter() {
        get_binding(bind_sexp, &mut split_list, break_stack, defn_map);
    }
    let bind_list = split_list;
    return bind_list;
}

fn is_keyword(var_name: &String) -> bool {
    // Check if variable name is a keyword
    let keyword_list = vec![
        "add1", "sub1", "negate", "let", "true", "false", "if", "set!", "block", "break", "loop",
        "input", "print",
    ];
    keyword_list.contains(&var_name.as_str())
}

fn check_valid(var_name: &String) -> bool {
    // Should add the regexp checker here
    if is_keyword(var_name) == true {
        panic!("Identifer name matches that of keyword");
    }
    return true;
}

fn bounds_check(num: i64) -> bool {
    let sign = num > 0;
    let prog_num = num << 1;
    let unprog_num = prog_num >> 1;
    let prog_sign = unprog_num > 0;
    if sign != prog_sign {
        panic!("Overflow occured. Invalid 32 bit number provided");
    }
    return true;
}

fn parse_expr(
    s: &Sexp,
    break_stack: &mut Vec<u64>,
    defn_map: &HashMap<String, (Sexp, Vec<String>)>,
) -> Expr {
    match s {
        // Match each possible s expression value to either an atomic value or a list of s expressions
        Sexp::Atom(I(n)) if bounds_check(*n) == true => {
            Expr::Num(i64::try_from(*n << 1).expect("Invalid number given"))
        } // If it is an atomic number, return a number
        Sexp::Atom(S(var)) if is_keyword(var) == false => Expr::Var(var.to_string()),
        Sexp::Atom(S(op)) if op == "true" => Expr::Boolean(true),
        Sexp::Atom(S(op)) if op == "false" => Expr::Boolean(false),
        Sexp::Atom(S(op)) if op == "input" => Expr::Input,
        Sexp::List(vec) => {
            // If it is a list of s expressions match each s expression again
            match &vec[..] {
                // Match each op code and return the corresponding Expr with the argument passed in
                [Sexp::Atom(S(op)), e] if op == "add1" => {
                    Expr::Add1(Box::new(parse_expr(e, break_stack, defn_map)))
                }
                [Sexp::Atom(S(op)), e] if op == "sub1" => {
                    Expr::Sub1(Box::new(parse_expr(e, break_stack, defn_map)))
                }
                [Sexp::Atom(S(op)), e] if op == "negate" => {
                    Expr::Negate(Box::new(parse_expr(e, break_stack, defn_map)))
                }
                [Sexp::Atom(S(op)), e] if op == "isbool" => {
                    Expr::IsBool(Box::new(parse_expr(e, break_stack, defn_map)))
                }
                [Sexp::Atom(S(op)), e] if op == "isnum" => {
                    Expr::IsNum(Box::new(parse_expr(e, break_stack, defn_map)))
                }
                [Sexp::Atom(S(op)), e] if op == "print" => {
                    Expr::Print(Box::new(parse_expr(e, break_stack, defn_map)))
                }
                [Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::Add(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::Sub(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::Mul(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == ">" => Expr::Greater(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "<" => Expr::Lesser(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == ">=" => Expr::GreaterEq(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "<=" => Expr::LesserEq(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "=" => Expr::Eq(
                    Box::new(parse_expr(e1, break_stack, defn_map)),
                    Box::new(parse_expr(e2, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), Sexp::List(sexp_bind_list), eval] if op == "let" => {
                    let bind_list = parse_bind_list(sexp_bind_list, break_stack, defn_map);
                    let eval_expr = parse_expr(eval, break_stack, defn_map);
                    if bind_list.len() == 0 {
                        panic!("Invalid list of bindings given! Please provide atleast one binding in the list")
                    }
                    Expr::Let(bind_list, Box::new(eval_expr))
                }
                [Sexp::Atom(S(op)), Sexp::Atom(S(var)), e] if op == "set!" => Expr::Set(
                    var.to_string(),
                    Box::new(parse_expr(e, break_stack, defn_map)),
                ),
                [Sexp::Atom(S(op)), exp_list @ ..] if op == "block" => {
                    let mut split_list: Vec<Expr> = vec![];
                    if exp_list.len() == 0 {
                        panic!("Invalid list of expressions given. Please provide atleast one statement in the block")
                    }
                    for exp in exp_list.iter() {
                        let parsed_expr = parse_expr(exp, break_stack, defn_map);
                        split_list.push(parsed_expr);
                    }
                    Expr::Block(split_list)
                }
                [Sexp::Atom(S(op)), cond, then_exp, else_exp] if op == "if" => {
                    let curr_count = IF_LABEL_COUNT.load(Ordering::Relaxed);
                    IF_LABEL_COUNT.store(curr_count + 1, Ordering::Relaxed);
                    Expr::If(
                        Box::new(parse_expr(cond, break_stack, defn_map)),
                        Box::new(parse_expr(then_exp, break_stack, defn_map)),
                        Box::new(parse_expr(else_exp, break_stack, defn_map)),
                        curr_count.to_string(),
                    )
                }
                [Sexp::Atom(S(op)), e] if op == "loop" => {
                    let curr_loop_count = LOOP_LABEL_COUNT.load(Ordering::Relaxed);
                    LOOP_LABEL_COUNT.store(curr_loop_count + 1, Ordering::Relaxed);
                    break_stack.push(curr_loop_count); // Push the latest loop label onto the
                                                       // break stack so that we know any breaks
                                                       // inside the loop body belong to this loop
                                                       // label
                    let loop_expr = Expr::Loop(
                        Box::new(parse_expr(e, break_stack, defn_map)),
                        curr_loop_count.to_string(),
                    );
                    break_stack.pop(); // Pop the break stack since we are outside of that loop
                                       // body
                    return loop_expr;
                }
                [Sexp::Atom(S(op)), e] if op == "break" => {
                    let next_to_break: u64 = *break_stack
                        .last()
                        .expect("Invalid break present without loop");
                    Expr::Break(
                        Box::new(parse_expr(e, break_stack, defn_map)),
                        next_to_break.to_string(),
                    )
                }
                [Sexp::Atom(S(fname)), param_list @ ..]
                    if is_correct_call(fname.to_string(), param_list.to_vec(), defn_map)
                        == true =>
                {
                    let mut args_list: Vec<Expr> = vec![];
                    for param in param_list.iter().rev() {
                        let param_expr = parse_expr(param, break_stack, defn_map);
                        args_list.push(param_expr);
                    }
                    Expr::CallFun(fname.to_string(), args_list)
                }

                _ => panic!("Invalid S expression vector provided: {:?}", vec),
            }
        }
        _ => panic!("Invalid S expression provided: {:?}", s), // If you don't match with anything, print an error
    }
}

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
        _ => panic!("Invalid expression provided"),
    }
}

fn compile_expr(
    e: &Expr,
    x86_insts: &mut Vec<Op>,
    env: &Stack,
    sp: usize,
    curr_fun: &String,
    is_tr: bool,
) {
    match e {
        // Match each Expr value to an x86 Op code and add it to the Op code list
        Expr::Num(n) => x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedInt(*n as i64))),
        Expr::Boolean(bval) => {
            if *bval == true {
                x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedInt(3)));
            } else if *bval == false {
                x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedInt(1)));
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
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Inc)
        }
        Expr::Sub1(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Dec)
        }
        Expr::Negate(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Negate)
        }
        Expr::IsBool(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::CheckBool);
        }
        Expr::IsNum(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::CheckNum);
        }
        Expr::Print(sub_exp) => {
            compile_expr(sub_exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rdi), Imm::Register(Reg::Rax)));
            x86_insts.push(Op::Call(SNEK_PRINT_FUN.to_string()));
        }
        Expr::Add(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::Plus(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Sub(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::Minus(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Mul(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::Times(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Greater(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::Greater(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Lesser(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::Lesser(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::GreaterEq(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::GreaterEq(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::LesserEq(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::LesserEq(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Eq(lexp, rexp) => {
            compile_expr(rexp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Mov(
                Imm::MemRef(Reg::Rbp, sp + 1),
                Imm::Register(Reg::Rax),
            ));
            compile_expr(lexp, x86_insts, env, sp + 1, curr_fun, false);
            x86_insts.push(Op::Eq(Imm::MemRef(Reg::Rbp, sp + 1)));
        }
        Expr::Let(bind_list, exp) => {
            let mut new_env = env.clone();
            let mut new_sp = sp;
            for bind in bind_list.iter() {
                compile_expr(&bind.1, x86_insts, &new_env, new_sp, curr_fun, false); // Compile the binding
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
            compile_expr(exp, x86_insts, &new_env, new_sp, curr_fun, is_tr); // Compile the bound expression in
                                                                             // the context of the binding
                                                                             // expression.
        }
        Expr::Set(bind_var, exp) => {
            compile_expr(exp, x86_insts, env, sp, curr_fun, false);
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
            for (idx, exp) in exp_list.iter().enumerate() {
                compile_expr(
                    exp,
                    x86_insts,
                    env,
                    sp,
                    curr_fun,
                    is_tr && idx == exp_list.len() - 1,
                );
            }
        }
        Expr::If(cond, then_exp, else_exp, label) => {
            let else_label = format!("{}{}", ELSE_LABEL, label);
            let end_label = format!("{}{}", FI_LABEL, label);
            compile_expr(cond, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Cmp(Imm::Register(Reg::Rax), Imm::Boolean(false)));
            x86_insts.push(Op::Jmp(else_label.to_string(), Some(Cond::Eq)));
            compile_expr(then_exp, x86_insts, env, sp, curr_fun, is_tr);
            x86_insts.push(Op::Jmp(end_label.to_string(), None));
            x86_insts.push(Op::AddLabel(else_label));
            compile_expr(else_exp, x86_insts, env, sp, curr_fun, is_tr);
            x86_insts.push(Op::AddLabel(end_label));
        }
        Expr::Loop(exp, label) => {
            let loop_label = format!("{}{}", LOOP_LABEL, label);
            let end_label = format!("{}{}", POOL_LABEL, label);
            x86_insts.push(Op::AddLabel(loop_label.clone()));
            compile_expr(exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Jmp(loop_label.to_string(), None));
            x86_insts.push(Op::AddLabel(end_label));
        }

        Expr::Break(exp, label) => {
            let end_label = format!("{}{}", POOL_LABEL, label);
            compile_expr(exp, x86_insts, env, sp, curr_fun, false);
            x86_insts.push(Op::Jmp(end_label.to_string(), None));
        }
        Expr::CallFun(fname, arguments) => {
            if fname == curr_fun && is_tr {
                for arg in arguments.iter() {
                    compile_expr(arg, x86_insts, env, sp, curr_fun, false);
                    x86_insts.push(Op::Push(Reg::Rax)); // Save argument in order on the stack
                                                        // temporarily.
                }
                for (idx, _arg) in arguments.iter().enumerate() {
                    x86_insts.push(Op::Pop(Reg::Rax));
                    x86_insts.push(Op::Mov(
                        Imm::MemRef(Reg::Rbp, idx + 1),
                        Imm::Register(Reg::Rax),
                    ));
                }
            } else {
                for arg in arguments {
                    compile_expr(arg, x86_insts, env, sp, curr_fun, false);
                    x86_insts.push(Op::Push(Reg::Rax));
                    //push into stack the arguments for the function
                }
            }
            if fname == curr_fun && is_tr {
                x86_insts.push(Op::Jmp(format!("{}{}", BODY_LABEL, fname), None));
            } else {
                let rsp_offset: i64 = (8 * arguments.len())
                    .try_into()
                    .expect("Invalid offset given");
                x86_insts.push(Op::Call(fname.to_string()));
                x86_insts.push(Op::Offset(Reg::Rsp, rsp_offset));
            }
        }
        Expr::DefFun(fname, exp, num_args, rsp_offset) => {
            x86_insts.push(Op::AddLabel(fname.to_string()));
            x86_insts.push(Op::Push(Reg::Rbp));
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rbp), Imm::Register(Reg::Rsp)));
            x86_insts.push(Op::Offset(Reg::Rsp, *rsp_offset));
            if *fname == MAIN_FUN {
                // The main function has the args in rdi
                x86_insts.push(Op::Mov(Imm::MemRef(Reg::Rbp, 1), Imm::Register(Reg::Rdi)));
            } else {
                // Otherwise we have to get from rbp + 8 to rbp - 8 slots
                for i in 0..*num_args {
                    x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::ArgRef(2 + i))); // rbp - 8
                                                                                          // contains the
                                                                                          // previous rbp. So
                                                                                          // we need to
                                                                                          // start from rbp
                                                                                          // - 16
                    x86_insts.push(Op::Mov(
                        Imm::MemRef(Reg::Rbp, i + 1),
                        Imm::Register(Reg::Rax),
                    ));
                }
            }
            x86_insts.push(Op::AddLabel(format!("{}{}", BODY_LABEL, fname)));
            compile_expr(exp, x86_insts, env, sp, curr_fun, is_tr);
            x86_insts.push(Op::Mov(Imm::Register(Reg::Rsp), Imm::Register(Reg::Rbp)));
            x86_insts.push(Op::Pop(Reg::Rbp));
            x86_insts.push(Op::Ret);
        }
    }
}

fn compare_type(memref: &Imm) -> String {
    let err_code = ErrCode::InvalidType as i32;
    let mov_str = format!("mov rcx, rax");
    let src_str = get_imm_val(memref);
    let xor_str = format!("xor rcx, {}", src_str);
    let and_str = format!("and rcx, 0x1");
    let cmp_str = format!("cmp rcx, 0");
    let err_code = format!("mov rdi, {}", err_code);
    let jump_ne = format!("jne {}", ERROR_LABEL);
    format!(
        "{}\n{}\n{}\n{}\n{}\n{}",
        mov_str, xor_str, and_str, cmp_str, err_code, jump_ne
    )
}

fn type_check_exp(memref: &Imm) -> String {
    match memref {
        Imm::MemRef(base_reg, offset) => {
            let reg_name = get_reg_name(base_reg);
            let mov_str = format!("mov rcx, [{} - 8 * {}]", reg_name, offset);
            let inv_type_str = get_inv_type_str();
            format!("{}\n{}", mov_str, inv_type_str)
        }
        Imm::Register(reg) => {
            let reg_name = get_reg_name(reg);
            let mov_str = format!("mov rcx, {}", reg_name);
            let inv_type_str = get_inv_type_str();
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
        Reg::Rsp => "rsp".to_string(),
        Reg::Rdi => "rdi".to_string(),
        Reg::Rbp => "rbp".to_string(),
    }
}

fn get_imm_val(imm: &Imm) -> String {
    match imm {
        Imm::Register(reg) => get_reg_name(reg),
        Imm::SignedInt(n) => format!("{}", n),
        Imm::MemRef(base_reg, offset) => {
            let base_str = get_reg_name(base_reg);
            format!("[{} - 8 * {}]", base_str, offset)
        }
        Imm::Boolean(bval) => {
            if *bval == true {
                format!("{}", 3)
            } else {
                format!("{}", 1)
            }
        }
        Imm::ArgRef(offset) => {
            format!("[rbp + 8 * {}]", offset)
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

fn get_inv_type_str() -> String {
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
            let inv_typ_exp_str = type_check_exp(&Imm::Register(Reg::Rax));
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
            let inv_typ_exp_str = type_check_exp(&Imm::Register(Reg::Rax));
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
            let inv_typ_exp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let undo_str = undo_prog_form(&Imm::Register(Reg::Rax));
            let overflow_str = get_overflow_str();
            let shl_str = format!("shl rax, 0x1");
            let neg_str = format!("neg rax");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_exp_str, undo_str, neg_str, overflow_str, shl_str, overflow_str
            )
        }
        Op::Call(fn_label) => {
            //TODO Push arguments in reverse order. What even is an argument?
            format!("call {}", fn_label)
        }
        Op::Plus(r_off) => {
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
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
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
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
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
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
            let and_str = format!("and rax, 0x1");
            let shl_str = format!("shl rax, 1");
            let or_str = format!("or rax, 0x1");
            format!("{}\n{}\n{}", and_str, shl_str, or_str)
        }
        Op::CheckNum => {
            let and_str = format!("and rax, 0x1");
            let xor_str = format!("xor rax, 0x1");
            let shl_str = format!("shl rax, 1");
            let or_str = format!("or rax, 0x1");
            format!("{}\n{}\n{}\n{}", and_str, xor_str, shl_str, or_str)
        }
        Op::Input => {
            format!("mov rax, [rbp - 8]")
        }
        Op::Greater(r_off) => {
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setg al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str, inv_typ_rexp_str, cmp_str, zero_str, setcc_str, shl_str, or_str
            )
        }
        Op::Lesser(r_off) => {
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setl al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str, inv_typ_rexp_str, cmp_str, zero_str, setcc_str, shl_str, or_str
            )
        }
        Op::GreaterEq(r_off) => {
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setge al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str, inv_typ_rexp_str, cmp_str, zero_str, setcc_str, shl_str, or_str
            )
        }
        Op::LesserEq(r_off) => {
            let inv_typ_lexp_str = type_check_exp(&Imm::Register(Reg::Rax));
            let inv_typ_rexp_str = type_check_exp(r_off);
            let src_str = get_imm_val(r_off);
            let cmp_str = format!("cmp rax, {}", src_str);
            let zero_str = format!("mov rax, 0");
            let setcc_str = format!("setle al");
            let shl_str = format!("shl rax, 0x1");
            let or_str = format!("or rax, 0x1");
            format!(
                "{}\n{}\n{}\n{}\n{}\n{}\n{}",
                inv_typ_lexp_str, inv_typ_rexp_str, cmp_str, zero_str, setcc_str, shl_str, or_str
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
                "{}\n{}\n{}\n{}\n{}\n{}",
                check_type_str, cmp_str, zero_str, setcc_str, shl_str, or_str
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

fn parse_fn(s: Sexp) -> (String, (Sexp, Vec<String>)) {
    match s {
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(op)), Sexp::List(fargs), defn] if op == "fun" => {
                let fname = &fargs[0].to_string();
                let fparams = &fargs[1..];
                let param_list = fparams.iter().map(|param| param.to_string()).collect();
                return (fname.to_string(), (defn.clone(), param_list));
            }
            _ => panic!("Invalid function definition provided"),
        },
        _ => panic!("Invalid function definition provided"),
    }
}

fn split_defns(defns: Vec<Sexp>) -> HashMap<String, (Sexp, Vec<String>)> {
    let mut defn_map = HashMap::<String, (Sexp, Vec<String>)>::new();
    for def in defns {
        let defn_tuple = parse_fn(def);
        if defn_map.contains_key(&defn_tuple.0) {
            panic!("Duplicate definition provided");
        } else {
            defn_map.insert(defn_tuple.0, defn_tuple.1);
        }
    }
    return defn_map;
}

fn split_prog(prog: Sexp) -> (Vec<Sexp>, Sexp) {
    let Sexp::List(def_expr) = prog else {
        panic!("Invalid S Expression Provided")
    };
    if let [defns @ .., expr] = &def_expr[..] {
        (defns.to_vec(), expr.clone())
    } else {
        panic!("Invalid program provided")
    }
}

fn compile_fns(defn_map: HashMap<String, (Sexp, Vec<String>)>, x86_insts: &mut Vec<Op>) {
    for (fname, fdef) in &defn_map {
        let defn = &fdef.0;
        let arg_list = &fdef.1;
        let mut arg_set = HashSet::new();
        for arg in arg_list {
            if arg_set.insert(arg).is_some() {
                panic!("Duplicate parameters provided in the function")
            }
        }
        let defn = parse_expr(&defn, &mut Vec::new(), &defn_map);
        let vars_offset: i64 = -8 * (expr_vars(&defn) + arg_list.len()) as i64; // Each arg also has
                                                                                // a copy inside the
                                                                                // stack frame.
        let fexpr = Expr::DefFun(
            fname.to_string(),
            Box::new(defn),
            arg_list.len(),
            vars_offset,
        );
        let mut env = Stack::new();
        for (index, param) in arg_list.iter().enumerate() {
            env.insert(param.to_string(), index + 1);
        }
        compile_expr(&fexpr, x86_insts, &env, env.len(), fname, true);
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();

    let in_file_name = &args[1];
    let out_file_name = &args[2];

    let mut in_file = File::open(in_file_name).expect("Invalid file given:{in_file_name}");
    let mut in_contents = String::new();
    in_file
        .read_to_string(&mut in_contents)
        .expect("Invalid File Given");
    let mut break_stack = Vec::new();

    let prog_sexp = format!("({})", in_contents);
    let split_prog = split_prog(parse(&prog_sexp).expect("Invalid S Expression Provided"));
    let prog_expr: Sexp = split_prog.1;
    let fn_list = split_prog.0;
    let defn_map: HashMap<String, (Sexp, Vec<String>)> = split_defns(fn_list);

    let expr = parse_expr(&prog_expr, &mut break_stack, &defn_map);

    let mut x86_insts: Vec<Op> = vec![];
    let mut x86_fun_insts: Vec<Op> = vec![];

    compile_fns(defn_map, &mut x86_fun_insts);

    let mut main_stack = Stack::new(); // Main always takes an argument of input
    main_stack.insert(INPUT_LABEL.to_string(), 1);

    let vars_offset: i64 = -8 * (expr_vars(&expr) + main_stack.len()) as i64;

    compile_expr(
        &Expr::DefFun(MAIN_FUN.to_string(), Box::new(expr), 1, vars_offset),
        &mut x86_insts,
        &main_stack,
        main_stack.len(),
        &MAIN_FUN.to_string(),
        false,
    );

    let defns = dump_instruction_strings(x86_fun_insts);

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
        defns, ERROR_LABEL, result
    );

    let mut out_file = File::create(out_file_name).expect("Invalid output file given");
    out_file
        .write_all(asm_program.as_bytes())
        .expect("Invalid output file");
}
