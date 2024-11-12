use crate::consts::*;
use im::HashSet;

use sexp::Atom::*;
use sexp::*;
use std::sync::atomic::Ordering;

pub enum ErrCode {
    Overflow = 1,
    InvalidType = 2,
    OutOfBounds = 3,
    ArityMismatch = 4,
    InvalidFunction = 5,
}

#[derive(Debug)]
pub enum Cond {
    Eq,
    Neq,
    Ge,
}

#[derive(Debug)]
pub enum Expr {
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
    DefFun(Option<String>, Vec<String>, Box<Expr>),
    Vec(Vec<Expr>),
    VecGet(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum Reg {
    Rax,
    Rcx,
    Rsp,
    Rdi,
    Rbp,
    Rsi,
    R12,
}

#[derive(Debug)]
pub enum Imm {
    // Imms can be Signed Ints or Memory References or Registers
    SignedLong(i64),
    MemRef(Reg, usize),
    Register(Reg),
    Boolean(bool),
    ArgRef(Reg, usize),
    RegRef(Reg, Reg, String),
    SignedInt(i32),
    UnsignedSize(usize),
}

#[derive(Debug)]
pub enum Op {
    // An enum of all possible x86 op codes
    Input,
    Inc,
    Dec,
    Negate,
    CheckBool,
    CheckNum,
    Call(Option<String>),
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
    And(Reg, Imm),
    Sar(Reg, Imm),
    Lea(Reg, String),
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

fn get_binding(bind_sexp: &Sexp, list: &mut Vec<(String, Expr)>, break_stack: &mut Vec<u64>) {
    // Split up the binding list
    // into var name + binding expr
    match bind_sexp {
        Sexp::List(vec) => match &vec[..] {
            [Sexp::Atom(S(var_name)), e]
                if is_duplicate(var_name.to_string(), list) == false
                    && check_valid(var_name) == true =>
            {
                list.push((var_name.to_string(), parse_expr(e, break_stack)))
            }
            _ => panic!("Invalid let expression provided"),
        },
        _ => panic!("Invalid let expression provided"),
    }
}

fn parse_bind_list(sexp_bind_list: &Vec<Sexp>, break_stack: &mut Vec<u64>) -> Vec<(String, Expr)> {
    // Parse binding SExps into
    // binding Exprs
    let mut split_list: Vec<(String, Expr)> = vec![];
    for bind_sexp in sexp_bind_list.iter() {
        get_binding(bind_sexp, &mut split_list, break_stack);
    }
    let bind_list = split_list;
    return bind_list;
}

fn is_keyword(var_name: &String) -> bool {
    // Check if variable name is a keyword
    let keyword_list = vec![
        "add1", "sub1", "negate", "let", "true", "false", "if", "set!", "block", "break", "loop",
        "input", "print", "vec", "vec-get",
    ];
    keyword_list.contains(&var_name.as_str())
}

fn parse_identifier(name: &Sexp) -> String {
    match name {
        Sexp::Atom(S(x)) => x.to_string(),
        _ => panic!("Invalid name provided"),
    }
}

pub fn parse_fn(s: Sexp, break_stack: &mut Vec<u64>) -> Expr {
    // Need to check for duplicate param names and duplicate functions
    let Sexp::List(defns) = s else {
        panic!("Invalid list of defns");
    };
    match &defns[..] {
        [Sexp::Atom(S(op)), Sexp::List(params), body] if op == "defn" => {
            let [name, params @ ..] = &params[..] else {
                panic!("Invalid function name provided");
            };
            let body = Box::new(parse_expr(body, break_stack));
            let name = parse_identifier(name);
            if is_keyword(&name) {
                panic!("Invalid function name given! Function name matches keyword");
            }
            let params: Vec<String> = params.iter().map(parse_identifier).collect();
            let mut params_set: HashSet<String> = HashSet::new();
            for param in params.clone() {
                if is_keyword(&param) {
                    panic!("Invalid function argument name given! Argument name matches keyword");
                }
                if params_set.contains(&param) {
                    panic!("Invalid function parameter provided! Duplicates found");
                } else {
                    params_set.insert(param);
                }
            }
            Expr::DefFun(Some(name), params, body)
        }
        [Sexp::Atom(S(op)), Sexp::List(params), body] if op == "fn" => {
            let [params @ ..] = &params[..];
            let body = Box::new(parse_expr(body, break_stack));
            let params: Vec<String> = params.iter().map(parse_identifier).collect();
            let mut params_set: HashSet<String> = HashSet::new();
            for param in params.clone() {
                if is_keyword(&param) {
                    panic!("Invalid function argument name given! Argument name matches keyword");
                }
                if params_set.contains(&param) {
                    panic!("Invalid function parameter provided! Duplicates found");
                } else {
                    params_set.insert(param);
                }
            }
            Expr::DefFun(None, params, body)
        }
        _ => panic!("Invalid defn provided"),
    }
}

pub fn parse_expr(s: &Sexp, break_stack: &mut Vec<u64>) -> Expr {
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
                    Expr::Add1(Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), e] if op == "sub1" => {
                    Expr::Sub1(Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), e] if op == "negate" => {
                    Expr::Negate(Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), e] if op == "isbool" => {
                    Expr::IsBool(Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), e] if op == "isnum" => {
                    Expr::IsNum(Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), e] if op == "print" => {
                    Expr::Print(Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::Add(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::Sub(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::Mul(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == ">" => Expr::Greater(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "<" => Expr::Lesser(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == ">=" => Expr::GreaterEq(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "<=" => Expr::LesserEq(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), e1, e2] if op == "=" => Expr::Eq(
                    Box::new(parse_expr(e1, break_stack)),
                    Box::new(parse_expr(e2, break_stack)),
                ),
                [Sexp::Atom(S(op)), Sexp::List(sexp_bind_list), eval] if op == "let" => {
                    let var_name = &sexp_bind_list[0];
                    let bind_exp = &sexp_bind_list[1];
                    let mut bind_list = vec![];
                    if is_duplicate(var_name.to_string(), &mut bind_list) == false
                        && check_valid(&var_name.to_string()) == true
                    {
                        bind_list.push((var_name.to_string(), parse_expr(&bind_exp, break_stack)))
                    };
                    let eval_expr = parse_expr(eval, break_stack);
                    if bind_list.len() == 0 {
                        panic!("Invalid list of bindings given! Please provide atleast one binding in the list")
                    }
                    Expr::Let(bind_list, Box::new(eval_expr))
                }
                [Sexp::Atom(S(op)), Sexp::List(sexp_bind_list), eval] if op == "let*" => {
                    let bind_list = parse_bind_list(sexp_bind_list, break_stack);
                    let eval_expr = parse_expr(eval, break_stack);
                    if bind_list.len() == 0 {
                        panic!("Invalid list of bindings given! Please provide atleast one binding in the list")
                    }
                    Expr::Let(bind_list, Box::new(eval_expr))
                }
                [Sexp::Atom(S(op)), Sexp::Atom(S(var)), e] if op == "set!" => {
                    Expr::Set(var.to_string(), Box::new(parse_expr(e, break_stack)))
                }
                [Sexp::Atom(S(op)), exp_list @ ..] if op == "block" => {
                    let mut split_list: Vec<Expr> = vec![];
                    if exp_list.len() == 0 {
                        panic!("Invalid list of expressions given. Please provide atleast one statement in the block")
                    }
                    for exp in exp_list.iter() {
                        let parsed_expr = parse_expr(exp, break_stack);
                        split_list.push(parsed_expr);
                    }
                    Expr::Block(split_list)
                }
                [Sexp::Atom(S(op)), cond, then_exp, else_exp] if op == "if" => {
                    let curr_count = IF_LABEL_COUNT.load(Ordering::Relaxed);
                    IF_LABEL_COUNT.store(curr_count + 1, Ordering::Relaxed);
                    Expr::If(
                        Box::new(parse_expr(cond, break_stack)),
                        Box::new(parse_expr(then_exp, break_stack)),
                        Box::new(parse_expr(else_exp, break_stack)),
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
                        Box::new(parse_expr(e, break_stack)),
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
                        Box::new(parse_expr(e, break_stack)),
                        next_to_break.to_string(),
                    )
                }
                [Sexp::Atom(S(op)), elems @ ..] if op == "vec" => {
                    let elems_expr = elems.iter().map(|e| parse_expr(e, break_stack)).collect();
                    Expr::Vec(elems_expr)
                }
                [Sexp::Atom(S(op)), vector, idx] if op == "vec-get" => {
                    let vec_exp = parse_expr(vector, break_stack);
                    let idx_exp = parse_expr(idx, break_stack);
                    Expr::VecGet(Box::new(vec_exp), Box::new(idx_exp))
                }
                [Sexp::Atom(S(op)), _, _] if op == "defn" || op == "fn" => {
                    parse_fn(s.clone(), break_stack)
                }
                [Sexp::Atom(S(fname)), param_list @ ..] => {
                    let mut args_list: Vec<Expr> = vec![];
                    for param in param_list.iter().rev() {
                        let param_expr = parse_expr(param, break_stack);
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
