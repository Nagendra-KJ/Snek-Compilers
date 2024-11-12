use std::env;
use std::fs::File;
use std::io::prelude::*;
use sexp::*;
use sexp::Atom::*;
use im::HashMap;

#[derive(Debug)]
enum Expr {			// An enum of all possible syntax expressions.
	Num(i32),		// Num is a 32 bit integer
	Add1(Box<Expr>),	// Add1, Sub1 and Negate are expressions which can contain a sub expression
	Sub1(Box<Expr>),
	Negate(Box<Expr>),
	Var(String),        // Variable is just a name
	Let(Vec<(String, Expr)>, Box<Expr>), // Let bindings take a binding list and a bound expression
	Add(Box<Expr>, Box<Expr>), // Add, Sub and Mul take two operands
	Sub(Box<Expr>, Box<Expr>),
	Mul(Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
enum Reg { // So far we have support for Rax and Rsp
	Rax,
	Rsp
}

#[derive(Debug)]
enum Imm {          // Imms can be Signed Ints or Memory References or Registers
	SignedInt(i32),
	MemRef(Reg, usize),
	Register(Reg)
}

#[derive(Debug)]
enum Op {			// An enum of all possible x86 op codes.
	Inc,
	Dec,
	Negate,
	Mov(Imm, Imm),		// Mov takes 2 immediate values
	Plus(Imm),          // Plus, Minus and Times take one immediate value and the other value is
                        // explicitly the Rax register
	Minus(Imm),
	Times(Imm)
}

type Stack = HashMap<String, usize>;

fn is_duplicate(var_name: String, list: &mut Vec<(String, Expr)>) -> bool { // Check for a
                                                                            // duplicate binding
	for binding in list.iter() {
		if binding.0 == var_name {
			panic!("Duplicate binding found!");
		}
	}
	return false;
}

fn get_binding(bind_sexp : &Sexp, list: &mut Vec<(String, Expr)>) { // Split up the binding list
                                                                    // into var name + binding expr
	match bind_sexp {
		Sexp::List(vec) => {
				match &vec[..] {
					[Sexp::Atom(S(var_name)), e] if is_duplicate(var_name.to_string(), list) == false &&
					check_valid(var_name) == true => {list.push((var_name.to_string(), parse_expr(e)))},
					_ => panic!("Invalid let expression provided")
				}
			},
		_ => panic!("Invalid let expression provided")
	}
}

fn parse_bind_list(sexp_bind_list: &Vec<Sexp>) -> Vec<(String, Expr)>{ // Parse binding SExps into
                                                                       // binding Exprs
	let mut split_list : Vec<(String, Expr)> = vec![];
	for bind_sexp in sexp_bind_list.iter() {
		get_binding(bind_sexp, &mut split_list);
	}
	let bind_list = split_list;
	return bind_list;
}

fn check_if_keyword(var_name: &String) -> bool { // Check if variable name is a keyword
	let keyword_list = vec!["add1", "sub1", "negate", "let"];
	if keyword_list.contains(&var_name.as_str())
	{
		panic!("The identifier name matches a keyword: {}", var_name);
	}
	return false;
}

fn check_valid(var_name: &String) -> bool { // Should add the regexp checker here
	return check_if_keyword(var_name) == false;
}

fn parse_expr(s: &Sexp) -> Expr {
	match s {		// Match each possible s expression value to either an atomic value or a list of s expressions
		Sexp::Atom(I(n)) => Expr::Num(i32::try_from(*n).expect("Invalid number given")), // If it is an atomic number, return a number
		Sexp::Atom(S(var)) => Expr::Var(var.to_string()),
		Sexp::List(vec) => { // If it is a list of s expressions match each s expression again
			match &vec[..] { // Match each op code and return the corresponding Expr with the argument passed in
				[Sexp::Atom(S(op)), e] if op == "add1" => Expr::Add1(Box::new(parse_expr(e))),
				[Sexp::Atom(S(op)), e] if op == "sub1" => Expr::Sub1(Box::new(parse_expr(e))),
				[Sexp::Atom(S(op)), e] if op == "negate" => Expr::Negate(Box::new(parse_expr(e))),
				[Sexp::Atom(S(op)), Sexp::List(sexp_bind_list), eval] if op == "let" => {
								let bind_list = parse_bind_list(sexp_bind_list);
								let eval_expr = parse_expr(eval);
								Expr::Let(bind_list, Box::new(eval_expr))
							},
				[Sexp::Atom(S(op)), e1, e2] if op == "+" => Expr::Add(Box::new(parse_expr(e1)), Box::new(parse_expr(e2))),
				[Sexp::Atom(S(op)), e1, e2] if op == "-" => Expr::Sub(Box::new(parse_expr(e1)), Box::new(parse_expr(e2))),
				[Sexp::Atom(S(op)), e1, e2] if op == "*" => Expr::Mul(Box::new(parse_expr(e1)), Box::new(parse_expr(e2))),
				_ => panic!("Invalid S expression vector provided: {:?}", vec),
			}
		},
		_ => panic!("Invalid S expression provided: {:?}", s), // If you don't match with anything, print an error
	}
}

fn compile_expr(e: &Expr, x86_insts: &mut Vec<Op>, env: &Stack, sp: usize) {
	match e { // Match each Expr value to an x86 Op code and add it to the Op code list
		Expr::Num(n) => x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::SignedInt(*n))),
		Expr::Add1(sub_exp) => { compile_expr(sub_exp, x86_insts, env, sp); x86_insts.push(Op::Inc) },
		Expr::Sub1(sub_exp) => { compile_expr(sub_exp, x86_insts, env, sp); x86_insts.push(Op::Dec) },
		Expr::Negate(sub_exp) => { compile_expr(sub_exp, x86_insts, env, sp); x86_insts.push(Op::Negate) },
		Expr::Var(v) => {
				let vpos = match env.get(v) {
						Some(p) => p,
						None => {
							panic!("Unbound variable identifier {v}");
						}
				};
				x86_insts.push(Op::Mov(Imm::Register(Reg::Rax), Imm::MemRef(Reg::Rsp, *vpos)));
		},
		Expr::Let(bind_list, exp) => {
				let mut new_env = env.clone();
				let mut var_count = 0;
				for bind in bind_list.iter() {
					compile_expr(&bind.1, x86_insts, &new_env, sp); // Compile the binding
                                                                    // expression
					let var_pos = sp + 1 + var_count; // Increment the variable count
					var_count = var_count + 1;
					x86_insts.push(Op::Mov(Imm::MemRef(Reg::Rsp, var_pos), Imm::Register(Reg::Rax)));
					new_env = new_env.update(bind.0.to_string(), var_pos);
				}
				let new_sp = sp + var_count;
				compile_expr(exp, x86_insts, &new_env, new_sp); // Compile the bound expression in
                                                                // the context of the binding
                                                                // expression.
		},
		Expr::Add(rexp, lexp) => {
						compile_expr(lexp, x86_insts, env, sp);
						x86_insts.push(Op::Mov(Imm::MemRef(Reg::Rsp, sp + 1), Imm::Register(Reg::Rax)));
						compile_expr(rexp, x86_insts, env, sp+1);
						x86_insts.push(Op::Plus(Imm::MemRef(Reg::Rsp, sp + 1)));
					 },
		Expr::Sub(rexp, lexp) => {
						compile_expr(lexp, x86_insts, env, sp);
						x86_insts.push(Op::Mov(Imm::MemRef(Reg::Rsp, sp + 1), Imm::Register(Reg::Rax)));
						compile_expr(rexp, x86_insts, env, sp+1);
						x86_insts.push(Op::Minus(Imm::MemRef(Reg::Rsp, sp + 1)));
					 },
		Expr::Mul(rexp, lexp) => {
						compile_expr(lexp, x86_insts, env, sp);
						x86_insts.push(Op::Mov(Imm::MemRef(Reg::Rsp, sp + 1), Imm::Register(Reg::Rax)));
						compile_expr(rexp, x86_insts, env, sp+1);
						x86_insts.push(Op::Times(Imm::MemRef(Reg::Rsp, sp + 1)));
					 }
	}
}

fn get_reg_name(reg : &Reg) -> String {
	match reg {
		Reg::Rax => "rax".to_string(),
		Reg::Rsp => "rsp".to_string()
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
	}
}

fn x86_instruction_string(instr: &Op) -> String {
	match instr { // Convert each x86 Opcode into its string format
		Op::Mov(dst, src) => {
					let dst_str = get_imm_val(dst);
					let src_str = get_imm_val(src);
					format!("mov {}, {}", dst_str, src_str)
				}
		Op::Inc => format!("inc rax"),
		Op::Dec => format!("dec rax"),
		Op::Negate => format!("neg rax"),
		Op::Plus(r_off) => {
				let src_str = get_imm_val(r_off);
				format!("add rax, {}", src_str)
			}
		Op::Minus(r_off) => {
				let src_str = get_imm_val(r_off);
				format!("sub rax, {}", src_str)
			}
		Op::Times(r_off) => {
				let src_str = get_imm_val(r_off);
				format!("imul rax, {}", src_str)
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

fn main() {
	let args: Vec<String> = env::args().collect();

	let in_file_name = &args[1];
	let out_file_name = &args[2];

	let mut in_file = File::open(in_file_name).expect("Unable to open {in_file_name}");
	let mut in_contents = String::new();
	in_file.read_to_string(&mut in_contents).expect("Unable to read file");

	let expr = parse_expr(&parse(&in_contents).expect("Unable to parse file contents"));

	let mut x86_insts : Vec<Op> = vec![];

	compile_expr(&expr, &mut x86_insts, &Stack::new(), 0);

    let result = dump_instruction_strings(x86_insts);

    let asm_program = format!("section .text
global our_code_starts_here
our_code_starts_here:
{}
ret
", result);

	let mut out_file = File::create(out_file_name).expect("Unable to create output file");
	out_file.write_all(asm_program.as_bytes()).expect("Unable to write to output file");
}
