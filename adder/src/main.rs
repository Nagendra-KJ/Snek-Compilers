use std::env;
use std::fs::File;
use std::io::prelude::*;
use sexp::*;
use sexp::Atom::*;

enum Expr {			// An enum of all possible syntax expressions.
	Num(i32),		// Num is a 32 bit integer
	Add1(Box<Expr>),	// Add1, Sub1 and Negate are expressions which can contain a sub expression
	Sub1(Box<Expr>),
	Negate(Box<Expr>)
}

enum Op {			// An enum of all possible x86 op codes.
	Inc,
	Dec,
	Negate,
	Mov(i32)		// Mov takes a 32 bit integer as a parameter
}

fn parse_expr(s: &Sexp) -> Expr {
	match s {		// Match each possible s expression value to either an atomic value or a list of s expressions
		Sexp::Atom(I(n)) => Expr::Num(i32::try_from(*n).expect("Invalid number given")), // If it is an atomic number, return a number
		Sexp::List(vec) => { // If it is a list of s expressions match each s expression again
			match &vec[..] { // Match each op code and return the corresponding Expr with the argument passed in
				[Sexp::Atom(S(op)), e] if op == "add1" => Expr::Add1(Box::new(parse_expr(e))),
				[Sexp::Atom(S(op)), e] if op == "sub1" => Expr::Sub1(Box::new(parse_expr(e))),
				[Sexp::Atom(S(op)), e] if op == "negate" => Expr::Negate(Box::new(parse_expr(e))),
				_ => panic!("Invalid S expression provided"),
			}
		},
		_ => panic!("Invalid S expression provided"), // If you don't match with anything, print an error
	}
}

fn compile_expr(e: &Expr, x86_insts: &mut Vec<Op>) {
	match e { // Match each Expr value to an x86 Op code and add it to the Op code list
		Expr::Num(n) => x86_insts.push(Op::Mov(*n)),
		Expr::Add1(sub_exp) => { compile_expr(sub_exp, x86_insts); x86_insts.push(Op::Inc)},
		Expr::Sub1(sub_exp) => { compile_expr(sub_exp, x86_insts); x86_insts.push(Op::Dec)},
		Expr::Negate(sub_exp) => { compile_expr(sub_exp, x86_insts); x86_insts.push(Op::Negate)},
	}
}

fn x86_instruction_string(instr: &Op) -> String {
	match instr { // Convert each x86 Opcode into its string format
		Op::Mov(n) => format!("mov rax, {}", n),
		Op::Inc => format!("inc rax"),
		Op::Dec => format!("dec rax"),
		Op::Negate => format!("neg rax"),
	}
}

fn dump_instruction_strings(x86_insts: Vec<Op>) -> String {
	return x86_insts // Iterate over the list of Op codes in the list and map each one to its string equivalent. Once done, collect it and join into a \n separated string
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

	compile_expr(&expr, &mut x86_insts);

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
