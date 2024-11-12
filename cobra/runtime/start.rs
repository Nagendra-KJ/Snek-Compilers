use std::env;

enum ErrCode {
    Overflow = 1,
    InvalidType = 2,
}

impl ErrCode {
    fn from_int(value: i32) -> Option<ErrCode> {
        match value {
            1 => Some(ErrCode::Overflow),
            2 => Some(ErrCode::InvalidType),
            _ => None,
        }
    }
}

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: i64) -> i64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(err_code: i32) {
    // TODO: print error message according to writeup
    let err_enum = ErrCode::from_int(err_code).expect("Invalid error code provided");
    let err_msg = get_err_msg(err_enum);
    eprintln!("{}", err_msg);
    std::process::exit(err_code);
}

fn get_err_msg(err_enum: ErrCode) -> String {
    match err_enum {
        ErrCode::Overflow => format!("An overflow occured"),
        ErrCode::InvalidType => format!("invalid arguments provided to operand"),
    }
}

fn parse_input(input: &str) -> i64 {
    // TODO: parse the input string into internal value representation
    if input == "true" {
        return 3;
    } else if input == "false" {
        return 1;
    } else {
        let num: i64 = input.parse().unwrap();
        return num << 1;
    }
}

fn parse_output(i: i64) {
    if i % 2 == 0 {
        println!("{}", i >> 1);
    } else {
        if i == 3 {
            println!("true");
        } else if i == 1 {
            println!("false");
        } else {
            panic!("Invalid value returned");
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() == 2 { &args[1] } else { "false" };
    let input = parse_input(&input);

    let i: i64 = unsafe { our_code_starts_here(input) };
    parse_output(i);
}