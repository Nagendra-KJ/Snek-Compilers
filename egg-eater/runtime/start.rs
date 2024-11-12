use std::env;
use std::mem;

enum ErrCode {
    Overflow = 1,
    InvalidType = 2,
    OutOfBounds = 3,
}

const TRUE: i64 = 7;
const FALSE: i64 = 3;

impl ErrCode {
    fn from_int(value: i32) -> Option<ErrCode> {
        match value {
            1 => Some(ErrCode::Overflow),
            2 => Some(ErrCode::InvalidType),
            3 => Some(ErrCode::OutOfBounds),
            _ => None,
        }
    }
}

static mut HEAP: [u64; 100000] = [0; 100000];

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01__main__"]
    fn our_code_starts_here(input: i64, heap: *mut u64) -> i64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(err_code: i32) {
    // TODO: print error message according to writeup
    let err_enum = ErrCode::from_int(err_code).expect("Invalid error code provided");
    let err_msg = get_err_msg(err_enum);
    eprintln!("{}", err_msg);
    std::process::exit(err_code);
}

#[export_name = "\x01snek_print"]
pub extern "C" fn snek_print(val: i64) -> i64 {
    parse_output(val);
    return val;
}

fn get_err_msg(err_enum: ErrCode) -> String {
    match err_enum {
        ErrCode::Overflow => format!("An overflow occured"),
        ErrCode::InvalidType => format!("invalid arguments provided to operand"),
        ErrCode::OutOfBounds => format!("Index out of bounds"),
    }
}

fn parse_input(input: &str) -> i64 {
    // TODO: parse the input string into internal value representation
    if input == "true" {
        return TRUE;
    } else if input == "false" {
        return FALSE;
    } else {
        let num: i64 = input.parse().unwrap();
        let sign = num > 0;
        let prog_num = num << 1;
        let unprog_num = prog_num >> 1;
        let prog_sign = unprog_num > 0;
        if sign != prog_sign {
            panic!("Overflow occured. Invalid 62 bit number provided");
        }

        return prog_num;
    }
}

fn parse_vec(i: i64) {
    if i % 2 == 0 {
        print!("{}", i >> 1);
    } else {
        if i == TRUE {
            print!("true");
        } else if i == FALSE {
            print!("false");
        } else {
            print!("(vec ");
            let ptr: *const i64 = unsafe { mem::transmute::<i64, *const i64>(i - 1) };
            let size = unsafe { *ptr };
            for i in 1..=size {
                let val = unsafe { *ptr.add(i as usize) };
                parse_vec(val);
                if i != size {
                    print!(" ");
                }
            }
            print!(")");
        }
    }
}

fn parse_output(i: i64) {
    if i % 2 == 0 {
        println!("{}", i >> 1);
    } else {
        if i == TRUE {
            println!("true");
        } else if i == FALSE {
            println!("false");
        } else {
            parse_vec(i);
            println!();
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() == 2 { &args[1] } else { "false" };
    let input = parse_input(&input);

    let i: i64 = unsafe { our_code_starts_here(input, HEAP.as_mut_ptr()) };
    parse_output(i);
}
