use std::{collections::HashSet, env};

type SnekVal = u64;

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(i64)]
pub enum ErrCode {
    InvalidArgument = 1,
    Overflow = 2,
    IndexOutOfBounds = 3,
    InvalidVecSize = 4,
    OutOfMemory = 5,
}

const TRUE: u64 = 7;
const FALSE: u64 = 3;

static mut HEAP_START: *const u64 = std::ptr::null();
static mut HEAP_END: *const u64 = std::ptr::null();

#[link(name = "our_code")]
extern "C" {
    // The \x01 here is an undocumented feature of LLVM that ensures
    // it does not add an underscore in front of the name.
    // Courtesy of Max New (https://maxsnew.com/teaching/eecs-483-fa22/hw_adder_assignment.html)
    #[link_name = "\x01our_code_starts_here"]
    fn our_code_starts_here(input: u64, heap_start: *const u64, heap_end: *const u64) -> u64;
}

#[export_name = "\x01snek_error"]
pub extern "C" fn snek_error(errcode: i64) {
    if errcode == ErrCode::InvalidArgument as i64 {
        eprintln!("invalid argument");
    } else if errcode == ErrCode::Overflow as i64 {
        eprintln!("overflow");
    } else if errcode == ErrCode::IndexOutOfBounds as i64 {
        eprintln!("index out of bounds");
    } else if errcode == ErrCode::InvalidVecSize as i64 {
        eprintln!("vector size must be non-negative");
    } else {
        eprintln!("an error ocurred {}", errcode);
    }
    std::process::exit(errcode as i32);
}

#[export_name = "\x01snek_print"]
pub unsafe extern "C" fn snek_print(val: SnekVal) -> SnekVal {
    println!("{}", snek_str(val, &mut HashSet::new()));
    val
}

/// This function is called when the program needs to allocate `count` words of memory and there's no
/// space left. The function should try to clean up space by triggering a garbage collection. If there's
/// not enough space to hold `count` words after running the garbage collector, the program should terminate
/// with an `out of memory` error.
///
/// Args:
///     * `count`: The number of words the program is trying to allocate, including an extra word for
///       the size of the vector and an extra word to store metadata for the garbage collector, e.g.,
///       to allocate a vector of size 5, `count` will be 7.
///     * `heap_ptr`: The current position of the heap pointer (i.e., the value stored in `%r15`). It
///       is guaranteed that `heap_ptr + 8 * count > HEAP_END`, i.e., this function is only called if
///       there's not enough space to allocate `count` words.
///     * `stack_base`: A pointer to the "base" of the stack.
///     * `curr_rbp`: The value of `%rbp` in the stack frame that triggered the allocation.
///     * `curr_rsp`: The value of `%rsp` in the stack frame that triggered the allocation.
///
/// Returns:
///
/// The new heap pointer where the program should allocate the vector (i.e., the new value of `%r15`)
///
#[export_name = "\x01snek_try_gc"]
pub unsafe extern "C" fn snek_try_gc(
    count: isize,
    heap_ptr: *const u64,
    stack_base: *const u64,
    curr_rbp: *const u64,
    curr_rsp: *const u64,
) -> *const u64 {
    let new_heap_ptr = snek_gc(heap_ptr, stack_base, curr_rbp, curr_rsp);
    if new_heap_ptr.add(count as usize) > HEAP_END {
        eprintln!("cannot add {:?} words", count);
        eprintln!("out of memory");
        std::process::exit(ErrCode::OutOfMemory as i32)
    }
    return new_heap_ptr;
}

unsafe fn zero_out_remainder(new_heap_ptr: *const u64) {
    let mut ptr = new_heap_ptr as *mut u64;
    while ptr < HEAP_END as *mut u64 {
        *ptr = 0;
        ptr = ptr.add(1);
    }
}

/// This function should trigger garbage collection and return the updated heap pointer (i.e., the new
/// value of `%r15`). See [`snek_try_gc`] for a description of the meaning of the arguments.
#[export_name = "\x01snek_gc"]
pub unsafe extern "C" fn snek_gc(
    heap_ptr: *const u64,
    stack_base: *const u64,
    curr_rbp: *const u64,
    curr_rsp: *const u64,
) -> *const u64 {
    let new_rbp = unsafe { *curr_rbp as *const u64 };
    let new_rsp = curr_rbp.add(2);

    get_live_objects(stack_base, curr_rbp, curr_rsp);

    if curr_rbp == stack_base {
        print_heap();
        compact();
        print_heap();
        let new_heap_ptr = get_new_heap_ptr();
        move_cells();
        print_heap();
        update_nested_cells();
        print_heap();
        update_stack(heap_ptr, curr_rbp, curr_rsp, stack_base);
        reset_gc_word();
        print_heap();
        zero_out_remainder(new_heap_ptr);
        print_heap();
        return new_heap_ptr;
        //return heap_ptr;
    }

    return snek_gc(heap_ptr, stack_base, new_rbp, new_rsp);
}

unsafe fn update_nested_cells() {
    let mut ptr = HEAP_START as *mut u64;
    while ptr < HEAP_END as *mut u64 {
        if ptr.add(1) >= HEAP_END as *mut u64 {
            return;
        }
        let size = ptr.add(1).read() as usize;
        if ptr.add(size + 2) > HEAP_END as *mut u64 {
            return;
        }
        for i in 0..size {
            let elem = ptr.add(2 + i).read() as *mut u64;
            if is_pointer(elem as u64) {
                // This is a pointer we need to update to its new location
                let elem_ptr = untag(elem as u64);
                let new_addr = *elem_ptr; // Get the relocation address from the gc word of the elem
                *ptr.add(2 + i) = new_addr + 1; // Point the elem to the new address retagged
            }
        }
        ptr = ptr.add(size + 2);
    }
}

unsafe fn print_heap() {
    let mut ptr = HEAP_START;
    while ptr < HEAP_END {
        let gc_word = ptr.read();
        let heap_size = ptr.add(1).read() as usize;
        ptr = ptr.add(heap_size + 2);
    }
}

unsafe fn get_new_heap_ptr() -> *const u64 {
    let mut ptr = HEAP_START;
    let mut end_ptr = HEAP_START;
    while ptr < HEAP_END {
        let gc_word = *ptr;
        let heap_size = *ptr.add(1);
        if gc_word != 0 {
            end_ptr = end_ptr.add(heap_size as usize + 2);
        }
        ptr = ptr.add(heap_size as usize + 2);
    }
    if end_ptr > HEAP_END {
        return HEAP_END;
    }
    return end_ptr;
}

unsafe fn update_stack(
    heap_ptr: *const u64,
    curr_rbp: *const u64,
    curr_rsp: *const u64,
    stack_base: *const u64,
) {
    let mut ptr = curr_rbp as *mut u64;
    while ptr >= curr_rsp as *mut u64 {
        let value = *ptr;
        if is_pointer(value) {
            let new_ptr = untag(value);
            let new_addr = *new_ptr;
            *ptr = new_addr + 1;
        }
        ptr = ptr.sub(1);
    }

    if curr_rbp == stack_base {
        return;
    }
    let new_rbp = unsafe { *curr_rbp as *const u64 };
    let new_rsp = curr_rbp.add(2);
    update_stack(heap_ptr, new_rbp, new_rsp, stack_base);
}

unsafe fn get_live_objects(stack_base: *const u64, curr_rbp: *const u64, curr_rsp: *const u64) {
    let mut ptr = curr_rbp;
    while ptr >= curr_rsp {
        let value = *ptr;
        if is_pointer(value) {
            let new_ptr = untag(value);
            set_gc_word_live(new_ptr);
        }
        ptr = ptr.sub(1);
    }
}

unsafe fn reset_gc_word() {
    let mut ptr = HEAP_START as *mut u64;
    while ptr < HEAP_END as *mut u64 {
        let heap_size = ptr.add(1).read();
        *ptr = 0; // Resetting the gc word
        ptr = ptr.add(heap_size as usize + 2);
    }
}

unsafe fn set_gc_word_live(heap_cell: *mut u64) {
    let heap_size = unsafe { *heap_cell.add(1) as usize };
    let heap_start = heap_cell;
    let heap_end = unsafe { heap_start.add(heap_size as usize + 2) };

    if *heap_cell == 1 {
        // GC word is already set to live and we can just avoid the dfs
        return;
    }

    *heap_cell = 1; // Marking GC word as 1

    let mut ptr = unsafe { heap_cell.add(2) }; // Get first element pointer
    while ptr < heap_end {
        let value = unsafe { *ptr };
        if is_pointer(value) {
            let new_ptr = untag(value);
            set_gc_word_live(new_ptr);
        }

        ptr = ptr.add(1);
    }
}

unsafe fn is_pointer(value: u64) -> bool {
    if value == 1 {
        return false;
    }
    if value > HEAP_END as u64 {
        return false;
    }
    if value < HEAP_START as u64 {
        return false;
    }
    return value as usize & 0x7 == 0x1;
}

fn untag(ptr: u64) -> *mut u64 {
    (ptr as usize - 1) as *mut u64
}

unsafe fn compact() {
    let mut relocation_ptr = HEAP_START;
    let mut itr_ptr = HEAP_START as *mut u64;

    while itr_ptr < HEAP_END as *mut u64 {
        let gc_word = itr_ptr.read();
        let heap_size = itr_ptr.add(1).read();
        if gc_word == 1 {
            // set the gc word of the heap cell to the relocation addresss
            let relocation_addr = relocation_ptr as u64;
            *itr_ptr = relocation_addr;
            // heap cell is live, so move both relocation ptr and itr ptr
            itr_ptr = itr_ptr.add(heap_size as usize + 2);
            relocation_ptr = relocation_ptr.add(heap_size as usize + 2);
        } else {
            // heap cell is not live, so move only itr ptr
            itr_ptr = itr_ptr.add(heap_size as usize + 2);
        }
    }
}

unsafe fn move_cells() {
    let mut itr_ptr: *mut u64 = HEAP_START as *mut u64;

    while itr_ptr < HEAP_END as *mut u64 {
        let gc_word = itr_ptr.read();
        let heap_size = itr_ptr.add(1).read();
        if gc_word != 0 {
            // heap cell is live relocate it to the address given in gc word
            let relocation_ptr = itr_ptr.read() as *mut u64;
            for i in 0..heap_size as usize + 2 {
                *relocation_ptr.add(i) = *itr_ptr.add(i);
            }
        }
        itr_ptr = itr_ptr.add(heap_size as usize + 2);
    }
}

/// A helper function that can be called with the `(snek-printstack)` snek function. It prints the stack
/// See [`snek_try_gc`] for a description of the meaning of the arguments.
#[export_name = "\x01snek_print_stack"]
pub unsafe extern "C" fn snek_print_stack(
    stack_base: *const u64,
    curr_rbp: *const u64,
    curr_rsp: *const u64,
) {
    let mut ptr = stack_base;
    println!("-----------------------------------------");
    while ptr >= curr_rsp {
        let val = *ptr;
        println!("{ptr:?}: {:#0x}", val);
        ptr = ptr.sub(1);
    }
    println!("-----------------------------------------");
}

unsafe fn snek_str(val: SnekVal, seen: &mut HashSet<SnekVal>) -> String {
    if val == TRUE {
        format!("true")
    } else if val == FALSE {
        format!("false")
    } else if val & 1 == 0 {
        format!("{}", (val as i64) >> 1)
    } else if val == 1 {
        format!("nil")
    } else if val & 1 == 1 {
        if !seen.insert(val) {
            return "[...]".to_string();
        }
        let addr = (val - 1) as *const u64;
        let size = addr.add(1).read() as usize;
        let mut res = "[".to_string();
        for i in 0..size {
            let elem = addr.add(2 + i).read();
            res = res + &snek_str(elem, seen);
            if i < size - 1 {
                res = res + ", ";
            }
        }
        seen.remove(&val);
        res + "]"
    } else {
        format!("unknown value: {val}")
    }
}

fn parse_input(input: &str) -> u64 {
    match input {
        "true" => TRUE,
        "false" => FALSE,
        _ => (input.parse::<i64>().unwrap() << 1) as u64,
    }
}

fn parse_heap_size(input: &str) -> usize {
    input.parse::<usize>().unwrap()
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() >= 2 { &args[1] } else { "false" };
    let heap_size = if args.len() >= 3 { &args[2] } else { "10000" };
    let input = parse_input(&input);
    let heap_size = parse_heap_size(&heap_size);

    // Initialize heap
    let mut heap: Vec<u64> = Vec::with_capacity(heap_size);
    unsafe {
        HEAP_START = heap.as_mut_ptr();
        HEAP_END = HEAP_START.add(heap_size);
    }

    let i: u64 = unsafe { our_code_starts_here(input, HEAP_START, HEAP_END) };
    unsafe { snek_print(i) };
}
