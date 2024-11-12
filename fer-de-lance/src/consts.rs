use std::sync::atomic::AtomicU64;

pub static MAIN_FUN: &str = "__main__";
pub static BODY_LABEL: &str = "__body__";
pub static START_LABEL: &str = "__start__";
pub static EXIT_LABEL: &str = "__exit__";
pub static FINISH_LABEL: &str = "__finish__";
pub static FI_LABEL: &str = "__fi__";
pub static ELSE_LABEL: &str = "__else__";
pub static LOOP_LABEL: &str = "__loop__";
pub static POOL_LABEL: &str = "__pool__";
pub static INPUT_LABEL: &str = "__input__";
pub static SNEK_PRINT_FUN: &str = "snek_print";
pub static ERROR_LABEL: &str = "__error__";
pub static ANON_LABEL: &str = "__anon__";

pub static TRUE: i32 = 7;
pub static FALSE: i32 = 3;

pub static IF_LABEL_COUNT: AtomicU64 = AtomicU64::new(0);
pub static LOOP_LABEL_COUNT: AtomicU64 = AtomicU64::new(0);
pub static ANON_FN_COUNT: AtomicU64 = AtomicU64::new(0);

pub static COMPARE_TYPES_FN: &str = "__compare_type__:
mov rcx, rdi ; Save 1st arg in rcx
mov rdx, rsi ; Save 2nd arg in rdx
and rcx, 0x1 ; Get last bit
and rdx, 0x1 ; Get last bit
cmp rcx, rdx ; Compare
mov rdi, 0x2 ; Copy error code
jne __error__ ; If not same error out
cmp rcx, 0x0 ; If same, check if last bit 0
je __end_compare_type__ ; If last bit 0 jump to end
; Last bit is 1 in both cases. Check second last bit
mov rcx, rdi ; Get 1st arg in rcx
mov rdx, rsi ; Get 2nd arg in rdx
and rcx, 0x2 ; Get 2nd last bit
and rdx, 0x2 ; Get 2nd last bit
cmp rcx, rdx ; Compare them both
mov rdi, 0x2 ; Copy error code
jne __error__ ; If not equal error out.
__end_compare_type__:
ret
";
