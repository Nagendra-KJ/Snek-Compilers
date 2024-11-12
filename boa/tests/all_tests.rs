mod infra;

// Your tests go here!
success_tests! {
    add1: "73",
    add: "15",
    mul: "50",
    nested_arith: "25",
    binding: "5",
    add_with_vars: "30",
    mul_with_vars: "200",
    nested_binding: "12",
    double_binding: "11",
    multiple_and_same: "30",
    multiple_bindings: "30",
    nested_add: "32",
    nested_mul: "231",
    nested_sub: "10",
    same_context_bind: "11",
    seq_add: "15",
    sub: "-5",
    sub_with_vars: "-10",
}


failure_tests! {
    unbound_id: "Unbound variable identifier x",
    duplicate_binding: "Duplicate binding",
    keyword_var: "The identifier name matches a keyword: add1",
}
