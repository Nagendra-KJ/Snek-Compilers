mod infra;

// Your tests go here!
success_tests! {
    {
        name:add_nested_input,
        file: "./add/add_nested_input.snek",
        input: "10",
        expected: "70",
    },
    {
        name:add_nested_var,
        file: "./add/add_nested_var.snek",
        input: "0",
        expected: "110",
    },
    {
        name:add_num_input,
        file: "./add/add_num_input.snek",
        input: "10",
        expected: "30",
    },
    {
        name:add_num_num,
        file: "./add/add_num_num.snek",
        input: "0",
        expected: "60",
    },
    {
        name:add_num_var,
        file: "./add/add_num_var.snek",
        input: "0",
        expected: "60",
    },
    {
        name:add_var_input_num,
        file: "./add/add_var_input.snek",
        input: "10",
        expected: "30",
    },
    {
        name:add_var_var,
        file: "./add/add_var_var.snek",
        input: "0",
        expected: "60",
    },
    {
        name:add1_input_num,
        file: "./add1/add1_input.snek",
        input: "10",
        expected: "11",
    },
    {
        name:add1_nested,
        file: "./add1/add1_nested.snek",
        input: "0",
        expected: "22",
    },
    {
        name:add1_num,
        file: "./add1/add1_num.snek",
        input: "0",
        expected: "21",
    },
    {
        name:add1_var,
        file: "./add1/add1_var.snek",
        input: "0",
        expected: "21",
    },
    {
        name:bool,
        file: "./atomics/bool.snek",
        input: "0",
        expected: "false",
    },
    {
        name:max_num,
        file: "./atomics/max_num.snek",
        input: "0",
        expected: "4611686018427387903",
    },
    {
        name:min_num,
        file: "./atomics/min_num.snek",
        input: "0",
        expected: "-4611686018427387904",
    },
    {
        name:input_num,
        file: "./atomics/input.snek",
        input: "10",
        expected: "10",
    },
    {
        name:input_bool,
        file: "./atomics/input.snek",
        input: "false",
        expected: "false",
    },
    {
        name:max_input,
        file: "./atomics/input.snek",
        input: "4611686018427387903",
        expected: "4611686018427387903",
    },
    {
        name:min_input,
        file: "./atomics/input.snek",
        input: "-4611686018427387904",
        expected: "-4611686018427387904",
    },

    {
        name:num,
        file: "./atomics/num.snek",
        input: "0",
        expected: "42",
    },
    {
        name:var,
        file: "./atomics/var.snek",
        input: "0",
        expected: "5",
    },
    {
        name:equal_bool_bool,
        file: "./equal/equal_bool_bool.snek",
        input: "0",
        expected: "false",
    },
    {
        name:equal_bool_input_bool,
        file: "./equal/equal_bool_input.snek",
        input: "false",
        expected: "true",
    },
    {
        name:equal_nested_input_true,
        file: "./equal/equal_nested_input.snek",
        input: "true",
        expected: "false",
    },
    {
        name:equal_nested_input_false,
        file: "./equal/equal_nested_input.snek",
        input: "false",
        expected: "true",
    },
        {
        name:equal_num_input_num_true,
        file: "./equal/equal_num_input.snek",
        input: "20",
        expected: "true",
    },
    {
        name:equal_num_input_num_false,
        file: "./equal/equal_num_input.snek",
        input: "19",
        expected: "false",
    },
    {
        name:equal_num_num,
        file: "./equal/equal_num_num.snek",
        input: "0",
        expected: "false",
    },
    {
        name:equal_num_var,
        file: "./equal/equal_num_var.snek",
        input: "0",
        expected: "false",
    },
    {
        name:equal_var_input_true,
        file: "./equal/equal_var_input.snek",
        input: "20",
        expected: "true",
    },
    {
        name:equal_var_input_false,
        file: "./equal/equal_var_input.snek",
        input: "19",
        expected: "false",
    },
    {
        name:equal_var_var,
        file: "./equal/equal_var_var.snek",
        input: "0",
        expected: "false",
    },
        {
        name:greater_num_input,
        file: "./greater/greater_num_input.snek",
        input: "10",
        expected: "true",
    },
    {
        name:greater_num_num,
        file: "./greater/greater_num_num.snek",
        input: "0",
        expected: "false",
    },
    {
        name:greater_num_var,
        file: "./greater/greater_num_var.snek",
        input: "0",
        expected: "true",
    },
    {
        name:greater_var_input_num,
        file: "./greater/greater_var_input.snek",
        input: "10",
        expected: "false",
    },
    {
        name:greater_var_var,
        file: "./greater/greater_var_var.snek",
        input: "0",
        expected: "true",
    },
            {
        name:greater_equal_num_input,
        file: "./greater_equal/greater_equal_num_input.snek",
        input: "10",
        expected: "true",
    },
    {
        name:greater_equal_num_num,
        file: "./greater_equal/greater_equal_num_num.snek",
        input: "0",
        expected: "false",
    },
    {
        name:greater_equal_num_var,
        file: "./greater_equal/greater_equal_num_var.snek",
        input: "0",
        expected: "true",
    },
    {
        name:greater_equal_var_input,
        file: "./greater_equal/greater_equal_var_input.snek",
        input: "20",
        expected: "true",
    },
    {
        name:greater_equal_var_var,
        file: "./greater_equal/greater_equal_var_var.snek",
        input: "0",
        expected: "true",
    },
    {
        name:if_cond,
        file: "./if/if_cond.snek",
        input: "0",
        expected: "true",
    },
    {
        name:if_false,
        file: "./if/if_false.snek",
        input: "0",
        expected: "false",
    },
    {
        name:if_input_num,
        file: "./if/if_input.snek",
        input: "10",
        expected: "true",
    },
    {
        name:if_input_true,
        file: "./if/if_input.snek",
        input: "true",
        expected: "true",
    },
    {
        name:if_input_false,
        file: "./if/if_input.snek",
        input: "false",
        expected: "false",
    },
    {
        name:if_non_bool,
        file: "./if/if_non_bool.snek",
        input: "0",
        expected: "true",
    },
    {
        name:if_non_cond,
        file: "./if/if_non_cond.snek",
        input: "0",
        expected: "true",
    },
    {
        name:if_true,
        file: "./if/if_true.snek",
        input: "0",
        expected: "true",
    },
    {
        name:isbool_bool,
        file: "./isbool/isbool_bool.snek",
        input: "0",
        expected: "true",
    },
    {
        name:isbool_input_num,
        file: "./isbool/isbool_input.snek",
        input: "4",
        expected: "false",
    },
    {
        name:isbool_input_bool,
        file: "./isbool/isbool_input.snek",
        input: "true",
        expected: "true",
    },
    {
        name:isbool_nested,
        file: "./isbool/isbool_nested.snek",
        input: "0",
        expected: "false",
    },
    {
        name:isbool_num,
        file: "./isbool/isbool_num.snek",
        input: "0",
        expected: "false",
    },
    {
        name:isbool_var,
        file: "./isbool/isbool_var.snek",
        input: "0",
        expected: "false",
    },
    {
        name: isbool_vec,
        file: "./isbool/isbool_vec.snek",
        input: "0",
        expected: "false",
    },
    {
        name:isnum_bool,
        file: "./isnum/isnum_bool.snek",
        input: "0",
        expected: "false",
    },
    {
        name:isnum_input_num,
        file: "./isnum/isnum_input.snek",
        input: "10",
        expected: "true",
    },
    {
        name:isnum_input_bool,
        file: "./isnum/isnum_input.snek",
        input: "false",
        expected: "false",
    },
    {
        name:isnum_nested,
        file: "./isnum/isnum_nested.snek",
        input: "0",
        expected: "true",
    },
    {
        name:isnum_num,
        file: "./isnum/isnum_num.snek",
        input: "0",
        expected: "true",
    },
    {
        name:isnum_var,
        file: "./isnum/isnum_var.snek",
        input: "0",
        expected: "true",
    },
    {
        name: isnum_vec,
        file: "./isnum/isnum_vec.snek",
        input: "0",
        expected: "false"
    },
    {
        name:lesser_num_input_num,
        file: "./lesser/lesser_num_input.snek",
        input: "10",
        expected: "false",
    },
    {
        name:lesser_num_num,
        file: "./lesser/lesser_num_num.snek",
        input: "0",
        expected: "true",
    },
    {
        name:lesser_num_var,
        file: "./lesser/lesser_num_var.snek",
        input: "0",
        expected: "false",
    },
    {
        name:lesser_var_input,
        file: "./lesser/lesser_var_input.snek",
        input: "10",
        expected: "true",
    },
    {
        name:lesser_var_var,
        file: "./lesser/lesser_var_var.snek",
        input: "0",
        expected: "false",
    },
        {
        name:lesser_equal_num_input,
        file: "./lesser_equal/lesser_equal_num_input.snek",
        input: "10",
        expected: "false",
    },
    {
        name:lesser_equal_num_num,
        file: "./lesser_equal/lesser_equal_num_num.snek",
        input: "0",
        expected: "true",
    },
    {
        name:lesser_equal_num_var,
        file: "./lesser_equal/lesser_equal_num_var.snek",
        input: "0",
        expected: "false",
    },
    {
        name:lesser_equal_var_input,
        file: "./lesser_equal/lesser_equal_var_input.snek",
        input: "20",
        expected: "true",
    },
    {
        name:lesser_equal_var_var,
        file: "./lesser_equal/lesser_equal_var_var.snek",
        input: "0",
        expected: "false",
    },
    {
        name:factorial,
        file: "./loop/factorial.snek",
        input: "5",
        expected: "120",
    },
    {
        name:fib_n,
        file: "./loop/fib_n.snek",
        input: "6",
        expected: "8",
    },
    {
        name:mul_nested_input,
        file: "./mul/mul_nested_input.snek",
        input: "10",
        expected: "8000",
    },
    {
        name:mul_nested_var,
        file: "./mul/mul_nested_var.snek",
        input: "0",
        expected: "40000",
    },
    {
        name:mul_num_input,
        file: "./mul/mul_num_input.snek",
        input: "10",
        expected: "200",
    },
    {
        name:mul_num_num,
        file: "./mul/mul_num_num.snek",
        input: "0",
        expected: "800",
    },
    {
        name:mul_num_var,
        file: "./mul/mul_num_var.snek",
        input: "0",
        expected: "800",
    },
    {
        name:mul_var_input,
        file: "./mul/mul_var_input.snek",
        input: "10",
        expected: "200",
    },
    {
        name:mul_var_var,
        file: "./mul/mul_var_var.snek",
        input: "0",
        expected: "800",
    },
    {
        name:min_underflow_2_60,
        file: "./negative/max_overflow.snek",
        input: "-1",
        expected: "-1152921504606846976",
    },
    {
        name:min_underflow_2_64,
        file: "./negative/max_overflow.snek",
        input: "-4",
        expected: "-4611686018427387904",
    },
    {
        name:strongly_typed,
        file: "./negative/strongly_typed.snek",
        input: "0",
        expected: "false",
    },
    {
        name:sub_nested_input,
        file: "./sub/sub_nested_input.snek",
        input: "10",
        expected: "30",
    },
    {
        name:sub_nested_var,
        file: "./sub/sub_nested_var.snek",
        input: "0",
        expected: "70",
    },
    {
        name:sub_num_input,
        file: "./sub/sub_num_input.snek",
        input: "10",
        expected: "10",
    },
    {
        name:sub_num_num,
        file: "./sub/sub_num_num.snek",
        input: "0",
        expected: "-20",
    },
    {
        name:sub_num_var,
        file: "./sub/sub_num_var.snek",
        input: "0",
        expected: "20",
    },
    {
        name:sub_var_input_num,
        file: "./sub/sub_var_input.snek",
        input: "10",
        expected: "-10",
    },
    {
        name:sub_var_var,
        file: "./sub/sub_var_var.snek",
        input: "0",
        expected: "20",
    },
    {
        name:sub1_input_num,
        file: "./sub1/sub1_input.snek",
        input: "10",
        expected: "9",
    },
    {
        name:sub1_nested,
        file: "./sub1/sub1_nested.snek",
        input: "0",
        expected: "18",
    },
    {
        name:sub1_num,
        file: "./sub1/sub1_num.snek",
        input: "0",
        expected: "19",
    },
    {
        name:sub1_var,
        file: "./sub1/sub1_var.snek",
        input: "0",
        expected: "19",
    },
    {
        name:max_overflow_2_60,
        file: "./negative/max_overflow.snek",
        input: "1",
        expected: "1152921504606846976",
    },
    {
        name:max_overflow_2_60_3,
        file: "./negative/max_overflow.snek",
        input: "3",
        expected: "3458764513820540928",
    },
    {
        name:break3,
        file: "./loop/break3.snek",
        input: "0",
        expected: "3"
    },
    {
        name:primality_true,
        file: "./loop/primality.snek",
        input: "5",
        expected: "true"
    },
    {
        name:primality_false,
        file: "./loop/primality.snek",
        input: "4",
        expected: "false"
    },
    {
        name:sum_of_cubes,
        file: "./loop/sum_of_cubes.snek",
        input: "4",
        expected: "100",
    },
    {
        name:shadow_binding,
        file: "./let/shadow_binding.snek",
        input: "0",
        expected: "5",
    },
    {
        name:anf_addition,
        file: "./let/anf_addition.snek",
        input: "0",
        expected: "70",
    },
    {
        name:fun_add,
        file: "./fun/add.snek",
        input: "10",
        expected: "20",
    },
    {
        name:fun_no_params,
        file: "./fun/fun_no_params.snek",
        input: "0",
        expected: "4\n4",
    },
    {
        name:fun_fact,
        file: "./fun/fact.snek",
        input: "6",
        expected: "720\n720",
    },
    {
        name:fun_recursive_fact,
        file: "./fun/recursive_fact.snek",
        input: "5",
        expected: "120",
    },
    {
        name:fun_tail_recursive_fact,
        file: "./fun/tail_recursive_fact.snek",
        input: "4",
        expected: "24",
    },
    {
        name:fun_recursive_sum,
        file: "./fun/recursive_sum.snek",
        input: "1000",
        expected: "500500",
    },
    {
        name:fun_tail_recursive_sum,
        file: "./fun/tail_recursive_sum.snek",
        input: "100",
        expected: "5050",
    },
    {
        name:fun_is_even_true,
        file: "./fun/is_even.snek",
        input: "100",
        expected: "100\ntrue\ntrue",
    },
    {
        name:fun_is_even_false,
        file: "./fun/is_even.snek",
        input: "99",
        expected: "99\nfalse\nfalse",
    },
    {
        name:fun_tail_recursive_max_true,
        file: "./fun/tail_recursive_max.snek",
        input: "99",
        expected: "99",
    },
    {
        name:fun_tail_recursive_max_false,
        file: "./fun/tail_recursive_max.snek",
        input: "-99",
        expected: "0",
    },
    {
        name:fun_tail_recursive_sum_so,
        file: "./fun/tail_recursive_sum.snek",
        input: "10000000",
        expected: "50000005000000",
    },
    {
        name:fun_call_fun,
        file: "./fun/fun_call_fun.snek",
        input: "0",
        expected: "25"
    },
    {
        name:vec,
        file: "./atomics/vec.snek",
        input: "0",
        expected: "(vec 10 (vec 20 (vec 30 false)))"
    },
    {
        name:vec_get,
        file: "./vec/vec_get.snek",
        input: "0",
        expected: "30"
    },
    {
        name:vec_points,
        file: "./vec/vec_points.snek",
        input: "0",
        expected: "(vec 40 60)"
    },
    {
        name:vec_linear_search_true,
        file: "./vec/vec_linear_search.snek",
        input: "0",
        expected: "3"
    },
    {
        name:vec_linear_search_false,
        file: "./vec/vec_linear_search.snek",
        input: "9",
        expected: "false"
    },
    {
        name:vec_binary_search_true,
        file: "./vec/vec_bst.snek",
        input: "0",
        expected: "0\n0"
    },
    {
        name:vec_binary_search_false,
        file: "./vec/vec_bst.snek",
        input: "9",
        expected: "false"
    }
}

runtime_error_tests! {
    {
        name:add_bool_bool,
        file: "./add/add_bool_bool.snek",
        input: "0",
        expected: "invalid argument"
    },
    {
        name:add_bool_input_num,
        file: "./add/add_bool_input.snek",
        input: "4",
        expected: "invalid argument"
    },
    {
        name:add_bool_input_bool,
        file: "./add/add_bool_input.snek",
        input: "false",
        expected: "invalid argument"
    },
    {
        name:add_num_bool,
        file: "./add/add_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:add1_bool,
        file: "./add1/add1_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:add1_input_bool,
        file: "./add1/add1_input.snek",
        input: "false",
        expected: "invalid argument"
    },
    {
        name:equal_num_bool,
        file: "./equal/equal_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:equal_nested_input_invalid,
        file: "./equal/equal_nested_input.snek",
        input: "4",
        expected: "invalid argument",
    },
    {
        name:equal_bool_input_num,
        file: "./equal/equal_bool_input.snek",
        input: "4",
        expected: "invalid argument"
    },
    {
        name:equal_num_input_bool,
        file: "./equal/equal_num_input.snek",
        input: "false",
        expected: "invalid argument"
    },
    {
        name:greater_bool_bool,
        file: "./greater/greater_bool_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:equal_bool_num,
        file: "./equal/equal_bool_num.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_bool_input_num,
        file: "./greater/greater_bool_input.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_bool_input_bool,
        file: "./greater/greater_bool_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:equal_nested_var,
        file: "./equal/equal_nested_var.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_num_bool,
        file: "./greater/greater_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_num_input_bool,
        file: "./greater/greater_num_input.snek",
        input: "false",
        expected: "invalid argument"
    },
    {
        name:greater_equal_bool_bool,
        file: "./greater_equal/greater_equal_bool_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_equal_bool_input_num,
        file: "./greater_equal/greater_equal_bool_input.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_equal_bool_input_bool,
        file: "./greater_equal/greater_equal_bool_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:greater_equal_num_bool,
        file: "./greater_equal/greater_equal_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_equal_num_input_bool,
        file: "./greater_equal/greater_equal_num_input.snek",
        input: "false",
        expected: "invalid argument"
    },
    {
        name:greater_equal_nested_input,
        file: "./greater_equal/greater_equal_nested_input.snek",
        input: "10",
        expected: "invalid argument",
    },
    {
        name:greater_equal_nested_var,
        file: "./greater_equal/greater_equal_nested_var.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:greater_nested_input,
        file: "./greater/greater_nested_input.snek",
        input: "10",
        expected: "invalid argument",
    },
    {
        name:greater_nested_var,
        file: "./greater/greater_nested_var.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:input_char,
        file: "./atomics/input.snek",
        input: "x",
        expected: "Invalid",
    },
    {
        name:lesser_bool_bool,
        file: "./lesser/lesser_bool_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_bool_input_num,
        file: "./lesser/lesser_bool_input.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_bool_input_bool,
        file: "./lesser/lesser_bool_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:lesser_num_bool,
        file: "./lesser/lesser_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_num_input_bool,
        file: "./lesser/lesser_num_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:lesser_nested_var,
        file: "./lesser/lesser_nested_var.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_nested_input_bool,
        file: "./lesser/lesser_nested_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:lesser_nested_input_num,
        file: "./lesser/lesser_nested_input.snek",
        input: "4",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_bool_bool,
        file: "./lesser_equal/lesser_equal_bool_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_bool_input_num,
        file: "./lesser_equal/lesser_equal_bool_input.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_bool_input_bool,
        file: "./lesser_equal/lesser_equal_bool_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_num_bool,
        file: "./lesser_equal/lesser_equal_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_num_input_bool,
        file: "./lesser_equal/lesser_equal_num_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_nested_input_num,
        file: "./lesser_equal/lesser_equal_nested_input.snek",
        input: "10",
        expected: "invalid argument",
    },
    {
        name:lesser_equal_nested_var,
        file: "./lesser_equal/lesser_equal_nested_var.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:mul_bool_bool,
        file: "./mul/mul_bool_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:mul_bool_input_num,
        file: "./mul/mul_bool_input.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:mul_bool_input_bool,
        file: "./mul/mul_bool_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:mul_num_bool,
        file: "./mul/mul_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:mul_num_input_bool,
        file: "./mul/mul_num_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:sub_bool_bool,
        file: "./sub/sub_bool_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:sub_bool_input_num,
        file: "./sub/sub_bool_input.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:sub_bool_input_bool,
        file: "./sub/sub_bool_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:sub_num_bool,
        file: "./sub/sub_num_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:sub_num_input_bool,
        file: "./sub/sub_num_input.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:sub1_bool,
        file: "./sub1/sub1_bool.snek",
        input: "0",
        expected: "invalid argument",
    },
    {
        name:sub1_input_bool,
        file: "./sub1/sub1_bool.snek",
        input: "false",
        expected: "invalid argument",
    },
    {
        name:max_overflow,
        file: "./negative/max_overflow.snek",
        input: "4",
        expected: "overflow",
    },
    {
        name:min_overflow,
        file: "./negative/max_overflow.snek",
        input: "-5",
        expected: "overflow",
    },
    {
        name:fun_recursive_sum_so,
        file: "./fun/recursive_sum.snek",
        input: "10000000",
        expected: "",
    },
    {
        name:equal_bool_vec,
        file: "./equal/equal_bool_vec.snek",
        input: "0",
        expected: "invalid",
    },
    {
        name:equal_num_vec,
        file: "./equal/equal_bool_num.snek",
        input: "0",
        expected: "invalid",
    },
    {
        name:vec_bounds,
        file: "./negative/vec_bounds.snek",
        input: "0",
        expected: "bounds"
    },
    {
        name:invalid_vec_get,
        file: "./negative/invalid_vec_get.snek",
        input: "0",
        expected: "invalid"
    }

}

static_error_tests! {
    {
        name:invalid_let,
        file: "./negative/invalid_let.snek",
        input: "0",
        expected: "Unbound"
    },
    {
        name:invalid_let_2,
        file: "./negative/invalid_let_2.snek",
        input: "0",
        expected: "Invalid"
    },
    {
        name:invalid_block,
        file: "./negative/invalid_block.snek",
        input: "0",
        expected: "Invalid"
    },
    {
        name:duplicate_binding,
        file: "./negative/duplicate_binding.snek",
        input: "0",
        expected: "Duplicate binding"
    },
    {
        name:invalid_set,
        file: "./negative/invalid_set.snek",
        input: "0",
        expected: "Unbound"
    },
    {
        name:keyword_identifer,
        file: "./negative/keyword_identifer.snek",
        input: "0",
        expected: "keyword"
    },
    {
        name:number_bounds_fail,
        file: "./negative/number_bounds_fail.snek",
        input: "0",
        expected: "Invalid",
    },
    {
        name:invalid_sexp,
        file: "./negative/invalid_sexp.snek",
        input: "0",
        expected: "Invalid",
    },
    {
        name:invalid_loop,
        file: "./negative/invalid_loop.snek",
        input: "0",
        expected: "Invalid",
    },
    {
        name:invalid_print,
        file: "./negative/invalid_print.snek",
        input: "0",
        expected: "Invalid",
    },
    {
        name:duplicate_params,
        file: "./negative/duplicate_params.snek",
        input: "0",
        expected: "Duplicate",
    },
    {
        name:duplicate_funs,
        file: "./negative/duplicate_funs.snek",
        input: "0",
        expected: "Duplicate",
    },
    {
        name:invalid_funs,
        file: "./negative/invalid_funs.snek",
        input: "0",
        expected: "Invalid",
    },
    {
        name:input_in_fun,
        file: "./negative/input_in_fun.snek",
        input: "0",
        expected: "Invalid",
    },
}
