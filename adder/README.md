# Adder Programming Language

## General info
This repo contains the code for the adder assignemnt of CSE:231 taken in Spring 2024 at UCSD, taught by [Prof. Ranjit Jhala](https://ranjitjhala.github.io).

## What is Adder
The adder language takes an S expression that contains 3 possible operations.
* add1 - Increment the value
* sub1 - Decrement the value
* negate - Multiply the value by -1

You can read more about adder [here](https://ucsd-cse231.github.io/sp24/week1/index.html).

## How to write in Adder

To write an adder program, simply create a `.snek` file which contains an S expression of what you are trying to do.

As an example consider:

```
(add1 (sub1 (negate 2)))
```
This takes 2, negates it, decrements it and then increments it to obtain a final value of -2.

## How to compile your snek file

To compile your snek file, run `make program.snek`. This will generate an executable `program.run` file.

## How to view the assembled ouput of your snek file

To create an assembled output, first run `make program.s`. This will generate the `program.s` assembly file which you can view. It is assembled into x86_64 instructions.

## How to run all tests present in test folder

There are a number of test files already provided in the test folder. To run all of them, simply run `./run_all.sh` and the generated outputs are written to the `output.txt` file.
