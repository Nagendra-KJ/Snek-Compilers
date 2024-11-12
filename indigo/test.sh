#!/bin/bash

# Iterate from 0 to 10
for NUM_REGS in {0..8}
do
    # Export the environment variable NUM_REGS
    export NUM_REGS=$NUM_REGS
    
    # Display the current value of NUM_REGS
    echo "Running tests with NUM_REGS=$NUM_REGS"
    
    # Run cargo test with the current value of NUM_REGS
    cargo test
    
    # Optionally, capture and display the test result status
    if [ $? -eq 0 ]; then
        echo "Tests passed with NUM_REGS=$NUM_REGS"
    else
        echo "Tests failed with NUM_REGS=$NUM_REGS"
    fi

	make clean

    echo "-----------------------------------"
done

