UNAME := $(shell uname)

ifeq ($(UNAME), Linux)
ARCH := elf64
endif
ifeq ($(UNAME), Darwin)
ARCH := macho64
TARGET := --target x86_64-apple-darwin
endif

tests/%.s: tests/%.snek src/main.rs
	cargo run -- $< tests/$*.s

tests/%.run: tests/%.s runtime/start.rs
	nasm -f $(ARCH) tests/$*.s -o tests/$*.o
	ar rcs tests/$(dir $*)lib$(notdir $*).a tests/$*.o
	rustc $(TARGET) -L tests/$(dir $*) -lour_code:$(notdir $*) runtime/start.rs -o tests/$*.run

.PHONY: test
test:
	cargo build
	cargo test

clean:
	find ./tests/ -type f \( -name *.a -o -name *.s -o -name *.run -o -name *.o \) -exec rm {} \;
