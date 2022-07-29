

.PHONY: all build
all build:
	cargo build

.PHONY: run test
run test:
	cargo run

.PHONY: clean
clean:
	cargo clean
	
