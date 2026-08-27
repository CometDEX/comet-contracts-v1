.PHONY: default build test clean

COMET_RUST_TOOLCHAIN ?= 1.78.0
COMET_TEST_ARGS ?=
WASM_RELEASE_DIR := target/wasm32-unknown-unknown/release
WASM_OPTIMIZED_DIR := target/wasm32-unknown-unknown/optimized

default: build

test: build
	RUSTUP_TOOLCHAIN=$(COMET_RUST_TOOLCHAIN) cargo test --workspace --all-targets --locked $(COMET_TEST_ARGS)

build:
	RUSTUP_TOOLCHAIN=$(COMET_RUST_TOOLCHAIN) stellar contract build --locked --optimize
	mkdir -p $(WASM_OPTIMIZED_DIR)
	cp $(WASM_RELEASE_DIR)/contracts.wasm $(WASM_OPTIMIZED_DIR)/comet.wasm
	cp $(WASM_RELEASE_DIR)/factory.wasm $(WASM_OPTIMIZED_DIR)/comet_factory.wasm
	cd $(WASM_OPTIMIZED_DIR) && \
		for i in *.wasm ; do \
			ls -l "$$i"; \
		done

clean:
	cargo clean
