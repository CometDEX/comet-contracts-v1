.PHONY: default build test generate-c-pow-vectors check-c-pow-vectors clean

COMET_TEST_ARGS ?=
WASM_TARGET_DIR := target/wasm32v1-none
OPTIMIZED_DIR := $(WASM_TARGET_DIR)/optimized

default: build

test: check-c-pow-vectors build
	cargo test --workspace --all-targets --locked $(COMET_TEST_ARGS)

generate-c-pow-vectors:
	python3 scripts/generate_c_pow_vectors.py

check-c-pow-vectors:
	python3 scripts/generate_c_pow_vectors.py --check

build:
	stellar contract build --optimize --locked
	mkdir -p $(OPTIMIZED_DIR)
	cp $(WASM_TARGET_DIR)/release/contracts.wasm $(OPTIMIZED_DIR)/comet.wasm
	cp $(WASM_TARGET_DIR)/release/factory.wasm $(OPTIMIZED_DIR)/comet_factory.wasm
	cd $(OPTIMIZED_DIR) && \
		for i in *.wasm ; do \
			ls -l "$$i"; \
		done

clean:
	cargo clean
