default: build

test: build
	cargo test --all --tests

build:
	soroban contract build
	mkdir -p target/wasm32-unknown-unknown/optimized
	soroban contract optimize \
		--wasm target/wasm32-unknown-unknown/release/contracts.wasm \
		--wasm-out target/wasm32-unknown-unknown/optimized/comet.wasm
	soroban contract optimize \
		--wasm target/wasm32-unknown-unknown/release/factory.wasm \
		--wasm-out target/wasm32-unknown-unknown/optimized/comet_factory.wasm
	cd target/wasm32-unknown-unknown/optimized/ && \
		for i in *.wasm ; do \
			ls -l "$$i"; \
		done

clean:
	cargo clean
