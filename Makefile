default: build

test: build
	cargo test --all --tests

build:
	stellar contract build
	mkdir -p target/wasm32v1-none/optimized
	stellar contract optimize \
		--wasm target/wasm32v1-none/release/contracts.wasm \
		--wasm-out target/wasm32v1-none/optimized/comet.wasm
	stellar contract optimize \
		--wasm target/wasm32v1-none/release/factory.wasm \
		--wasm-out target/wasm32v1-none/optimized/comet_factory.wasm
	cd target/wasm32v1-none/optimized/ && \
		for i in *.wasm ; do \
			ls -l "$$i"; \
		done

clean:
	cargo clean
