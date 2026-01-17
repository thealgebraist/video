# Rust Asset Generator (tch-rs)

This small scaffold demonstrates loading a TorchScript/CModule model using `tch` (the Rust bindings for PyTorch) and producing output tensors.

Build prerequisites
- Rust toolchain (rustup/cargo)
- A libtorch binary available for `tch` to link against. Either set `LIBTORCH` to the libtorch folder or install a compatible libtorch on your system. See `tch` docs: https://github.com/LaurentMazare/tch-rs

Build

```bash
cd rust_asset_generator
cargo build --release
```

Run

```bash
# Example: replace /path/to/model.pt with a TorchScript/CModule model
./target/release/rust_asset_generator --model /path/to/model.pt --output ./generated --count 3
```

Output
- The program writes tensor files `output_0.pt`, `output_1.pt`, ... into the output directory.

Next steps
- Integrate this binary into the Python pipeline, or extend it to decode tensors to images/audio depending on your model.
