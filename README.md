# Checker: A Static Analysis Tool for Rust Safety

This tool is based on rust-mir-checker and MIRAI, utilizing the fundamental approaches of both. Built on the theory of [Abstract Interpretation](https://en.wikipedia.org/wiki/Abstract_interpretation), this tool aims to perform demand-driven analysis to detect unsafe code and potential panic-triggering code in Rust programs.

The implementation leverages principles from existing static analysis frameworks while focusing specifically on identifying safety issues and runtime panic possibilities through advanced static analysis techniques.

## Requirements

* Rust nightly, as specified in [rust-toolchain](rust-toolchain.toml).
* `rustc-dev` and `llvm-tools-preview`:

  ```sh
  $ rustup component add rustc-dev llvm-tools-preview
  ```
* `GMP`, `MPFR`, `PPL` and `Z3`:

  ```sh
  # For Ubuntu:
  $ sudo apt-get install libgmp-dev libmpfr-dev libppl-dev libz3-dev
  $ wget https://github.com/llvm/llvm-project/releases/download/llvmorg-15.0.6/clang+llvm-15.0.6-x86_64-linux-gnu-ubuntu-18.04.tar.xz
  $ tar xvf clang+llvm-15.0.6-x86_64-linux-gnu-ubuntu-18.04.tar.xz
  ```

## Build

1. Clone the repository (use `--recursive` to initialize the nested submodule)

   ```sh
   $ git clone git@github.com:SSCT-Lab/Reaper.git

   $ cd Reaper
   ```
2. Build & Install

   ```sh
   # Use the LLVM lld linker
   $ export RUSTFLAGS="-Clink-args=-fuse-ld=lld"
   # You can build and install the cargo subcommand:
   $ cargo install --path .

   # Or, you can only build the checker itself:
   $ cargo build
   ```

## Example

The following is a simple example which contains an out-of-bounds access in unsafe code.

```rust
fn main() {
    let mut array: [u8; 5] = [1, 2, 3, 4, 5];
    let p = array.as_mut_ptr();
    // println!("out_of_bound_access: {}", unsafe { *p.offset(5) });
    let _out_of_bound_access = unsafe { *p.offset(5) };
}

```

It compiles but will panic at runtime. Our checker can detect it at compile time, the following command will emit a warning:

```sh
./target/debug/checker tests/unsafe-bugs/offset/src/main.rs
warning: [Checker] Provably error: index out of bound
 --> tests/unsafe-bugs/offset/src/main.rs:5:42
  |
5 |     let _out_of_bound_access = unsafe { *p.offset(5) };
  |                                          ^^^^^^^^^^^

warning: 1 warning emitted
```

## Usage

Before using this tool, make sure your Rust project compiles without any errors or warnings.

```sh
# If you have installed the cargo subcommand:
$ CHECKER_FLAGS="--unsafe_only" cargo checker

# Or, you can directly run the checker for a single file
$ target/debug/checker <path-to-file>

# Or run bin in target directory
$ CHECKER_FLAGS='--unsafe_only' ./target/debug/cargo-checker checker
```

## Debug

Set `RUST_LOG` environment variable to enable logging:

```sh
# Enable all logging
$ export RUST_LOG=checker

# Can also set logging level
$ export RUST_LOG=checker=debug
```

For more settings, please see the documents of [env_logger](https://crates.io/crates/env_logger).

## Bug Found

All bugs found can be triggered.

**Abbreviation Legend for Bug Categories:**

- **UB class (starts with U-)**
    - **U-OOB**: Out-of-Bounds access
    - **U-DF**: Double Free
    - **U-UAF**: Use After Free
    - **U-ML**: Memory Leak
    - **U-MA**: Misaligned Address

- **Panic class (starts with P-)**
    - **P-AO**: Arithmetic Overflow
    - **P-DZ**: Division by Zero
    - **P-OOB**: Index Out of Bounds


## Future Work

There are a lot of limitations of Checker that we would like to address in the future

* Add support for `rust-std` (using `xargo` to compile `rust-std`).
* Treat the static analyzer as a back-end and add a front-end to filter false positives using an LLM.
* Implement more rules to detect a wider range of errors.
* As a next step, refactor the tool into a generic framework to allow users to more easily check for specific types of memory errors.

## Troubleshooting

For macOS, you may encounter `dyld: Library not loaded` error, try setting:

```sh
$ export LD_LIBRARY_PATH=$(rustc --print sysroot)/lib:$LD_LIBRARY_PATH
```

## Credits

Many ideas and code bases are from the following projects, many thanks!

* [MIRAI](https://github.com/facebookexperimental/MIRAI)
* [MIR-Checker](https://github.com/lizhuohua/rust-mir-checker)
* [Miri](https://github.com/rust-lang/miri)

## License

See [LICENSE](LICENSE) and [licenses](licenses)
# reaper
