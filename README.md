# wasm-preprocessing
Software needed for preprocessing WASM files so that they can be ran on the TrueBit VM.

I think it will be better to implement these steps in some other language than OCaml, because OCaml can currently only run in the Truebit
VM by using OCaml bytecode interpreter.

Testing:
```
cargo run test.wasm
```
