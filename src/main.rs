
extern crate wasmparser;

use wasmparser::WasmDecoder;
use wasmparser::Parser;
use wasmparser::ParserState;

use std::io::prelude::*;
use std::fs::File;
use std::io;

use std::str;

fn get_name(bytes: &[u8]) -> &str {
  str::from_utf8(bytes).ok().unwrap()
}

fn read_wasm_bytes() -> std::io::Result<Vec<u8>> {
   let mut f = File::open("test.wasm")?;

   let mut buffer = vec![0; 10];
   // read the whole file
   f.read_to_end(&mut buffer)?;
   return Ok(buffer);
}

fn main() {

  let ref buf: Vec<u8> = read_wasm_bytes().ok().unwrap();
  let mut parser = Parser::new(buf);
  loop {
    let state = parser.read();
    match *state {
        ParserState::BeginWasm { .. } => {
            println!("====== Module");
        }
        ParserState::ExportSectionEntry { field, ref kind, .. } => {
            println!("  Export {} {:?}", get_name(field), kind);
        }
        ParserState::ImportSectionEntry { module, field, .. } => {
            println!("  Import {}::{}", get_name(module), get_name(field))
        }
        ParserState::EndWasm => break,
        _ => ( /* println!(" Other {:?}", state) */ )
    }
  }
}

