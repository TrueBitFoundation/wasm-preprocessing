
extern crate parity_wasm;
use parity_wasm::elements::*;
use parity_wasm::elements::Opcode::*;

/*
extern crate wasmparser;
use wasmparser::WasmDecoder;
use wasmparser::Parser;
use wasmparser::ParserState;
*/

use std::io::prelude::*;
use std::fs::File;

use std::str;
use std::env;

use std::collections::HashMap;

// enum for op codes

/*

These can just be binary values?

enum Op<TI32, TI64, TF32, TF64> {
  I32(TI32),
  I64(TI64),
  F32(TF32),
  F64(TF64),
}

enum IntUnop = Clz | Ctz | Popcnt
enum IntBinop = Add | Sub | Mul | DivS | DivU | RemS | RemU
             | And | Or | Xor | Shl | ShrS | ShrU | Rotl | Rotr
enum IntTestop = Eqz
enum IntRelop = Eq | Ne | LtS | LtU | GtS | GtU | LeS | LeU | GeS | GeU
enum IntCvtop = ExtendSI32 | ExtendUI32 | WrapI64
             | TruncSF32 | TruncUF32 | TruncSF64 | TruncUF64
             | ReinterpretFloat

struct LoadOp {
    
}


*/

enum Size {
    Mem8,
    Mem16,
    Mem32,
    Mem64,
}

enum Packing {
    ZX,
    SX,
}

enum Inst {
 EXIT,
 UNREACHABLE,
 NOP,
 JUMP(u32),
 JUMPI(u32),
 JUMPFORWARD(u32),
 CALL(u32),
 LABEL(u32),
 RETURN,
 LOAD {
    offset: u32,
    memsize : Size,
    packing : Packing,
 },
 STORE {
    offset: u32,
    memsize : Size,
 },
 DROP(u32),
 DROPN,
 DUP(u32),
 SET(u32),
 LOADGLOBAL(u32),
 STOREGLOBAL(u32),
 CURMEM,
 GROW,
 CALLI,
 CHECKCALLI(u64),
 PUSH(u64),
 UNOP(u8),
 BINOP(u8),
 STUB(String),
 INPUTSIZE,
 INPUTNAME,
 INPUTDATA,
 OUTPUTSIZE,
 OUTPUTNAME,
 OUTPUTDATA,
 INITCALLTABLE(u32),
 INITCALLTYPE(u32),
 SETSTACK(u32),
 SETCALLSTACK(u32),
 SETTABLE(u32),
 SETGLOBALS(u32),
 SETMEMORY(u32),
}

use Inst::*;

// convert memory

// convert globals

// convert tables

// decoding

fn get_name(bytes: &[u8]) -> &str {
    str::from_utf8(bytes).ok().unwrap()
}

fn read_wasm_bytes(fname : &str) -> std::io::Result<Vec<u8>> {
    let mut f = File::open(fname)?;

    let mut buffer = Vec::new();
    // read the whole file
    f.read_to_end(&mut buffer)?;
    return Ok(buffer);
}

struct Control {
    target : u32,
    rets : u32,
    level : u32,
}

/*
struct FuncType {
    
}

struct Context {
    ptr : u32,
    bptr : u32,
    label : u32,
    f_types : HashMap<u32, FuncType>,
    f_types2 : HashMap<u32, FuncType>,
    block_return : Vec<Control>,
}
*/

fn block_len(bt : &BlockType) -> u32 {
    match *bt {
        BlockType::Value(_) => 1,
        BlockType::NoResult => 0,
    }
}

// Read instructions until block end?
// Or perhaps process whole function?

/*
fn process_block(locals : u32, ops : &Opcodes) {
}
*/

fn adjust_stack(res : &mut Vec<Inst>, diff : u32, num : u32) {
    if diff == 0 { return; }
    for i in num..1 {
        res.push(DUP(i));
        res.push(SET(diff+i+1));
        res.push(DROP(1));
    }
    res.push(DROP(diff));
}

fn is_func(e : &External) -> bool {
    match *e {
        External::Function(idx) => {
            true
        },
        _ => false
    }
}

fn get_num_imports(m : &Module) -> u32 {
    match m.import_section() {
        None => 0,
        Some(sec) => {
            let arr = sec.entries();
            arr.iter().filter(|&x| is_func(x.external())).count() as u32
        }
    }
}

fn get_func_type(m : &Module, sig : u32) -> &FunctionType {
    match m.type_section().unwrap().types()[sig as usize] {
        Type::Function(ref t) => t
    }
}

fn handle_function(m : &Module, func : &FuncBody, idx : usize) {
    println!("Got function with {:?} ops", func.code().elements().len());
    println!("{:?}", func.code().elements());
    
    let sig = m.function_section().unwrap().entries()[idx].type_ref();
    let ftype = get_func_type(m, sig);
    // let num_imports = get_num_imports(m);
    
    let mut res : Vec<Inst> = Vec::new();
    let mut stack : Vec<Control> = Vec::new();
    let mut label : u32 = 0;
    let mut ptr : u32 = (func.locals().len() + ftype.params().len()) as u32;
    let mut bptr : u32 = 0;
    for op in func.code().elements().iter() {
        match *op {
            Unreachable => res.push(UNREACHABLE),
            Nop => res.push(NOP),
            Block(bt) => {
                let end_label = label;
                label = label + 1;
                bptr = bptr + 1;
                let rets = block_len(&bt);
                stack.push(Control {level: ptr+rets, rets: rets, target: end_label});
            },
            Loop(bt) => {
                let start_label = label;
                label = label + 1;
                bptr = bptr + 1;
                let rets = block_len(&bt);
                stack.push(Control {level: ptr+rets, rets: rets, target: start_label});
                res.push(LABEL(start_label));
            },
            End => {
                if stack.len() == 0 { break; }
                let c : Control = stack.pop().unwrap();
                ptr = c.level;
                bptr = bptr - 1;
                res.push(LABEL(c.target));
            },
            If(bt) => {
                ptr = ptr - 1;
                bptr = bptr + 1;
                let else_label = label;
                let end_label = label+1;
                let rets = block_len(&bt);
                stack.push(Control {level: ptr+rets, rets: rets, target: end_label});
                label = label+2;
                res.push(UNOP(0x50)); // I64Eqz
                res.push(JUMPI(else_label));
            },
            Else => {
                let c : Control = stack.pop().unwrap();
                res.push(LABEL(c.target));
                stack.push(c);
            },
            
            Br(x) => {
                let c = &stack[stack.len() - (x as usize)];
                adjust_stack(&mut res, ptr - c.level, c.rets);
                ptr = ptr - c.rets;
                res.push(JUMP(c.target));
            },
            
            I32Const(x) => {
                res.push(PUSH(x as u64));
                ptr = ptr+1;
            },
            I64Const(x) => {
                res.push(PUSH(x as u64));
                ptr = ptr+1;
            },
            F32Const(x) => {
                res.push(PUSH(x as u64));
                ptr = ptr+1;
            },
            F64Const(x) => {
                res.push(PUSH(x as u64));
                ptr = ptr+1;
            },
            
            GetGlobal(x) => {
                ptr = ptr + 1;
                res.push(LOADGLOBAL(x));
            },
            SetGlobal(x) => {
                ptr = ptr - 1;
                res.push(STOREGLOBAL(x));
            },
            
            GetLocal(x) => {
                res.push(DUP(ptr-x));
                ptr = ptr + 1;
            },
            SetLocal(x) => {
                res.push(SET(ptr-x));
                res.push(DROP(1));
                ptr = ptr - 1;
            },
            
            I32Load(flag, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem32, packing:Packing::ZX});
            },
            
            I32Add => {
                ptr = ptr - 1;
                res.push(BINOP(0x62));
            },
            I32And => {
                ptr = ptr - 1;
                res.push(BINOP(0x71));
            },
            F32ConvertSI32 => {
                res.push(UNOP(0xb2));
            },
            
            _ => {
                println!("at {:?}", op);
            }
        }
    }
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("Usage: {} in.wasm", args[0]);
        return;
    }
    
    let module = parity_wasm::deserialize_file(&args[1]).ok().unwrap();

    let code_section = module.code_section().unwrap(); // Part of the module with functions code
    
    println!("Function count in wasm file: {}", code_section.bodies().len());
    println!("Function signatures in wasm file: {}", module.function_section().unwrap().entries().len());
    
    // so we do not have parameters here, have to the get them from elsewhere?
    for (idx,f) in code_section.bodies().iter().enumerate() {
        handle_function(&module, f, idx);
    }


/*

    let ref buf: Vec<u8> = read_wasm_bytes(&args[1]).unwrap();
    let mut parser = Parser::new(buf);
    loop {
        let state = parser.read();
        match *state {
            ParserState::ExportSectionEntry {
                field,
                ref kind,
                index,
            } => {
                println!("ExportSectionEntry {{ field: \"{}\", kind: {:?}, index: {} }}",
                         get_name(field),
                         kind,
                         index);
            }
            ParserState::ImportSectionEntry {
                module,
                field,
                ref ty,
            } => {
                println!("ImportSectionEntry {{ module: \"{}\", field: \"{}\", ty: {:?} }}",
                         get_name(module),
                         get_name(field),
                         ty);
            }
            ParserState::EndWasm => break,
            // ParserState::BeginFunctionBody {range} => process_block(&mut parser),
            ParserState::Error(err) => panic!("Error: {:?}", err),
            _ => println!("{:?}", state),
        }
    }
    let state = parser.read();
    */
}

