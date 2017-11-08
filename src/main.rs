
extern crate parity_wasm;
use parity_wasm::elements::*;
use parity_wasm::elements::Opcode::*;

extern crate tiny_keccak;
use tiny_keccak::Keccak;

use std::io::prelude::*;
use std::fs::File;

use std::str;
use std::env;

use std::collections::HashMap;

// enum for op codes

#[derive(Debug, Clone)]
enum Size {
    Mem8,
    Mem16,
    Mem32,
    Mem64,
}

#[derive(Debug, Clone)]
enum Packing {
    ZX,
    SX,
}

#[derive(Debug, Clone)]
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

enum InCode {
 NoIn,
 Immed,
 GlobalIn,
 StackIn0,
 StackIn1,
 StackIn2,
 StackInReg,
 StackInReg2,
 ReadPc,
 ReadStackPtr,
 CallIn,
 MemoryIn1,
 MemsizeIn,
 TableIn,
 MemoryIn2,
 TableTypeIn,
 InputSizeIn,
 InputNameIn,
 InputDataIn,
}

enum AluCode {
    Normal(u8),
    Trap,
    Exit,
    Min,
    CheckJump,
    Nop,
    FixMemory {
        memsize : Size,
        packing : Packing,
    },
    CheckJumpForward,
    CheckDynamicCall,
}

enum Reg {
    Reg1,
    Reg2,
    Reg3,
}

enum OutCode {
    StackOutReg1,
    StackOut0,
    StackOut1,
    StackOut2,
    CallOut,
    NoOut,
    GlobalOut,
    MemoryOut1 {
        memsize : Size,
    },
    MemoryOut2 {
        memsize : Size,
    },
    InputSizeOut,
    InputNameOut,
    InputCreateOut,
    InputDataOut,
    CallTableOut,
    CallTypeOut,
    SetStack,
    SetCallStack,
    SetTable,
    SetTableTypes,
    SetMemory,
    SetGlobals,
}

enum StackCode {
    StackRegSub,
    StackReg,
    StackReg2,
    StackReg3,
    StackInc,
    StackDec,
    StackNop,
    StackDec2,
    StackDecImmed
}

struct DecodedOp {
    read_reg1 : InCode,
    read_reg2 : InCode,
    read_reg3 : InCode,
    write1 : (Reg, OutCode),
    write2 : (Reg, OutCode),
    alu_code : AluCode,
    call_ch : StackCode,
    stack_ch : StackCode,
    pc_ch : StackCode,
    mem_ch : bool,
    immed : u64,
}

fn decode(i : &Inst) -> DecodedOp {
    use AluCode::*;
    use StackCode::*;
    use InCode::*;
    use OutCode::*;
    use Reg::*;

    let noop = DecodedOp {
        read_reg1: NoIn,
        read_reg2: NoIn,
        read_reg3: NoIn,
        write1: (Reg1, NoOut),
        write2: (Reg1, NoOut),
        alu_code: AluCode::Nop,
        call_ch: StackNop,
        stack_ch: StackNop,
        pc_ch: StackInc,
        mem_ch: false,
        immed: 0
    };
    match *i {
        NOP => noop,
        STUB(_) => noop,
        LABEL(_) => noop,
        UNREACHABLE => DecodedOp {alu_code: Trap, .. noop},
        EXIT => DecodedOp {alu_code:Exit, .. noop},
        JUMP(x) => DecodedOp {immed:x as u64, read_reg1: Immed, pc_ch: StackReg, .. noop},
        JUMPI(x) => DecodedOp {immed:x as u64, read_reg1: Immed, read_reg2: StackIn0, read_reg3: ReadPc, alu_code: CheckJump, pc_ch:StackReg, stack_ch: StackDec, .. noop},
        JUMPFORWARD(x) => DecodedOp {immed: x as u64, read_reg1: StackIn0, read_reg2: ReadPc, alu_code: CheckJumpForward, pc_ch: StackReg, stack_ch: StackDec, .. noop},
        CALL(x) => DecodedOp {immed:x as u64, read_reg1: Immed, read_reg2: ReadPc, write1: (Reg2, CallOut), call_ch: StackInc, pc_ch: StackReg, .. noop},
        CHECKCALLI(x) => DecodedOp {immed:x, read_reg1: StackIn0, read_reg2: TableTypeIn, alu_code: CheckDynamicCall, pc_ch: StackInc, .. noop},
        CALLI => DecodedOp {read_reg2: ReadPc, read_reg1: StackIn0, read_reg3: TableIn, pc_ch: StackReg3, write1: (Reg2, CallOut), call_ch: StackInc, stack_ch: StackDec, .. noop},
        INPUTSIZE => DecodedOp {read_reg1: StackIn0, read_reg2: InputSizeIn, write1: (Reg2, StackOut1), .. noop},
        INPUTNAME => DecodedOp {read_reg1: StackIn0, read_reg2: StackIn1, read_reg3: InputNameIn, write1: (Reg3, StackOut2), stack_ch: StackDec, .. noop},
        INPUTDATA => DecodedOp {read_reg1: StackIn0, read_reg2: StackIn1, read_reg3: InputDataIn, write1: (Reg3, StackOut2), stack_ch: StackDec, .. noop},
        OUTPUTSIZE => DecodedOp {read_reg1: StackIn0, read_reg2: StackIn1, write1: (Reg2, InputSizeOut), write2: (Reg2, InputCreateOut), stack_ch: StackDec2, .. noop},
        OUTPUTNAME => DecodedOp {immed:2, read_reg1: StackIn2, read_reg2: StackIn1, read_reg3: StackIn0, write1: (Reg3, InputNameOut), stack_ch: StackDecImmed, .. noop},
        OUTPUTDATA => DecodedOp {immed:2, read_reg1: StackIn2, read_reg2: StackIn1, read_reg3: StackIn0, write1: (Reg3, InputDataOut), stack_ch: StackDecImmed, .. noop},
        RETURN => DecodedOp {read_reg1: CallIn, call_ch: StackDec, pc_ch: StackReg, .. noop},
        LOAD {offset, ref memsize, ref packing} => DecodedOp {
            immed: offset as u64, read_reg1: StackIn0, read_reg2: MemoryIn1, read_reg3: MemoryIn2,
            alu_code: FixMemory{memsize:memsize.clone(), packing: packing.clone()},
            write1: (Reg1, StackOut1), .. noop},
        STORE {offset, ref memsize} => DecodedOp {
            immed: offset as u64,
            read_reg1: StackIn1,
            read_reg2: StackIn0,
            write1: (Reg2, MemoryOut1 {memsize: memsize.clone()}),
            write2: (Reg2, MemoryOut2 {memsize: memsize.clone()}),
            stack_ch: StackDec2, .. noop},
        DROP(x) => DecodedOp {immed: x as u64, read_reg1: Immed, stack_ch: StackRegSub, .. noop},
        DROPN => DecodedOp {read_reg1: StackIn0, stack_ch: StackRegSub, .. noop},
        DUP(x) => DecodedOp {immed: x as u64, read_reg1: Immed, read_reg2: StackInReg, write1: (Reg2, StackOut0), stack_ch: StackInc, .. noop},
        SET(x) => DecodedOp {immed: x as u64, read_reg1: Immed, read_reg2: StackIn0, write1: (Reg2, StackOutReg1), .. noop},
        LOADGLOBAL(x) => DecodedOp {immed: x as u64, read_reg1: Immed, read_reg2: GlobalIn, write1: (Reg2, StackOut0), stack_ch: StackInc, .. noop},
        STOREGLOBAL(x) => DecodedOp {immed: x as u64, read_reg1: Immed, read_reg2: StackIn0, write1: (Reg2, GlobalOut), stack_ch: StackDec, .. noop},
        INITCALLTABLE(x) => DecodedOp {immed: x as u64, read_reg2: StackIn0, write1: (Reg2, CallTableOut), stack_ch: StackDec, .. noop},
        INITCALLTYPE(x) => DecodedOp {immed: x as u64, read_reg2: StackIn0, write1: (Reg2, CallTypeOut), stack_ch: StackDec, .. noop},
        CURMEM => DecodedOp {stack_ch: StackInc, read_reg2: MemsizeIn, write1: (Reg2, StackOut0), .. noop},
        GROW => DecodedOp {read_reg2: MemsizeIn, read_reg3: StackIn0, mem_ch: true, stack_ch: StackDec, .. noop},
        PUSH(lit) => DecodedOp {immed: lit, read_reg1: Immed, stack_ch: StackInc, write1: (Reg1, StackOut0), .. noop},
        UNOP(op) => DecodedOp {read_reg1: StackIn0, write1: (Reg1, StackOut1), alu_code: Normal(op), .. noop},
        BINOP(op) => DecodedOp {read_reg1: StackIn1, read_reg2: StackIn0, write1: (Reg1, StackOut2), alu_code: Normal(op), stack_ch: StackDec, .. noop},
        SETSTACK(x) => DecodedOp {immed: x as u64, read_reg1: Immed, write1: (Reg1,SetStack), .. noop},
        SETCALLSTACK(x) => DecodedOp {immed: x as u64, read_reg1: Immed, write1: (Reg1,SetCallStack), .. noop},
        SETGLOBALS(x) => DecodedOp {immed: x as u64, read_reg1: Immed, write1: (Reg1,SetGlobals), .. noop},
        SETMEMORY(x) => DecodedOp {immed: x as u64, read_reg1: Immed, write1: (Reg1,SetMemory), .. noop},
        SETTABLE(x) => DecodedOp {immed: x as u64, read_reg1: Immed, write1: (Reg1,SetTableTypes), write2: (Reg1,SetTable), .. noop},
    }
}

// convert memory

// convert globals

// convert tables

// decoding

fn get_name(bytes: &[u8]) -> &str {
    str::from_utf8(bytes).ok().unwrap()
}

#[derive(Debug, Clone)]
struct Control {
    target : u32,
    rets : u32,
    level : u32,
    else_label : u32,
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

fn get_func_imports(m : &Module) -> Vec<&ImportEntry> {
    match m.import_section() {
        None => Vec::new(),
        Some(sec) => {
            let arr = sec.entries();
            arr.iter().filter(|&x| is_func(x.external())).collect::<Vec<&ImportEntry>>()
        }
    }
}

fn get_func_type(m : &Module, sig : u32) -> &FunctionType {
    match m.type_section().unwrap().types()[sig as usize] {
        Type::Function(ref t) => t
    }
}

fn find_func_type(m : &Module, num : u32) -> &FunctionType {
    // maybe it is import
    if num < get_num_imports(m) {
        let arr = m.import_section().unwrap().entries();
        let idx = match *arr.iter().filter(|&x| is_func(x.external())).collect::<Vec<&ImportEntry>>()[num as usize].external() {
            External::Function(idx) => idx,
            _ => 0,
        };
        get_func_type(m, idx)
    }
    // find it from sig section
    else {
        get_func_type(m, m.function_section().unwrap().entries()[(num - get_num_imports(m)) as usize].type_ref())
    }
}

fn num_func_returns(ft : &FunctionType) -> u32 {
    match ft.return_type() {
        None => 0,
        Some(_) => 1,
    }
}

fn count_locals(func : &FuncBody) -> u32 {
    func.locals().iter().fold(0, |sum, x| sum + x.count())
}

fn type_code(t : &ValueType) -> u8 {
    match *t {
        ValueType::I32 => 0,
        ValueType::I64 => 1,
        ValueType::F32 => 2,
        ValueType::F64 => 3,
    }
}

fn hash_ftype(ft : &FunctionType) -> u64 {
    let mut hash = Keccak::new_keccak256();
    let mut data = Vec::new();
    
    for t in ft.params() {
        data.push(type_code(t));
    }
    
    data.push(0xff);
    match ft.return_type() {
        None => {},
        Some(t) => data.push(type_code(&t)),
    }
    
    hash.update(&data);
    
    let mut arr: [u8; 32] = [0; 32];
    hash.finalize(&mut arr);
    let mut res : u64 = 0;
    for i in 0..7 {
        res = res*256 + arr[i] as u64;
    }
    // println!("Got result {}", res);
    res
}

fn handle_function(m : &Module, func : &FuncBody, idx : usize) -> Vec<Inst> {
    let sig = m.function_section().unwrap().entries()[idx].type_ref();
    let ftype = get_func_type(m, sig);
    
    println!("Got function with {:?} ops, {:?} locals and {} params",
        func.code().elements().len(), count_locals(func), ftype.params().len());
    // println!("{:?}", func.code().elements());
    
    // let num_imports = get_num_imports(m);
    
    let mut res : Vec<Inst> = Vec::new();
    let mut stack : Vec<Control> = Vec::new();
    let mut label : u32 = 0;
    let mut ptr : u32 = count_locals(func) + (ftype.params().len() as u32);
    let mut bptr : u32 = 0;
    
    // Construct the function top level frame
    let end_label = label;
    label = label + 1;
    bptr = bptr + 1;
    let rets = num_func_returns(ftype);
    stack.push(Control {level: rets, rets: rets, target: end_label, else_label: 0});
    
    // Push default values
    for i in 1..(count_locals(func) as usize) + ftype.params().len() {
        res.push(PUSH(0));
    }
    
    for op in func.code().elements().iter() {
        // println!("handling {}; {:?} ... label {}", ptr, op, label);
        match *op {
            Unreachable => res.push(UNREACHABLE),
            Nop => res.push(NOP),
            Block(bt) => {
                let end_label = label;
                label = label + 1;
                bptr = bptr + 1;
                let rets = block_len(&bt);
                stack.push(Control {level: ptr+rets, rets: rets, target: end_label, else_label: 0});
            },
            Loop(bt) => {
                let start_label = label;
                label = label + 1;
                bptr = bptr + 1;
                let rets = block_len(&bt);
                stack.push(Control {level: ptr+rets, rets: rets, target: start_label, else_label: 0});
                res.push(LABEL(start_label));
            },
            End => {
                if stack.len() == 0 { break; }
                let c : Control = stack.pop().unwrap();
                ptr = c.level;
                bptr = bptr - 1;
                if (c.else_label != 0) {
                    res.push(LABEL(c.else_label));
                }
                res.push(LABEL(c.target));
            },
            If(bt) => {
                ptr = ptr - 1;
                bptr = bptr + 1;
                let else_label = label;
                let end_label = label+1;
                let rets = block_len(&bt);
                stack.push(Control {level: ptr+rets, rets: rets, target: end_label, else_label});
                label = label+2;
                res.push(UNOP(0x50)); // I64Eqz
                res.push(JUMPI(else_label));
            },
            Else => {
                let mut c : Control = stack.pop().unwrap();
                res.push(LABEL(c.else_label));
                c.else_label = 0;
                stack.push(c);
            },
            Drop => {
                ptr = ptr - 1;
                res.push(DROP(1));
            },
            
            Br(x) => {
                let c = &stack[stack.len() - (x as usize) - 1];
                adjust_stack(&mut res, ptr - c.level, c.rets);
                ptr = ptr - c.rets;
                res.push(JUMP(c.target));
            },
            BrIf(x) => {
                let c = &stack[stack.len() - (x as usize) - 1];
                let continue_label =label;
                let end_label = label+1;
                label = label+2;
                res.push(JUMPI(continue_label));
                res.push(JUMP(end_label));
                res.push(LABEL(continue_label));
                adjust_stack(&mut res, ptr - c.level - 1, c.rets);
                res.push(JUMP(c.target));
                res.push(LABEL(end_label));
                ptr = ptr - 1;
            },
            Return => {
                let c = &stack[0];
                adjust_stack(&mut res, ptr - c.level, c.rets);
                ptr = ptr - c.rets;
                res.push(JUMP(c.target));
            },
            BrTable(ref tab, def) => {
                let rets = &stack[stack.len() - (def as usize) - 1].rets;
                let len = tab.len() as u32;
                res.push(JUMPFORWARD(len));
                for i in 0..len {
                    res.push(JUMP (label+i as u32));
                }
                for (i,num) in tab.iter().enumerate() {
                    let c = &stack[stack.len() - (*num as usize) - 1];
                    res.push(LABEL(label+i as u32));
                    adjust_stack(&mut res, ptr - c.level - 1, c.rets);
                    res.push(JUMP(c.target));
                }
                let c = &stack[stack.len() - (def as usize) - 1];
                res.push(LABEL(label+len as u32));
                adjust_stack(&mut res, ptr - c.level - 1, c.rets);
                res.push(JUMP(c.target));
                
                ptr = ptr-1-rets;
                label = label + len + 2;
            },
            
            Select => {
                let else_label = label;
                let end_label = label+1;
                res.push(JUMPI(else_label));
                res.push(SET(2));
                res.push(DROP(1));
                res.push(JUMP(end_label));
                res.push(LABEL(else_label));
                res.push(DROP(1));
                res.push(LABEL(end_label));
                
                label = label+2;
                ptr = ptr-2;
            },
            
            Call(x) => {
                let ftype = find_func_type(m, x);
                // println!("calling {} with type {:?}", x, ftype);
                res.push(CALL(x));
                ptr = ptr - (ftype.params().len() as u32) + num_func_returns(ftype);
            },
            CallIndirect(x,_) => {
                let ftype = get_func_type(m, x);
                res.push(CHECKCALLI(hash_ftype(&ftype)));
                res.push(CALLI);
                ptr = ptr - (ftype.params().len() as u32) + num_func_returns(ftype) - 1;
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
            TeeLocal(x) => {
                res.push(SET(ptr-x));
            },
            
            CurrentMemory(_) => {
                ptr = ptr+1;
                res.push(CURMEM);
            },
            GrowMemory(_) => {
                ptr = ptr-1;
                res.push(GROW);
            },
            
            I32Load(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem32, packing:Packing::ZX});
            },
            I32Load8S(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem8, packing:Packing::SX});
            },
            I32Load8U(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem8, packing:Packing::ZX});
            },
            I32Load16S(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem16, packing:Packing::SX});
            },
            I32Load16U(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem16, packing:Packing::ZX});
            },
            
            I64Load(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem64, packing:Packing::ZX});
            },
            I64Load8S(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem8, packing:Packing::SX});
            },
            I64Load8U(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem8, packing:Packing::ZX});
            },
            I64Load16S(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem16, packing:Packing::SX});
            },
            I64Load16U(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem16, packing:Packing::ZX});
            },
            I64Load32S(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem32, packing:Packing::SX});
            },
            I64Load32U(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem32, packing:Packing::ZX});
            },
            
            F32Load(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem32, packing:Packing::ZX});
            },
            F64Load(_, offset) => {
                res.push(LOAD {offset, memsize: Size::Mem64, packing:Packing::ZX});
            },
            
            I32Store(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem32});
            },
            I32Store8(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem8});
            },
            I32Store16(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem16});
            },
            
            I64Store(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem64});
            },
            I64Store8(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem8});
            },
            I64Store16(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem16});
            },
            I64Store32(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem32});
            },
            
            F32Store(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem32});
            },
            F64Store(_, offset) => {
                res.push(STORE {offset, memsize: Size::Mem64});
            },
            
            I32Eqz => res.push(UNOP(0x45)),
            I32Eq => { ptr = ptr - 1; res.push(BINOP(0x46)); },
            I32Ne => { ptr = ptr - 1; res.push(BINOP(0x47)); },
            I32LtS => { ptr = ptr - 1; res.push(BINOP(0x48)); },
            I32LtU => { ptr = ptr - 1; res.push(BINOP(0x49)); },
            I32GtS => { ptr = ptr - 1; res.push(BINOP(0x4a)); },
            I32GtU => { ptr = ptr - 1; res.push(BINOP(0x4b)); },
            I32LeS => { ptr = ptr - 1; res.push(BINOP(0x4c)); },
            I32LeU => { ptr = ptr - 1; res.push(BINOP(0x4d)); },
            I32GeS => { ptr = ptr - 1; res.push(BINOP(0x4e)); },
            I32GeU => { ptr = ptr - 1; res.push(BINOP(0x4f)); },
            
            I64Eqz => res.push(UNOP(0x50)),
            I64Eq => { ptr = ptr - 1; res.push(BINOP(0x51)); },
            I64Ne => { ptr = ptr - 1; res.push(BINOP(0x52)); },
            I64LtS => { ptr = ptr - 1; res.push(BINOP(0x53)); },
            I64LtU => { ptr = ptr - 1; res.push(BINOP(0x54)); },
            I64GtS => { ptr = ptr - 1; res.push(BINOP(0x55)); },
            I64GtU => { ptr = ptr - 1; res.push(BINOP(0x56)); },
            I64LeS => { ptr = ptr - 1; res.push(BINOP(0x57)); },
            I64LeU => { ptr = ptr - 1; res.push(BINOP(0x58)); },
            I64GeS => { ptr = ptr - 1; res.push(BINOP(0x59)); },
            I64GeU => { ptr = ptr - 1; res.push(BINOP(0x5a)); },
            
            F32Eq => { ptr = ptr - 1; res.push(BINOP(0x5b)); },
            F32Ne => { ptr = ptr - 1; res.push(BINOP(0x5c)); },
            F32Lt => { ptr = ptr - 1; res.push(BINOP(0x5d)); },
            F32Gt => { ptr = ptr - 1; res.push(BINOP(0x5e)); },
            F32Le => { ptr = ptr - 1; res.push(BINOP(0x5f)); },
            F32Ge => { ptr = ptr - 1; res.push(BINOP(0x60)); },
            
            F64Eq => { ptr = ptr - 1; res.push(BINOP(0x61)); },
            F64Ne => { ptr = ptr - 1; res.push(BINOP(0x62)); },
            F64Lt => { ptr = ptr - 1; res.push(BINOP(0x63)); },
            F64Gt => { ptr = ptr - 1; res.push(BINOP(0x64)); },
            F64Le => { ptr = ptr - 1; res.push(BINOP(0x65)); },
            F64Ge => { ptr = ptr - 1; res.push(BINOP(0x66)); },

            I32Clz => res.push(UNOP(0x67)),
            I32Ctz => res.push(UNOP(0x68)),
            I32Popcnt => res.push(UNOP(0x69)),
            I32Add => { ptr = ptr - 1; res.push(BINOP(0x6a)); },
            I32Sub => { ptr = ptr - 1; res.push(BINOP(0x6b)); },
            I32Mul => { ptr = ptr - 1; res.push(BINOP(0x6c)); },
            I32DivS => { ptr = ptr - 1; res.push(BINOP(0x6d)); },
            I32DivU => { ptr = ptr - 1; res.push(BINOP(0x6e)); },
            I32RemS => { ptr = ptr - 1; res.push(BINOP(0x6f)); },
            I32RemU => { ptr = ptr - 1; res.push(BINOP(0x70)); },
            I32And => { ptr = ptr - 1; res.push(BINOP(0x71)); },
            I32Or => { ptr = ptr - 1; res.push(BINOP(0x72)); },
            I32Xor => { ptr = ptr - 1; res.push(BINOP(0x73)); },
            I32Shl => { ptr = ptr - 1; res.push(BINOP(0x74)); },
            I32ShrS => { ptr = ptr - 1; res.push(BINOP(0x75)); },
            I32ShrU => { ptr = ptr - 1; res.push(BINOP(0x75)); },
            I32Rotl => { ptr = ptr - 1; res.push(BINOP(0x77)); },
            I32Rotr => { ptr = ptr - 1; res.push(BINOP(0x78)); },

            I64Clz => res.push(UNOP(0x79)),
            I64Ctz => res.push(UNOP(0x7a)),
            I64Popcnt => res.push(UNOP(0x7b)),
            I64Add => { ptr = ptr - 1; res.push(BINOP(0x7c)); },
            I64Sub => { ptr = ptr - 1; res.push(BINOP(0x7d)); },
            I64Mul => { ptr = ptr - 1; res.push(BINOP(0x7e)); },
            I64DivS => { ptr = ptr - 1; res.push(BINOP(0x7f)); },
            I64DivU => { ptr = ptr - 1; res.push(BINOP(0x80)); },
            I64RemS => { ptr = ptr - 1; res.push(BINOP(0x81)); },
            I64RemU => { ptr = ptr - 1; res.push(BINOP(0x82)); },
            I64And => { ptr = ptr - 1; res.push(BINOP(0x83)); },
            I64Or => { ptr = ptr - 1; res.push(BINOP(0x84)); },
            I64Xor => { ptr = ptr - 1; res.push(BINOP(0x85)); },
            I64Shl => { ptr = ptr - 1; res.push(BINOP(0x86)); },
            I64ShrS => { ptr = ptr - 1; res.push(BINOP(0x87)); },
            I64ShrU => { ptr = ptr - 1; res.push(BINOP(0x88)); },
            I64Rotl => { ptr = ptr - 1; res.push(BINOP(0x89)); },
            I64Rotr => { ptr = ptr - 1; res.push(BINOP(0x8a)); },
            
            F32Abs => res.push(UNOP(0x8b)),
            F32Neg => res.push(UNOP(0x8c)),
            F32Ceil => res.push(UNOP(0x8d)),
            F32Floor => res.push(UNOP(0x8e)),
            F32Trunc => res.push(UNOP(0x8f)),
            F32Nearest => res.push(UNOP(0x90)),
            F32Sqrt => res.push(UNOP(0x91)),
            F32Add => { ptr = ptr - 1; res.push(BINOP(0x92)); },
            F32Sub => { ptr = ptr - 1; res.push(BINOP(0x93)); },
            F32Mul => { ptr = ptr - 1; res.push(BINOP(0x94)); },
            F32Div => { ptr = ptr - 1; res.push(BINOP(0x95)); },
            F32Min => { ptr = ptr - 1; res.push(BINOP(0x96)); },
            F32Max => { ptr = ptr - 1; res.push(BINOP(0x97)); },
            F32Copysign => { ptr = ptr - 1; res.push(BINOP(0x98)); },
            
            F64Abs => res.push(UNOP(0x99)),
            F64Neg => res.push(UNOP(0x9a)),
            F64Ceil => res.push(UNOP(0x9b)),
            F64Floor => res.push(UNOP(0x9c)),
            F64Trunc => res.push(UNOP(0x9d)),
            F64Nearest => res.push(UNOP(0x9e)),
            F64Sqrt => res.push(UNOP(0x9f)),
            F64Add => { ptr = ptr - 1; res.push(BINOP(0xa0)); },
            F64Sub => { ptr = ptr - 1; res.push(BINOP(0xa1)); },
            F64Mul => { ptr = ptr - 1; res.push(BINOP(0xa2)); },
            F64Div => { ptr = ptr - 1; res.push(BINOP(0xa3)); },
            F64Min => { ptr = ptr - 1; res.push(BINOP(0xa4)); },
            F64Max => { ptr = ptr - 1; res.push(BINOP(0xa5)); },
            F64Copysign => { ptr = ptr - 1; res.push(BINOP(0xa6)); },
            
            
            I32WarpI64 => res.push(UNOP(0xa7)),
            I32TruncSF32 => res.push(UNOP(0xa8)),
            I32TruncUF32 => res.push(UNOP(0xa9)),
            I32TruncSF64 => res.push(UNOP(0xaa)),
            I32TruncUF64 => res.push(UNOP(0xab)),
            I64ExtendSI32 => res.push(UNOP(0xac)),
            I64ExtendUI32 => res.push(UNOP(0xad)),
            I64TruncSF32 => res.push(UNOP(0xae)),
            I64TruncUF32 => res.push(UNOP(0xaf)),
            I64TruncSF64 => res.push(UNOP(0xb0)),
            I64TruncUF64 => res.push(UNOP(0xb1)),
            F32ConvertSI32 => res.push(UNOP(0xb2)),
            F32ConvertUI32 => res.push(UNOP(0xb3)),
            F32ConvertSI64 => res.push(UNOP(0xb4)),
            F32ConvertUI64 => res.push(UNOP(0xb5)),
            F32DemoteF64 => res.push(UNOP(0xb6)),
            F64ConvertSI32 => res.push(UNOP(0xb7)),
            F64ConvertUI32 => res.push(UNOP(0xb8)),
            F64ConvertSI64 => res.push(UNOP(0xb9)),
            F64ConvertUI64 => res.push(UNOP(0xba)),
            F64PromoteF32 => res.push(UNOP(0xbb)),

            I32ReinterpretF32 => res.push(UNOP(0xbc)),
            I64ReinterpretF64 => res.push(UNOP(0xbd)),
            F32ReinterpretI32 => res.push(UNOP(0xbe)),
            F64ReinterpretI64 => res.push(UNOP(0xbf)),
            
        }
    }
    
    // function exit, make stack adjustments
    if rets > 0 {
        for i in 0..rets-1 {
            res.push(DUP(rets-i));
            res.push(SET(ptr-i+1));
            res.push(DROP(1));
        }
    }
    res.push(DROP (count_locals(func) + (ftype.params().len() as u32)));
    res.push(RETURN);
    res
}

fn resolve_func_labels(arr : &Vec<Inst>) -> Vec<Inst> {
    let mut table = HashMap::new();
    for (i, el) in arr.iter().enumerate() {
        match *el {
            LABEL(x) => { table.insert(x, i as u32); },
            _ => {}
        }
    }
    arr.iter().map(|x| {
        match *x {
            JUMPI(x) => JUMPI(*(table.get(&x).unwrap())),
            JUMP(x) => JUMP(*(table.get(&x).unwrap())),
            ref a => a.clone()
        }
        }).collect::<Vec<Inst>>()
}

fn init_value(m : &Module, expr : &InitExpr) -> u64 {
    0
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("Usage: {} in.wasm", args[0]);
        return;
    }
    
    let module = parity_wasm::deserialize_file(&args[1]).ok().unwrap();

    let code_section = module.code_section().unwrap(); // Part of the module with functions code
    let num_imports = get_num_imports(&module);
    
    println!("Function count in wasm file: {}", code_section.bodies().len());
    println!("Function signatures in wasm file: {}", module.function_section().unwrap().entries().len());
    println!("Function imports: {}", num_imports);
    
    let mut res = Vec::new();
    let mut table = HashMap::new();
    
    // init call table
    if let Some(sec) = module.elements_section() {
        let mut count = 0;
        for els in sec.entries().iter() {
            for el in els.members().iter() {
                res.push(NOP);
                res.push(NOP);
                res.push(NOP);
                res.push(NOP);
                count = count+1;
            }
        }
        println!("Found {} elements in the call table", count);
    }
    
    // init globals, first imports
    let mut globals = 0;
    if let Some(sec) = module.import_section() {
        for entry in sec.entries().iter() {
            if let &External::Global(_) = entry.external() {
                res.push(PUSH(0));
                res.push(STOREGLOBAL(globals));
                globals = globals + 1;
            }
        }
    }
    
    // then own globals
    if let Some(sec) = module.global_section() {
        for g in sec.entries().iter() {
            res.push(PUSH(init_value(&module, g.init_expr())));
            res.push(STOREGLOBAL(globals));
            globals = globals + 1;
        }
    }
    
    // init memory
    if let Some(sec) = module.data_section() {
        for seg in sec.entries().iter() {
            let offset = init_value(&module, seg.offset());
            for (i, bt) in seg.value().iter().enumerate() {
                res.push(PUSH(offset+i as u64));
                res.push(PUSH(*bt as u64));
                res.push(STORE{offset:0, memsize:Size::Mem8});
            }
        }
    }
    
    // make the initializer for file system, command line parameters
    
    // handle imports (just empty codes now)
    for (idx,f) in get_func_imports(&module).iter().enumerate() {
        table.insert(idx as u32, res.len() as u32);
    }
    
    // so we do not have parameters here, have to the get them from elsewhere?
    for (idx,f) in code_section.bodies().iter().enumerate() {
        let mut arr = handle_function(&module, f, idx);
        let arr = resolve_func_labels(&mut arr);
        table.insert(idx as u32 +num_imports, res.len() as u32);
        for el in arr {
            res.push(el.clone());
        }
    }
    
    // setup call table
    if let Some(sec) = module.elements_section() {
        let mut pos = 0; // should be length of vm init
        for seg in sec.entries().iter() {
            let offset = init_value(&module, seg.offset()) as u32;
            for (idx, fnum) in seg.members().iter().enumerate() {
                res[pos+0] = PUSH(*table.get(fnum).unwrap() as u64);
                res[pos+1] = INITCALLTABLE(offset + idx as u32);
                res[pos+2] = PUSH(hash_ftype(find_func_type(&module, *fnum)));
                res[pos+3] = INITCALLTYPE(offset + idx as u32);
                
                pos = pos+4;
            }
        }

    }

    // resolve calls
    let res = res.iter().map(|x| {
        match *x {
            CALL(x) => CALL(*(table.get(&x).unwrap())),
            ref a => a.clone()
        }
        }).collect::<Vec<Inst>>();

}

