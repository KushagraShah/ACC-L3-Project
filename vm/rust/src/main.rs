mod memory;
mod engine;

use std::{env, process};
use std::fs::File;
use std::io::{BufReader, BufRead};

use crate::engine::Engine;
use crate::memory::Memory;

pub type L3Value = i32;
pub const LOG2_VALUE_BYTES : usize = 2;
pub const LOG2_VALUE_BITS  : usize = 5;
pub const VALUE_BITS       : usize = 1 << LOG2_VALUE_BITS;

const DEFAULT_MEMORY_SIZE  : usize = 1_000_000;

const TAG_REGISTER_FRAME : L3Value = 201;

fn load(file_name: &str, mem: &mut Memory, index: &mut usize)
        -> Result<(), String> {
    let file = File::open(file_name)
        .map_err(|_| format!("can't open file {}", file_name))?;

    for (i, line) in BufReader::new(file).lines().enumerate() {
        let line = line
            .map_err(|_| format!("I/O problem at line {}", i + 1))?;
        let instr = u32::from_str_radix(&line[0..8], 16)
            .map_err(|_| format!("can't parse line {}:\n{}", i + 1, line))?;
        mem[*index] = instr as i32;
        *index += 1;
    }
    Ok(())
}

enum Command {
    ShowHelp,
    Run { memory_size: usize, file_name: String },
}

fn parse_args() -> Result<Command, String> {
    let mut memory_size = DEFAULT_MEMORY_SIZE;
    let mut maybe_file_name = None;

    let mut args_it = env::args().skip(1);
    while let Some(arg) = args_it.next() {
        if arg == "-h" {
            return Ok(Command::ShowHelp)
        } else if arg == "-m" {
            if let Some(s) = args_it.next() {
                memory_size = s.parse::<usize>()
                    .map_err(|_| format!("invalid memory size: {}", s))?
            } else {
                Err(format!("missing argument to -m"))?
            }
        } else if maybe_file_name == None {
            maybe_file_name = Some(arg.to_string())
        } else {
            Err(format!("more than one file name given"))?
        }
    }
    maybe_file_name
        .map(|file_name| Command::Run { memory_size, file_name })
        .ok_or(format!("no file name given"))
}

fn actual_main() -> Result<i32, String> {
    match parse_args()? {
        Command::ShowHelp => {
            println!("Usage: {} [<options>] <asm_file>",
                     env::args().next().unwrap_or("l3vm".to_string()));
            println!("options:");
            println!("  -h         display this help message and exit");
            println!("  -m <size>  set memory size in bytes");
            Ok(0)
        },
        Command::Run { memory_size, file_name } => {
            let mut mem = Memory::new(memory_size >> 2);

            let mut index: usize = 0;
            load(&file_name, &mut mem, &mut index)?;

            let constant_regs = index;
            for constant in 0..32 {
                mem[index] = constant as L3Value;
                index += 1;
            }

            mem.set_heap_start(index);
            let mut engine = Engine::new(mem);
            engine.set_cb(constant_regs);
            Ok(engine.run())
        },
    }
}

fn main() {
    match actual_main() {
        Ok(exit_code) =>
            process::exit(exit_code),
        Err(e) => {
            eprintln!("Error: {}", e);
            process::exit(1)
        }
    }
}
