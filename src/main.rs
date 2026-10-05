/*! Entry point for command-line executable.

This file is responsible for handling top-level input-output, with 
all interesting processing of programs delegated to other files.
*/
/* @TODO: Some of the program static-checking code is separate for batch
  mode and interactive mode. As much as possible, both modes should use the same
  code path, to prevent the languages supported by each tool from diverging 
*/

use std::path::PathBuf;
use std::fs::File;
use std::io;
use std::io::prelude::*;
use std::collections::HashSet;

use glp::command_line::{CommandLineArgs,HELP};
use glp::parser::pdlp::logic_program;
use glp::statics_common;
use glp::pdlp::statics::*;
use glp::pdlp::dynamics::{DynamicMachine, StaticMachine, Machine};
use glp::printer_common;
use glp::ast::*;
use glp::pdlp;

/** Symbol displayed to user as top-level prompt */
const TOP_PROMPT: &str = "-  ";

/** Full message explaining REPL usage. */
const REPL_HELP: &str = 
"Interactive mode supports the following commands:
help            Print this help message
quit            Exit the program
print           Print all definitions to the screen
def DEFINITION  Add DEFINITION to the program.
?- FORMULA      Execute the query FORMULA.

DEFINITION and FORMULA follow the same syntax as batch mode.
Example DEFINITIONS:
prog ::= a U b; c U d.
a <- b, a <- c.
[d]a <- b, [d]b <- b.

Example FORMULA:
a & b -> c | [d]e

If the input is not a complete command, the continuation prompt 
(> symbol) will be displayed. To return from this prompt to the top-level,
press the Enter key a second time.
";


//@TODO: Detect partial inputs that cannot possibly complete, reject them
/** Read one command from user over stdin. 

If a partial command is provided, additional lines are read until the command is
complete. If a blank line is read, the partial command is canceled.
*/
fn read_repl_command() -> REPLCommand {
  let mut buffer = String::new();
  let stdin = io::stdin();
  loop {
    match stdin.read_line(&mut buffer) {
        Ok(n) if n == 1 => { return REPLCommand::DoNothing() }, 
        Ok(_) => {
            match glp::parser::pdlp::repl_command(&buffer) {
                Ok(rc) => return rc,
                // Symbol > is the continuation prompt, requisting more input.
                Err(_) => {print!("> "); let _ = io::stdout().flush(); }
            }
        }
        Err(e) => {eprintln!("Read failed: {}", e);}
    }
  }
}

/** Execute one definition in interactive mode. */
fn interactive_defn(cs: &mut HashSet<String>, ds: &mut HashSet<String>, sm: &mut StaticMachine, dd: &Vec<Defn>) {
    for d in dd {
      sm.define(d)
    }
}

/** Execute one query in interactive mode */
fn interactive_query(m: &mut Machine, f: &Formula) {
    let m_prev = m.clone();
    m.inquire(f);
    m.run();
    if m.is_proved() {
        println!("Theorem proved: {}", printer_common::formula(f));
    } else {
        eprintln!("Machine stuck:\n{}", pdlp::printer::machine(&m));
        *m = m_prev;
    }
}

/** Entry point for interactive mode. */
fn interactive (_args: &CommandLineArgs) {
    let mut clause_syms: HashSet<String> = HashSet::new();
    let mut defined_syms: HashSet<String> = HashSet::new();
    println!("Interactive mode. Type help and press Enter for instructions.");
    // Maintain separate static and dynamic machine instead of combined Machine for
    // borrow checker compatibility reasons.
    let mut sm = StaticMachine::new();
    let dm = DynamicMachine::new();
    loop {
      print!("{}", TOP_PROMPT); let _ = io::stdout().flush(); 
      match read_repl_command() {
        REPLCommand::DoNothing() => {},
        REPLCommand::Help() => {println!("{}", REPL_HELP);},
        REPLCommand::Quit() => {return;},
        REPLCommand::Print() => {
            let m = Machine {sm: &sm, dm: dm.clone()};
            println!("{}", pdlp::printer::machine_prog(&m));
        },
        REPLCommand::Define(d) => {
            let dd = statics_common::normalize_body(d);
            interactive_defn(&mut clause_syms, &mut defined_syms, &mut sm, &dd.unwrap())
        },
        REPLCommand::Query(f) => {
            let mut m = Machine {sm: &sm.clone(), dm: dm.clone() };
            interactive_query(&mut m, &f)
        },
      }
    }
}

fn index_str(source: &String, i: i32) -> String {
    let delim_len = if source.contains("\r\n") { 2 } else { 1};
    let mut row = 1;
    let mut col = i;
    for line in source.lines() {
        let ilen = i32::try_from(line.len()).unwrap();
        if col < ilen {
            break;
        } else {
            row = row + 1;
            col = col - (delim_len + ilen);
        }
    }
    format!("{}:{}", row,col)
}

fn span_str(source: &String, s: Span) -> String {
    format!("{}-{}", index_str(source,s.start), index_str(source,s.start+s.len))
}

// @TODO: Rewrite to use ? syntax for clarity.
/** Entry point for batch mode. */
fn batch (args: &CommandLineArgs) {
    for filename in &args.input_files {
        let path = PathBuf::from(&filename);
        match File::open(&path) {
            Result::Err(e) => {eprintln!("Skipping file {:?}, could not open due to error: {}", filename, e)},
            Result::Ok(mut file) => {
                let mut source = String::new();
                match file.read_to_string(&mut source) {
                    Ok(_len) => {
                        match logic_program(&source) {
                            Ok(lp) => {
                                let nlp = statics_common::normalize(*lp).unwrap();
                                println!("Running file {:?} ...", filename);
                                let mut sm = StaticMachine::new();
                                let mut m = Machine::of_lp(&mut sm, &nlp);
                                m.run();
                                if m.is_proved() {
                                    println!("Theorem proved: {}", printer_common::formula(&nlp.query));
                                } else {
                                    eprintln!("Machine stuck:\n{}", pdlp::printer::machine(&m));
                                }
                            },
                            Err(e) => eprintln!("Skipping file {:?}, parse error: {}", filename, e)
                        }
                    }
                    Err(e) => {eprintln!("Skipping file {:?}, could not read due to error: {}", filename, e)}
                }       
            }
        }
    }    
}

/** Main entry point */
pub fn main () {
    let args = CommandLineArgs::from_env();
    if args.help {
        println!("{}", HELP);
        return;
    } else if args.is_interactive() {
        interactive(&args);
    } else {
        batch(&args);
    }
}