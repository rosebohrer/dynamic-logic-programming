/** Propositional dynamic logic as a logic programming language.

The unique point is that we can model a software system in propositional dynamic logic
and then automatically prove correctness guarantees about the system. A typical example use is
to prove that a finite state machine satisfies an invariant property.

This crate contains both a library and an executable. The executable can be executed in either
batch or interactive mode. To execute interactive mode, runwith no arguments. To execute a file
in batch mode, pass the file as a command line argument.
*/
pub mod command_line;
pub mod debugger;
pub mod ast;
pub mod statics_common;
pub mod parser;
pub mod examples; 
pub mod pdlp;
pub mod ddlp;
pub mod printer_common;
pub mod frontends;