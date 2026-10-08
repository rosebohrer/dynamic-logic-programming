/*! Exploits proof search to generate a program which satisfies the given specification 
  This synthesis algorithm is designed for the box-free fragment of PDLP.
*/
use crate::command_line::{CommandLineArgs, Verbosity};
use crate::ast::{Formula,Program,FormulaNode,ProgramNode};
use FormulaNode::*; use ProgramNode::*;

/** A single program constant c in the source program corresponds to a family of constants c_i for synthesis.
  This data structure represents a single such c_i */
#[derive(Clone, Debug)]
pub struct SynthConst {
    c: String,
    i: usize,
}

/** The synthesis state for a single branch of proof search (which may have multiple open goals).
  When multiple goals G1 & ... & GN are open, all except GN represent test conditions, which do not
  contribute to the synthesized program. Thus it is sufficient to consider only GN.
  Because the diamond fragment of PDLP always synthesizes straight-line programs, the state of a program
  being synthesized is just the sequence of program constants which we have decided to invoke so far.
  Every time a program constant is executed during proof search, a symbol is appended to the end.
*/
#[derive(Clone, Debug)]
pub struct SynthRecord { 
    sl: Vec<SynthConst>,
}

/** Main data structure for synthesis, contains entire state during proof search, covering
  all outstanding search branches */
#[derive(Clone, Debug)]
pub struct Synthesizer {
  /** Command-line arguments provided by the user, which may include flags 
      controlling the synthesizer. */
  pub ca: CommandLineArgs,
  /** Synthesizer data structure follows the same structure as the machine's stack for backtracking
    proof search. Each entry in the outermost vector corresponds to a point where branching occurs 
    in the search. The entry contains all remaining alternatives at that point in the search. 
    Each alternative contains a SynthRecord containing an in-progress synthesized program. */
  pub stack: Vec<Vec<SynthRecord>>,
  /** Successfully synthesized program at end of search, if any */
  pub result: Option<SynthRecord>,
}

impl Synthesizer {
    /** Initialize synthesizer based on provided command line flags */
    pub fn of_command_line(ca: &CommandLineArgs) -> Self {
        Synthesizer {ca: ca.clone(), stack: vec![], result: None}
    }

    /** Initialize synthesizer to default status */
    pub fn default() -> Self {
        Synthesizer {ca: CommandLineArgs::DEFAULT, stack: vec![], result: None}
    } 

    /** @TODO: Confirm that this API is sufficient by reading dynamics */
    /** Start proof search */
    pub fn start(&mut self) -> () {
        self.stack = vec![vec![SynthRecord{sl: vec![]}]]
    }
    
    /** Split into n branches for constant c */
    pub fn branch(&mut self, c: &String, n: usize) -> () {

    }
    
    /** Try next branch */
    pub fn next(&mut self) -> () {

    }
    
    /** Search has succeeeded, record current candidate program as a winner */
    pub fn finish(&mut self) -> () {

    }
}