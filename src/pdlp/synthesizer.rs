/*! Exploits proof search to generate a program which satisfies the given specification 
  This synthesis algorithm is designed for the box-free fragment of PDLP.
*/
use crate::command_line::Verbosity::DebugVerbose;
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

    /** Start proof search */
    pub fn start(&mut self) -> () {
        if !self.ca.is_synthesizer_enabled() { return; }
        if self.ca.verbosity() == DebugVerbose { println!("TRACE: START"); }
        self.stack = vec![vec![SynthRecord{sl: vec![]}]];
    }
    
    /** Split into n branches for constant c
     * usize < 1 indicates branching that does not generate code, such as or-branching.
     */
    pub fn branch(&mut self, c: &String, n: usize) -> () {
        if !self.ca.is_synthesizer_enabled() { return; }
        if self.ca.verbosity() == DebugVerbose { println!("TRACE: BRANCH {}/{}", c, n); }
        if self.stack.is_empty() || self.stack.last().expect("NONEMPTY").is_empty() {
            if self.ca.verbosity() == DebugVerbose { println!("TRACE: STACK: {:?}", self.stack.clone()); }
            return;
        }
        /** Binary branching with no effect on program, just add 1 alternative */
        if n == 0 {
            let curr = self.stack.last().expect("NONEMPTY")[0].clone();
            self.stack.push(vec![curr.clone(), curr]);
        } else /* Real branching */ { 
            let curr = self.stack.last().expect("NONEMPTY")[0].clone();            
            let mut alts = vec![];
            for i in 0..n {
                let sc = SynthConst { c: c.clone(), i};
                let mut sl = curr.sl.clone();
                sl.push(sc);
                let sr = SynthRecord { sl };
                alts.push(sr);
            }
            self.stack.push(alts);
        }
    }
    
    /** Try next branch */
    pub fn next(&mut self) -> () {
        if !self.ca.is_synthesizer_enabled() { return; }
        if self.ca.verbosity() == DebugVerbose { println!("TRACE: NEXT-START: {:?}", self.stack); }
        if self.stack.is_empty() {
          return;
        } else {
          loop {
            if self.stack.is_empty() || self.stack.last().expect("NONEMPTY").is_empty(){ return; }
            let mut alts = self.stack.pop().expect("NONEMPTY");
            let _alt = alts.remove(0);
            if !alts.is_empty() { self.stack.push(alts); break; }
          } 
        if self.ca.verbosity() == DebugVerbose { println!("TRACE: NEXT-END: {:?}", self.stack); }
        }
    }
    
    /** Search has succeeeded, record current candidate program as a winner */
    pub fn finish(&mut self) -> () {
        if !self.ca.is_synthesizer_enabled() { return; }
        // points behave like a stack FIFO
        let point = if self.stack.is_empty() { vec![] } else {self.stack.last().expect("NONEMPTY").clone() }; 
        // records within a point behave left-right so take leftmost
        let record = if point.is_empty() { SynthRecord { sl : vec![]} } else {point[0].clone() }; 
        self.result = Some (record);
        if self.ca.verbosity() == DebugVerbose { println!("TRACE: FINISH: {:?}", self.result); }
    }
}