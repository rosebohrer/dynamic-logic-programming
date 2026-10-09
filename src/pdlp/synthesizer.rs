/*! Exploits proof search to generate a program which satisfies the given specification 
  This synthesis algorithm is designed for the box-free fragment of PDLP.
*/
use crate::command_line::Verbosity::DebugVerbose;
use crate::command_line::{CommandLineArgs};
use std::collections::HashMap;

// Disable to get more accurate timestamps during debugging.
pub const ALLOW_PRINTING: bool = false;


/** A single program constant c in the source program corresponds to a family of constants c_i for synthesis.
  This data structure represents a single such c_i */
#[derive(Clone, Debug)]
pub struct SynthConst {
    c: String,
    i: usize,
}

impl SynthConst {
    pub fn pretty_string(&self) -> String {
        format!("{}-{}", self.c, self.i)
    }
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

impl SynthRecord {
    pub fn pretty_string(&self) -> String {
        if self.sl.is_empty() {
            return "Empty".to_string();
        }
        let mut acc = self.sl[0].pretty_string();
        for i in 1..self.sl.len() {
            acc = format!("{};{}", acc, self.sl[i].pretty_string())
        }
        acc
    }
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
  /** Used only for compositional synthesis problems. Records all components so far. */
  pub components: HashMap<String, SynthRecord>,
}

impl Synthesizer {
    fn do_print(&self) -> bool {
        ALLOW_PRINTING && self.ca.verbosity() == DebugVerbose
    }

    /** Pretty-print string for code */
    pub fn pretty_result(&self) -> String {
        match self.result.clone() {
            None => "None".to_string(),
            Some(res) => res.pretty_string(),
        }
    }
    
    /** Set  command line flags */
    pub fn set_command_line(&mut self, ca: &CommandLineArgs) -> () {
        self.ca = ca.clone();    
    }
    
    /** Initialize synthesizer to default status */
    pub fn default() -> Self {
        Synthesizer {ca: CommandLineArgs::DEFAULT, stack: vec![], result: None, components: HashMap::new()}
    } 

    /** Initialize synthesizer based on provided command line flags */
    pub fn of_command_line(ca: &CommandLineArgs) -> Self {
        let mut res = Self::default();
        res.set_command_line(ca);
        res
    }

    /** Start proof search */
    pub fn start(&mut self) -> () {
        if !self.ca.is_synthesizer_enabled() { return; }
        if self.do_print() { println!("TRACE: START"); }
        self.stack = vec![vec![SynthRecord{sl: vec![]}]];
    }
    
    /** Split into n branches for constant c
     * usize < 1 indicates branching that does not generate code, such as or-branching.
     */
    pub fn branch(&mut self, c: &String, n: usize) -> () {
        if !self.ca.is_synthesizer_enabled() { return; }
        if self.do_print() { println!("TRACE: BRANCH {}/{}", c, n); }
        if self.stack.is_empty() || self.stack.last().expect("NONEMPTY").is_empty() {
            if self.do_print() { println!("TRACE: STACK: {:?}", self.stack.clone()); }
            return;
        }
        /* Binary branching with no effect on program, just add 1 alternative */
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
        if self.do_print() { println!("TRACE: NEXT-START: {:?}", self.stack); }
        if self.stack.is_empty() {
          return;
        } else {
          loop {
            if self.stack.is_empty() || self.stack.last().expect("NONEMPTY").is_empty(){ return; }
            let mut alts = self.stack.pop().expect("NONEMPTY");
            let _alt = alts.remove(0);
            if !alts.is_empty() { self.stack.push(alts); break; }
          } 
        if self.do_print() { println!("TRACE: NEXT-END: {:?}", self.stack); }
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
        if self.do_print() { println!("TRACE: FINISH: {:?}", self.pretty_result()); }
    }

    /** Save current result as component, reset result and stack. */
    pub fn save_component(&mut self, other: &Synthesizer, name: &String) -> () {
        match &other.result {
            None => (),
            Some(v) => { 
                self.components.insert(name.clone(), v.clone()); self.result = None; self.stack = vec![];
            }
        }
    }

    /** Apply all current component definitions to the result. */
    pub fn apply_components(&mut self) -> () {
        match &self.result {
            None => (),
            Some(sr) => {
                let mut out = vec![];
                for sc in &sr.sl {
                    match self.components.get(&sc.c) {
                        None => {
                            out.push(sc.clone())
                        },
                        Some(repl) => {
                            let mut sr =  repl.sl.clone();
                            out.append(&mut sr)
                        },
                    }
                }
                self.result = Some(SynthRecord { sl: out })
            }
        }
    }
}