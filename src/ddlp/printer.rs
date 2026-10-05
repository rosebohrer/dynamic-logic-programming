use crate::ddlp::dynamics::{Machine,Goal};
use crate::printer_common;

/** How many stack frames are printed at most  when printing a machine. */
const MAX_FRAMES: i64 = 5;
/** Whether the stack is printed at all when printing a machine. */
const SHOW_STACK: bool = false;

/** Pretty-print a goal, e.g., from a machine. 

Because goals are part of the runtime state rather than the source code, they
are not meant to be parsed and thus their pretty-printing syntax is arbitrary
*/
pub fn goal(g: &Goal) -> String {
  let mut s = "".to_string();
  for f in &g.assumps {
    s.push_str(&printer_common::formula(&f));
    s.push_str(",");
  }
  s.push_str("|- ");
  s.push_str(&printer_common::formula(&g.concl));
  s
}

//@TODO: Revise the two printing functions for machines.
/** Prints the logic program stored in the given machine. */
pub fn machine_prog(m: &Machine) -> String {
  let mut s = "".to_string();
  for (c, a) in &m.sm.prog_defns {
    s.push_str(c);
    s.push_str(" ::= ");
    s.push_str(&printer_common::program(&a));
    s.push_str(".\n");
  }
  for (_p, fmls) in &m.sm.atom_preds {
    for i in 0..(fmls.len()-1) {
      s.push_str(&printer_common::formula(&fmls[i]));
      s.push_str(",\n");
    }
    s.push_str(&printer_common::formula(&fmls[fmls.len()-1]));
    s.push_str(".\n\n");
  }
  for (_c, map) in &m.sm.symbol_preds {
    let mut is_first_sym_pred: bool = true;
    for (_a, ps) in map {
      for p in ps {
        if is_first_sym_pred {
          is_first_sym_pred = false;
        } else {
          s.push_str(", ");
        }
        s.push_str(&printer_common::formula(&p));
      }
    }
    s.push_str(".\n\n");
  }
  s
}

/** Prints the runtime state of a machine.

The logic program associated to the machine is not printed.
*/
pub fn machine(m: &Machine) -> String {
  let mut s = "".to_string();
  let mut frame_count = 0;
  s.push_str("\nGOALS: ==========================\n");
  for g in &m.dm.goals {
    s.push_str(&goal(&g));
    s.push_str("\n");
  }
  if SHOW_STACK {
    s.push_str("\nSTACK:\n");
    for frame in &m.dm.stack {
      if frame_count >= MAX_FRAMES {
        break;
      }
      if !frame.is_empty() {
        s.push_str("FRAME =============================\n");
        frame_count = frame_count + 1;
      }
      for alt in frame {
        s.push_str("ALT -------------");
        for g in alt {
          s.push_str(&goal(&g));
          s.push_str("\n");
        }
      }
    }
  }
  s
}