use crate::ast::Formula;
use crate::pdlp::dynamics::{Machine,Goal};
use crate::printer_common;
use std::collections::HashMap;

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

/** String representation of all formulas in given predicate map */
fn map_print(m: &HashMap<String, Vec<Formula>>) -> String {
    let mut s = "".to_string();
    let mut is_first_sym_pred: bool = true;
    for (_a, ps) in m {
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
    s
}

/** Prints the logic program stored in the given machine. */
pub fn machine_prog(m: &Machine) -> String {
  let mut s = "".to_string();
  for (c, a) in &m.sm.prog_defns {
    s.push_str(c);
    s.push_str(" ::= ");
    s.push_str(&printer_common::program(&a));
    s.push_str(".\n");
  }
  s.push_str(&format!("{} ATOMS: ", m.sm.atom_preds.len()));
  s.push_str(&map_print(&m.sm.atom_preds));
  s.push_str(&format!("{} BOXES: ", m.sm.box_preds.len()));
  s.push_str(&map_print(&m.sm.box_preds));
  s.push_str(&format!("{} DIAMONDS: ", m.sm.diamond_preds.len()));
  s.push_str(&map_print(&m.sm.diamond_preds));
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