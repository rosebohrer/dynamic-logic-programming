/*! Execute logic programs.

The core data structure Machine captures a logic program and its runtime state.
The Goal data structure is used within a Machine to store a formula in a
convenient normal form. The essential methods are the constructor Machine::of_lp
and the execution method Machine::run().

The efficiency of the proof search algorithm in Machine::run() is central to the
success of the language as a whole. We use several heuristics to promote adequate
runtime performance. We distinguish invertible rules that have no effect on provability
and apply such rules first, so their proof effort is not duplicated in the event of 
branching. Non-branching rules are then prioritized over branching. Appling rules 
under modalities is essential for completeness, but is only considered when no other 
options are present, to minimize branching factor. Predicate definitions are organized 
in hashmaps for efficient lookup of the maching clause, as opposed to attempting unification
for all rules present. 
*/

use crate::ast::{Formula,Program,FormulaNode,ProgramNode,DefnNode,LogicProgram,Defn};
use crate::ast::respan as respan;
use crate::ddlp::statics;
use crate::ddlp::printer;
use crate::command_line::CommandLineArgs;
use crate::debugger::Debugger;
use crate::ast::{Span,Spanned};
use FormulaNode::*; use ProgramNode::*; use DefnNode::*;
use std::collections::HashMap;
use crate::statics_common;

/** A normal-form (sub)goal to be solved.
Normal form is A1 & ... & AN -> G for goal formula G and clause formulas Ai.
So explicitly separate out Ai's and G. 
No guarantee is made on the order of assumptions in the vector.
They may be reversed, e.g., for performance.
*/
#[derive(Clone,PartialEq,Debug)]
pub struct Goal {
    pub assumps: Vec<Formula>,
    pub concl: Formula,
}

impl Goal {
  /** Initial goal in empty machine to distinguish it from proved machine. */
  pub const INIT: Self = Goal { assumps: vec![], concl: Spanned { node: True(), span: Span::DEFAULT }};

  /** Convert a formula to a goal */
  pub fn of_formula(fml: &Formula) -> Self {
      if let Imply(p, q) = &fml.node {
          let Goal { mut assumps, concl } = Self::of_formula(&q);
          assumps.insert(0,*p.clone());
          Goal { assumps, concl }
      } else { Goal { assumps: vec![], concl: fml.clone() } }
  }

  /** Drop modality of conclusion */
  pub fn unbox_concl(&mut self) {
    match &self.concl.node {
      MBox(_, p) => { self.concl = *p.clone(); },
      _ => (),
    }
  }
}


/** The static part of a machine. See documentation of each field. */
#[derive(Clone,Debug)]
pub struct StaticMachine {
  ////// Static components - do not change at runtime
    /** Represents all explicitly-defined programs c ::= a as a map of c -> a */
    pub prog_defns: HashMap<String, Program>,
    /** Represents all predicates whose heads are atoms. 
    letting p be an atom with clauses <q_i>, the map stores all p -> <q_i> */
    pub atom_preds: HashMap<String, Vec<Formula>>,
    /** Represents all predicates whose heads are box formulas.
    Letting head [c]p_i be defined by clauses q_ij, the representation is a 
    nested map c -> p_i -> <q_ij>. 
    A given box predicate has a single c, possibly (usually) with multiple p_i. */
    pub symbol_preds: HashMap<String, HashMap<String, Vec<Formula>>>,
}

impl StaticMachine {
  /** Create new empty static machine */
  pub fn new() -> StaticMachine {
    let prog_defns = HashMap::new();
    let atom_preds = HashMap::new();
    let symbol_preds = HashMap::new();
    StaticMachine { prog_defns, atom_preds, symbol_preds }    
  }

  /** Add a definition to a machine */
  pub fn define(&mut self, d: &Defn) {
    match &d.node {
      ProgDefn(c, a) => {self.prog_defns.insert(c.to_string(), *a.clone()); ()},
      PredDefn(clauses) if statics::is_atom(&statics_common::conclusion(&clauses[0])) => {
            let Pred(p) = &statics_common::conclusion(&clauses[0]).node else {panic!("Atom not predicate")} ; 
            self.atom_preds.insert(p.clone(), clauses.clone());
            ()
         },
        // Predicates that define a boxed formula
      PredDefn(clauses) => {
          let mut inner_map: HashMap<String, Vec<Formula>>= HashMap::new();
          for clause in clauses {
              if let MBox(_,fml) = statics_common::conclusion(clause).node {
                  if let Pred(p) = fml.node {
                      // If head already map, add clause to vector, else insert single clause
                      inner_map.entry(p.to_string())
                        .and_modify(|acc| acc.push(clause.clone()))
                        .or_insert(vec![clause.clone()]);
                  } else {()} // should never occur for well-formed lp
              } else {()} // should never occur for well-formed lp
              
          }
          let key: String = 
              if let MBox(prog, _) = statics_common::conclusion(&clauses[0]).node {
                  if let Symbol(c) = prog.node {
                      c
                  } else { "IMPOSSIBLE".to_string() }
              } else { "IMPOSSIBLE".to_string() };
          self.symbol_preds.insert(key, inner_map);
          ()
      },
      // VarDefn() is only available in PDLP, safe to ignore in DDLP
      VarDefn(_, _) => {},
    } 
  }
}

#[derive(Clone,Debug)]
pub struct DynamicMachine {
    ////// Dynamic components - change at runtime
    /** Remember debug print level, step count, etc. */
    pub d: Debugger,
    /** The (sub)goals remaining to be solved. Search proceeds left-to-right.
      A new machine is represented by the single goal True. 
      A proved machine is represented by the empty goal vector. */
    pub goals: Vec<Goal>,
    /** Stack for backtracking proof search. Each entry in the outermost vector corresponds to a point
    where branching occurs in the search. The entry contains all remaining alternatives at that point in
    the search. Each alternative is a vector of all subgoals at that moment. */
    pub stack: Vec<Vec<Vec<Goal>>>,
    /** Stack of modalities under which we are searching for rules to apply. Proof search begins from top-level 
    operator downward, but the ability to apply rules under a modality is necessary for completeness.
    In programs containing composition, we frequently must simplify the inner program before the outer. 
    For example, in proof search on the formula [a][b]P, we set modalities is vec![a], and 
    the goal to [b]P so that rules targeting [b]P may be applied. */
    pub modalities: Vec<Program>,
}

impl DynamicMachine {
  pub fn new() -> Self {
    let d = Debugger::default();
    let goals = vec![Goal::INIT]; // Non-empty so that is_proved() = false
    let stack = vec![];
    let modalities = vec![];
    DynamicMachine {d, goals, stack, modalities}
  }
}


/** The runtime configuration of a logic program. See documentation of each field. */
#[derive(Debug)]
pub struct Machine<'a> {
    pub sm: &'a StaticMachine,
    pub dm: DynamicMachine,
}

impl<'a> Machine<'a> {
  /** Don't deep-copy the program part, just the dynamic part */
  pub fn clone(self: &mut Machine<'a>) -> Machine<'a> {
    let sm = &self.sm;
    let dm = self.dm.clone();
    Machine { sm, dm }
  }

  /** Add a query to a machine as a new subgoal. */
  pub fn inquire(&mut self, f: &Formula) {
    // Special case: if we started with singleton goal True() for empty machine, overwrite. 
    if self.dm.goals.len() == 1 && self.dm.goals[0] == Goal::INIT {
      self.dm.goals[0] = Goal::of_formula(f);
    } else {
      self.dm.goals.push(Goal::of_formula(f));
    }
  }
  
  /** Load static machine */
  pub fn set_static(&mut self, sm: &'a StaticMachine) {
    self.sm = sm;
  }

  /** Remember the command line arguments. */
  pub fn set_command_line(&mut self, ca: &CommandLineArgs) {
    self.dm.d = Debugger::of_command_line(ca);
  }

  /** Create an empty machine.
  
  Mainly used in interactive mode where there are initially no definitions or goals.
  Machine::of_lp is recommended when running a known program.
  */
  pub fn new(sm: &'a StaticMachine) -> Self {
    Machine { sm,  dm: DynamicMachine::new() }
  }

  /** Assumes well-formed logic program */
  pub fn of_lp(sm: &'a mut StaticMachine, lp: &LogicProgram) -> Self {
    for defn in &lp.body {
      sm.define(defn);
    }
    let mut m = Self::new(sm);
    m.inquire(&lp.query);
    m
  }

  /** Replace assumption i of goal g with vector of assumptions */
  fn splice_assumps(&self, g: &Goal, i: usize, mut insert_assumps: Vec<Formula>) -> Goal {
    let mut assumps: Vec<Formula> = vec![];
    for j in 0..i {
      assumps.push(g.assumps[j].clone());
    }
    assumps.append(&mut insert_assumps);
    for j in i+1..g.assumps.len() {
      assumps.push(g.assumps[j].clone());
    }
    Goal { assumps, concl: g.concl.clone()}
  }

  /** Whether rules are being applied at formula's top-level vs. under a modality */
  fn is_top_level(&self) -> bool {
    self.dm.modalities.is_empty()
  }

  /** Wrap a formula in the modalities of the current machine */
  fn modalize(&self, mut f: Formula) -> Formula {
    let s = f.span;
    for i in (0..self.dm.modalities.len()).rev() {
      f = respan(s, MBox(Box::new(self.dm.modalities[i].clone()), Box::new(f)));
    }
    f
  }
  
  /** Compute lossless steps applicable to given assumption of a goal. */
  fn left_steps_at_assump(&self, close: &mut Vec<Vec<Goal>>, lossless: &mut Vec<Vec<Goal>>, lossy: &mut Vec<Vec<Goal>>, i: usize, j: usize) {
    let g = &self.dm.goals[i];
    // Hypothesis rule
    if self.is_top_level() && g.assumps.contains(&g.concl) {
      close.push(vec![]);
      return;
    }
    match &g.assumps[j].node {
      And(l, r) => {lossless.push(vec![self.splice_assumps(&g, j, vec![*l.clone(),*r.clone()])]); return;},
      Imply(l, r) => {
        let uses = self.splice_assumps(&g, j, vec![*r.clone()]);
        let mut shows = self.splice_assumps(&g, j, vec![]);
        shows = Goal { assumps: shows.assumps, concl: *l.clone()};
        lossy.push(vec![shows, uses])
      },
      MBox(a, p) => {
        match &a.node {
          Choice(l, r) => {
            let (sl, sr) = (l.span, r.span);
            lossless.push(vec![self.splice_assumps(&g, j, vec![respan(sl,MBox(l.clone(), p.clone())), 
                                                               respan(sr,MBox(r.clone(), p.clone()))])]); 
            return;
          },
          Test(q) => {
            let s = g.assumps[j].span;
            lossless.push(vec![self.splice_assumps(&g, j, vec![respan(s, Imply(q.clone(),p.clone()))])]); 
            return;
          },
          _ => (),
        }
      }
      _ => (),
    }
  }
  
  /** Compute steps applicable to any assumption of a goal. */
  fn left_steps_at_goal(&self, close: &mut Vec<Vec<Goal>>, lossless: &mut Vec<Vec<Goal>>, lossy: &mut Vec<Vec<Goal>>, i: usize) {
    let assumps = &self.dm.goals[i].assumps;
    for j in 0..assumps.len() {
      self.left_steps_at_assump(close, lossless, lossy, i, j);
      if !close.is_empty() || !lossless.is_empty() {
        return;
      }
    }
  }
  
  /** Implement expansion of explicit program definitions. */
  fn prog_defn_case(&self, lossless: &mut Vec<Vec<Goal>>, g: &Goal, c: &String, p: Formula) {
    match self.sm.prog_defns.get(c) {
      Some(defn) => lossless.push(vec![Goal { assumps: g.assumps.clone(), concl: respan(defn.span, MBox(Box::new(defn.clone()), Box::new(p)))}]),
      None => (),
    }
  }
  
  /** If symbol is defined as box predicate with given postcondition, count branches. Else 0 */
  fn symbol_pred_arity(&self, symbol: &String, post: &String) -> usize {
    if self.sm.symbol_preds.contains_key(symbol) && self.sm.symbol_preds[symbol].contains_key(post) {
      self.sm.symbol_preds[symbol][post].len()
    } else {
      0
    }
  }
  
  /** Implement invocation of symbol predicates. */
  fn symbol_pred_case(&self, out: &mut Vec<Vec<Goal>>, g: &Goal, symbol: &String, post: &String) {
    let clauses = &self.sm.symbol_preds[symbol][post];
    for clause in clauses {
      let mut vec: Vec<Goal> = vec![];
      let assumps = statics_common::assumptions(&clause);
      for assump in assumps {
        vec.push(Goal {assumps: g.assumps.clone(), concl: self.modalize(assump.clone())});
      }
      out.push(vec)
    }
  }
  
  /** If string is defined as an atom predicate, count branches. Else 0. */
  fn atom_pred_arity(&self, p: &String) -> usize {
    match self.sm.atom_preds.get(p) {
      Some(defn) => defn.len(),
      _ => 0,
    }
  }
  
  /** Implement invocation of atom predicates */
  fn atom_pred_case(&self, out: &mut Vec<Vec<Goal>>, g: &Goal, p: &String) {
    match self.sm.atom_preds.get(p) {
      Some(defn) => {
        for clause in defn {
          let mut vec: Vec<Goal> = vec![];
          let assumps = statics_common::assumptions(&clause);
          for assump in assumps {
            vec.push(Goal {assumps: g.assumps.clone(), concl: self.modalize(assump.clone())});
          }
          out.push(vec)
        }
      },
      None => (),
    }
  }

  // @TODO: Better name, better efficiency perhaps
  /** Remove outermost modality from conclusion of given goal.*/
  fn step_right_in(&mut self, i: usize)  {
    self.dm.goals[i].unbox_concl();
  }

  /** Lossless steps applicable to conclusion of given goal. */
  fn right_steps_at_goal(&mut self, close: &mut Vec<Vec<Goal>>, lossless: &mut Vec<Vec<Goal>>, lossy: &mut Vec<Vec<Goal>>, i: usize) {
    let tl = self.is_top_level();
    let g = &self.dm.goals[i];
    match &g.concl.node {
      MBox(prog, p) => {
        match &prog.node {
          Seq(a, b) => {
            let (s1, s2) = (a.span, b.span);
            lossless.push(vec![Goal { assumps: g.assumps.clone(), concl: self.modalize(respan(s1, MBox(a.clone(), Box::new(respan(s2, MBox(b.clone(), p.clone()))))))}])
          },
          Choice(a, b) => {
            let (s1, s2) = (a.span, b.span);
            lossless.push(vec![Goal { assumps: g.assumps.clone(), concl: self.modalize(respan(s1, MBox(a.clone(), p.clone())))}
                             , Goal { assumps: g.assumps.clone(), concl: self.modalize(respan(s2, MBox(b.clone(), p.clone())))}]);
          },
          Test(q) if tl => {
            /*  Although we could jump right to making an assumption, we instead create an implication so that
             we better match the left rule, where an implication is the more efficient choice */
            lossless.push(vec![Goal {assumps: g.assumps.clone(), concl: respan(g.concl.span, Imply(q.clone(), p.clone()))}]);
          },
          Loop(a, inv) if tl => {
            let invs = statics_common::disjuncts(&inv);
            let mut preserves: Vec<Goal> = vec![];
            let mut posts: Vec<Goal> = vec![];
            let mut all_goals: Vec<Goal> = vec![];
            for j in invs {
            /*pub fn respan<T>(sp: Span, t: T) -> Spanned<T> {
                Spanned { node: t, span: sp } } */
              preserves.push(Goal {assumps: vec![j.clone()], concl: respan(g.concl.span,MBox(a.clone(), inv.clone())) });
              posts.push(Goal {assumps: vec![j], concl: *p.clone() });
            }
            let pre: Goal = Goal { assumps: g.assumps.clone(), concl: *inv.clone()};
            all_goals.push(pre); all_goals.append(&mut preserves); all_goals.append(&mut posts);
            lossless.push(all_goals);
          },
          Symbol(c) => {
            if let Pred(d) = &p.node {
              match self.symbol_pred_arity(&c, &d) {
                1 => self.symbol_pred_case(lossless, &g, &c, &d),
                0 => self.prog_defn_case(lossless, &g, &c, *p.clone()),
                _ => self.symbol_pred_case(lossy, &g, &c.clone(), &d.clone()),
              }
            } else { self.prog_defn_case(lossless, &g, &c, *p.clone()) }
          },
          _ => (),
        }
        // Only search under box if other options fail.
        if lossless.is_empty() && lossy.is_empty() {
          self.dm.modalities.push(*prog.clone());
          self.step_right_in(i);
          self.right_steps_at_goal(close, lossless, lossy, i);
          self.dm.modalities.pop();
        }
      },
      And(p, q) => lossless.push(vec![Goal { assumps: g.assumps.clone(), concl: self.modalize(*p.clone())},
                             Goal { assumps: g.assumps.clone(), concl: self.modalize(*q.clone())}]),
      Imply(p, q) if tl => {
        // @TODO: Attempt to remove clone.
        let mut assumps = g.assumps.clone();
        assumps.push(*p.clone());
        lossless.push(vec![Goal { assumps, concl: *q.clone() }]);},
      Pred(p) => {
        match self.atom_pred_arity(&p) {
          1 => self.atom_pred_case(lossless, &g, &p),
          0 => (),
          _ => self.atom_pred_case(lossy, &g, &p.clone()),
        }},
      Or(p, q) => {
        lossy.push(vec![Goal { assumps: g.assumps.clone(), concl: self.modalize(*p.clone())}]);
        lossy.push(vec![Goal { assumps: g.assumps.clone(), concl: self.modalize(*q.clone())}]);
      },
      // Sound even when not top-level, [a]true is an axiom.
      True() => close.push(vec![]),
      _ => (),
    }
  }
  
  /** All steps applicable to given goal.

  Returns a nested vector <v_i> of successors to goal g_j.
  Each step replaces the single goal g_j by all of v_i.
  For example, v_i = <> represents closing a goal,
   v_i = <g_j'> represents replacing g_j by g_j', and
   v_i = <g_1, g_2> replaces g_j by two goals g_1 and g_2.
 */
  fn steps_at_goal(&mut self, i: usize) -> Vec<Vec<Goal>>{
    let mut closing_steps = vec![];
    let mut lossless_steps = vec![];
    let mut lossy_steps = vec![];
    self.left_steps_at_goal(&mut closing_steps, &mut lossless_steps, &mut  lossy_steps, i);
    self.right_steps_at_goal(&mut closing_steps, &mut lossless_steps, &mut  lossy_steps, i);
    if !closing_steps.is_empty() {
      return closing_steps;
    } else if !lossless_steps.is_empty() {
      return lossless_steps;
    } else {
      return lossy_steps;
    }
  }

  /** Replace goal i with goal vector. */
  fn splice_goals(&mut self, i: usize, insert_goals: Vec<Goal>) -> Self {
    let mut new_goals: Vec<Goal> = vec![];
    let Machine { sm, dm } = self.clone();
    let DynamicMachine {d, goals, stack, modalities} = dm;
    for j in 0..i {
        new_goals.push(goals[j].clone());
    }
    new_goals.append(&mut insert_goals.clone());
    for j in i+1..goals.len() {
        new_goals.push(goals[j].clone());
    }
    Machine { sm, dm: DynamicMachine {d, goals: new_goals, stack, modalities} }
  }
  
  /** Given a machine, what are all possible machines it can step to? */
  pub fn steps(&mut self) -> Vec<Self> {
    let mut successors: Vec<Self> = vec![];
    if self.dm.goals.is_empty() {
      return successors;
    }
        
    /* Enforce left-to-right execution order. If the first goal is stuck, the entire
     * proof is stuck and it's better to discover early. */
    let goal_vecs = self.steps_at_goal(0);
    for goal_vec in &goal_vecs {
      let new_mach = self.splice_goals(0, goal_vec.to_vec());
      successors.push(new_mach);
    }
    successors
  }

  /** Whether the machine has succeeded in proving its goal.
  
  Note that this method returns true upon creating an empty machine with 
  the new() constructor because no goal has been set. 
  */
  pub fn is_proved(&self) -> bool {
    self.dm.goals.len() == 0
  }
  
  /** Whether machine has gotten stuck during search and failed to prove. */
  pub fn is_stuck(&mut self) -> bool {
    self.dm.goals.len() != 0 && self.dm.stack.len() == 0 && self.steps().len() == 0
  }

  /** Perform proof search. */
  pub fn run(&mut self)  {
    loop {
      if self.dm.d.verbosity().is_debug() {
        //println!("{}", printer::machine(self));
        self.dm.d.step();
      }
      if self.dm.d.terminated() {
        return;
      }
      if self.is_proved() {
        return;
      }
      let mut succs = self.steps();
      if succs.len() == 1 {
        *self = succs.remove(0);
      } else if succs.len() > 1 {
        // removes first element in place.
        *self = succs.remove(0);
        let mut alts = vec![];
        for succ in succs {
          alts.push(succ.dm.goals);
        }
        self.dm.stack.push(alts);
      } else {
        while !self.dm.stack.is_empty() && self.dm.stack.last().expect("NONEMPTY").is_empty() {
          self.dm.stack.pop();
        }
        if self.dm.stack.is_empty() {
          return;
        } else {
          let mut alts = self.dm.stack.pop().expect("NONEMPTY");
          let alt = alts.remove(0);
          self.dm.goals = alt;
          self.dm.stack.push(alts);
        }
      }
    }
  }
}