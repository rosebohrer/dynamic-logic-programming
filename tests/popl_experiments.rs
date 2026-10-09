/* The experiments for the POPL2027 submission 
  Running:
    cargo test popl_experiments -- --test-threads=1 --show-output
*/
pub mod common;

use std::time::Duration;
use glp::examples;
use glp::frontends::graph::Graph;
use glp::frontends::guesser::Guesser;
use glp::statics_common;
use glp::{parser,command_line};
use command_line::CommandLineArgs;
use glp::pdlp::dynamics::{StaticMachine as PStaticMachine,Machine as PMachine};
use glp::ddlp::dynamics::{StaticMachine as DStaticMachine,Machine as DMachine};
use glp::pdlp::synthesizer::Synthesizer;
use common::Profile;
use glp::ast::{FormulaNode::*, ProgramNode::*, LogicProgram};

#[cfg(test)]
mod tests {
    use super::*;
    use glp::printer_common;
use parser::pdlp::logic_program as parselp;
    const REPETITIONS: i64 = 1;
    /* Enable synthesizer in the two-shot tests. Useful to disable this for performance profiling 
       because its performance impact is unclear. */
    const COMPOSITIONAL_SYNTH: bool = true;
    
    /** Run code and record how long it takes */
    fn pdlp_time_runs_of_all(machs: &mut Vec<PMachine>, is_quiet: bool) -> Profile {
        let mut prof = Profile::new();
        let mut debug = machs[0].dm.d.clone();
        for _i in 0..REPETITIONS {
            let mut dur : Duration = Duration::new(0,0);
            let mut steps = 0;
            for i in 0..machs.len() {
                let mut mach_start = machs[i].clone();
                debug.start_timer();
                mach_start.run();
                dur = dur + debug.elapsed_time();
                steps = steps + mach_start.dm.d.elapsed_steps();
                assert!(mach_start.is_proved());
                machs[i] = mach_start;
                
            }
            prof.add(steps, dur);
        }
        if !is_quiet {
            println!("Completed {} repetitions in time: {:?}", REPETITIONS, prof.avg_time());
            println!("Steps: {}", prof.steps);
        }
        prof
    }

    /** Run code and record how long it takes */
    fn pdlp_test_one(code: String, is_synth: bool) -> Profile {
        let mut dmachs : Vec<PMachine> = vec![];
        let lp_norm = statics_common::normalize(*parselp(&code.clone()).unwrap()).unwrap();
        let mut sm = PStaticMachine::new();
        let mut m = PMachine::of_lp(&mut sm, &lp_norm);
        if is_synth {
            m.set_command_line(&CommandLineArgs::SYNTH);
        } else {
            m.set_command_line(&CommandLineArgs::DEBUG);
        }
        dmachs.push(m);
        pdlp_time_runs_of_all(&mut dmachs, false)
    }

    fn find_sym_name(lp: &LogicProgram) -> String {
        match &lp.query.node {
            MDiamond(sym, _) => {  
                match &sym.node {
                    Symbol(sc) => sc.clone(),
                    _ => "N/A".to_string(),
                }},
            _ => "N/A".to_string(),
        }
     }

    /** Run exactly two programs, record how long they take. */
    fn pdlp_test_two(code1: String, code2: String) -> Profile {
        let mut dmachs : Vec<PMachine> = vec![];
        // Allow running without the compositional synthesizer so that we can assess whether there is any noticeable 
        // performance difference. Also this mode is more robust to different styles of 
        if !COMPOSITIONAL_SYNTH {
            // In this mode, simply parse the two LPs, create machines for them, and run the machines
            let lp_norm1 = statics_common::normalize(*parselp(&code1.clone()).unwrap()).unwrap();
            let lp_norm2 = statics_common::normalize(*parselp(&code2.clone()).unwrap()).unwrap();
            let mut sm1 = PStaticMachine::new();
            let mut m1 = PMachine::of_lp(&mut sm1, &lp_norm1);
            m1.set_command_line(&CommandLineArgs::DEBUG);
            let mut sm2 = PStaticMachine::new();
            let mut m2 = PMachine::of_lp(&mut sm2, &lp_norm2);
            m2.set_command_line(&CommandLineArgs::DEBUG);
            dmachs.push(m1); dmachs.push(m2);
            pdlp_time_runs_of_all(&mut dmachs, false)
        } else {
            // In compositional synthesis mode, split the lemma LP into all the lemmmas to be proved, prove each one, collect
            // their resulting programs as components in the synthesizer, then after running the final main LP, substitute in
            // the definitions of every component to get the final answer.
            let lp_norm1 = statics_common::normalize(*parselp(&code1.clone()).unwrap()).unwrap();
            let lp_norm2 = statics_common::normalize(*parselp(&code2.clone()).unwrap()).unwrap();
            let mut profs = vec![];
            // Break up the lemma by top-level conjunctions. Assume all components are &-separated.
            let conjs = statics_common::conjuncts(&*lp_norm1.query);
            let mut syn = Synthesizer::default();
            for i in 0..conjs.len() {
                let mut lp = lp_norm1.clone();
                lp.query = Box::new(conjs[i].clone()); 
                // Inspect the syntax of the formula to find the component name. Assume it's in a <> formula at top of component.
                let comp_name = find_sym_name(&lp);
                let mut sm1 = PStaticMachine::new();
                let mut m1 = PMachine::of_lp(&mut sm1, &lp);
                m1.set_command_line(&CommandLineArgs::SYNTH);
                let mut mv = vec![m1];
                profs.push(pdlp_time_runs_of_all(&mut mv, true)); 
                // Remember code synthesized for component
                syn.save_component(&mv[0].dm.syn, &comp_name);
            }
            let mut sm2 = PStaticMachine::new();
            let mut m2 = PMachine::of_lp(&mut sm2, &lp_norm2);
            m2.dm.syn = syn;
            m2.set_command_line(&CommandLineArgs::SYNTH); 
            let mut m2vec = vec![m2];
            let mut prof_final = pdlp_time_runs_of_all(&mut m2vec, true);
            assert!(m2vec[0].is_proved());
            // Plug in solutions of every component
            m2vec[0].dm.syn.apply_components();
            println!("COMPOSITE SYNTHESIS RESULT: {}", m2vec[0].dm.syn.pretty_result());
            // Add up costs of every interpreter invocation
            for i in 0..profs.len() {
                prof_final.add_single(&profs[i]);
            }
            println!("Completed {} repetitions in time: {:?}", REPETITIONS, prof_final.avg_time());
            println!("Steps: {}", prof_final.steps);
            prof_final
        }
    }

    /** Run code and record how long it takes */
    fn ddlp_time_runs_of_all(machs: &mut Vec<DMachine>) -> Profile {
        let mut prof = Profile::new();
        let mut debug = machs[0].dm.d.clone();
        for _i in 0..REPETITIONS {
            let mut dur : Duration = Duration::new(0,0);
            let mut steps = 0;
            for i in 0..machs.len() {
                let mut mach_start = machs[i].clone();
                debug.start_timer();
                mach_start.run();
                dur = dur + debug.elapsed_time();
                steps = steps + mach_start.dm.d.elapsed_steps();
                machs[i] = mach_start;
            }
            prof.add(steps, dur);
        }
        println!("Completed {} repetitions in time: {:?}", REPETITIONS, prof.avg_time());
        println!("Steps: {}", prof.steps);
        prof
    }

    /** Run code and record how long it takes */
    fn ddlp_test_one(code: String) -> Profile {
        let mut dmachs : Vec<DMachine> = vec![];
        let lp_norm = statics_common::normalize(*parselp(&code.clone()).unwrap()).unwrap();
        let mut sm = DStaticMachine::new();
        let mut m = DMachine::of_lp(&mut sm, &lp_norm);
        m.set_command_line(&CommandLineArgs::DEBUG);
        dmachs.push(m);
        ddlp_time_runs_of_all(&mut dmachs)
    }

    /* Currently unused: assert example proves but do not record statistics */
    fn _pdlp_assert_code_proves(lp_code: String)  {
        let lp_norm = statics_common::normalize(*parselp(&lp_code.clone()).unwrap()).unwrap();
        let mut sm = PStaticMachine::new();
        let mut lp_mach = PMachine::of_lp(&mut sm, &lp_norm);
        lp_mach.run();
        assert!(lp_mach.is_proved());
    }

    /* Currently unused: assert example proves but do not record statistics */
    fn _ddlp_assert_code_proves(lp_code: String) {
        let lp_norm = statics_common::normalize(*parselp(&lp_code.clone()).unwrap()).unwrap();
        let mut sm = DStaticMachine::new();
        let mut lp_mach = DMachine::of_lp(&mut sm, &lp_norm);
        lp_mach.run();
        assert!(lp_mach.is_proved());
    }
   
    /** Format profile for printing */
    fn prof_str(prof: &Profile) -> String {
        format!(",{},{}",prof.steps,prof.avg_time().as_millis())
    }

    /** Print entire table of POPL submission experiment results */
    fn report_experiments(misc_labels: Vec<String>, misc_profs: Vec<Profile>, 
        ddlp_peg_sizes: Vec<usize>, ddlp_peg_profs: Vec<Profile>,
        pdlp_peg_sizes: Vec<usize>, pdlp_peg_profs: Vec<Profile>,
        os_sizes: Vec<usize>, os_profs: Vec<Profile>,
        ts_sizes: Vec<usize>, ts_profs: Vec<Profile>) {
        // Assertions about correctness of various vectors
        assert_eq!(misc_labels.len(), misc_profs.len());
        assert_eq!(ddlp_peg_sizes.len(), ddlp_peg_profs.len());
        assert_eq!(pdlp_peg_sizes.len(), pdlp_peg_profs.len());
        assert_eq!(os_sizes.len(), os_profs.len());
        assert_eq!(ts_sizes.len(), ts_profs.len());
        assert!(ddlp_peg_sizes.len() <= pdlp_peg_sizes.len());
        for i in 0..ddlp_peg_sizes.len() {
            assert_eq!(ddlp_peg_sizes[i], pdlp_peg_sizes[i]);
        }
        assert!(os_sizes.len() <= ts_sizes.len());
        for i in 0..os_sizes.len() {
            assert_eq!(os_sizes[i], ts_sizes[i]);
        }
        // Start of function body
        for i in 0..misc_labels.len() {
            println!("{}{}", misc_labels[i], prof_str(&misc_profs[i]));
        }
        println!(",,");
        for i in 0..ddlp_peg_sizes.len() {
            println!("PEG{}{}{}", ddlp_peg_sizes[i], prof_str(&ddlp_peg_profs[i]), prof_str(&pdlp_peg_profs[i]));
        }
        for i in ddlp_peg_sizes.len()..pdlp_peg_sizes.len() {
            println!("PEG{},,{}", pdlp_peg_sizes[i], prof_str(&pdlp_peg_profs[i]));
        }
        println!(",,,,");
        for i in 0..os_sizes.len() {
            println!("G{}{}{}", os_sizes[i], prof_str(&os_profs[i]), prof_str(&ts_profs[i]));
        }
        for i in os_sizes.len()..ts_sizes.len() {
            println!("G{},,{}", ts_sizes[i], prof_str(&ts_profs[i]));
        }
    }

    /* Complete evaluation suite */
    #[test]
    pub fn popl_experiments() {
        /* TESTING MISC  */
        let misc_labels: Vec<String> = vec!["exdfa".to_string(), "exnfa".to_string(), "expeg".to_string(),
          "1count".to_string(), "2count".to_string(), "nim33".to_string()];
        let mut misc_profiles : Vec<Profile> = vec![];
        misc_profiles.push(pdlp_test_one(examples::POPL_DFA.to_string(), false));
        misc_profiles.push(pdlp_test_one(examples::POPL_NFA.to_string(), false));
        misc_profiles.push(pdlp_test_one(examples::POPL_PEG.to_string(), false));
        misc_profiles.push(pdlp_test_one(examples::ONE_COUNTER_CONJ.to_string(), false));
        misc_profiles.push(pdlp_test_one(examples::TWO_COUNTERS.to_string(), false));
        misc_profiles.push(pdlp_test_one(examples::NIM_THREE_THREE.to_string(), false));
        
        /* TESTING PEGS */
        let ddlp_peg_sizes = vec![/*4*/];
        let mut ddlp_peg_profiles : Vec<Profile> = vec![];
        for size in &ddlp_peg_sizes {
            let source = Graph::cycle(*size).to_full_ddlp_source();
            ddlp_peg_profiles.push(ddlp_test_one(source));
        }
        let pdlp_peg_sizes = vec![/*4,5,6,7,8*/];
        let mut pdlp_peg_profiles : Vec<Profile> = vec![];
        for size in &pdlp_peg_sizes {
            let source = Graph::cycle(*size).to_full_pdlp_source();
            pdlp_peg_profiles.push(pdlp_test_one(source, false));
        }

        // Max size 19 optimal for 10-minute maximum - 20 is just over 10 minutes
        /*  TESTING COUNTERS */
        let os_sizes = vec![/*1,2,*/3/* ,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19*/];
        let mut os_profs : Vec<Profile> = vec![];
        for size in &os_sizes {
            let g = Guesser::of_size(*size);
            let source = g.to_source_single();
            os_profs.push(pdlp_test_one(source, true));
        }

        // Max size 77 is optimal for 10-minute maximum, 78 is just over
        let ts_sizes = vec![/*1,2,*/3/*,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,40,80,120,160,200,240,280,320,360,400*/];
        let mut ts_profs : Vec<Profile> = vec![];
        for size in &ts_sizes {
            let g = Guesser::of_size(*size);
            let source1 = g.to_source_lemmas();
            let source2 = g.to_source_combiner();
            ts_profs.push(pdlp_test_two(source1, source2));
        }
        report_experiments(misc_labels,misc_profiles,ddlp_peg_sizes,ddlp_peg_profiles,
          pdlp_peg_sizes,pdlp_peg_profiles,os_sizes,os_profs,ts_sizes,ts_profs);
    }
}