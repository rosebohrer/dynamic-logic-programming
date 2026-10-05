/** Record the time taken by repeated execution tests. This is a basic performance tester meant
 * for assessing the impact of optimizations, and should not be confused with the POPL benchmarks.
 */
pub mod common;

use glp::{parser,examples,command_line};
use command_line::CommandLineArgs;
use glp::ddlp::dynamics;
use dynamics::{StaticMachine,Machine};

#[cfg(test)]
mod tests {
    use super::*;
    use parser::pdlp::logic_program as parselp;
                    
    const REPETITIONS: i64 = 1;

    /** Repeatedly run pursuit-evasion game from FLOPS2026 paper */
    #[test]
    fn profile_paper_peg() {                              
        let lp_paper_peg = parselp(examples::FLOPS_PEG).unwrap();
        let mut sm = StaticMachine::new();
        let mut m = Machine::of_lp(&mut sm, &lp_paper_peg);
        m.set_command_line(&CommandLineArgs::DEFAULT);
        let mut mach_start = m.clone();
        mach_start.dm.d.start_timer();
        for _i in 0..REPETITIONS {
            m = mach_start.clone();
            m.run();
        }
        let dur = mach_start.dm.d.elapsed_time();
        println!("Completed {} repetitions in time: {:?}", REPETITIONS, dur);
        println!("Steps: {}", m.dm.d.elapsed_steps());
    }
}