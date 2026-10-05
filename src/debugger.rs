/*! Stores debugging-related configuration and status, such as debug printing
  configuration flags and performance profiling statistics.
*/
use crate::command_line::{CommandLineArgs, Verbosity};
use std::time::{Instant,Duration};

#[derive(Clone, Debug)]
pub struct Debugger {
  /** Command-line arguments provided by the user, which may include debug flags. */
  ca: CommandLineArgs,
  /** Last time at which start_timer() method was called.
   
  Used for performance profiling */
  timer: Instant,
  /** Maximum number of steps before terminating execution early.

  This is used to help debug programs which fail to terminate in a reasonable time. */
  max_steps: i64,
  /** Steps elapsed since execution began. */
  current_steps: i64,
}

impl Debugger {
    /** If debugging flag is enabled, terminate after this many steps*/
    const DEFAULT_MAX_STEPS: i64 = 1_000_000_000_000_000;

    /** Initialize debugger based on provided command line flags */
    pub fn of_command_line(ca: &CommandLineArgs) -> Self {
        Debugger {ca: ca.clone(), timer: Instant::now(), 
            max_steps: Self::DEFAULT_MAX_STEPS, current_steps: 0}
    }

    /** Initialize debugger to default status */
    pub fn default() -> Self {
        Debugger {ca: CommandLineArgs::DEFAULT, timer: Instant::now(), 
            max_steps: Self::DEFAULT_MAX_STEPS, current_steps: 0}
    }

    /** Record the current time as a start time for profiling. */
    pub fn start_timer(&mut self) {
        self.timer = Instant::now();
    }

    /** Report time elapsed since timer started */
    pub fn elapsed_time(&self) -> Duration {
        Instant::now().duration_since(self.timer)
    }

    /** Report steps elapsed since creation */
    pub fn elapsed_steps(&self) -> i64 {
        self.current_steps
    }

    /** Record a step of execution. */
    pub fn step(&mut self) {
        self.current_steps = self.current_steps + 1;
    }

    /** Determine whether the debugging termination limit has been reached. */
    pub fn terminated(&self) -> bool {
        self.current_steps >= self.max_steps
    }

    /** The level of verbosity with which to print console output. */
    pub fn verbosity(&self) -> Verbosity {
        self.ca.verbosity()
    }
}