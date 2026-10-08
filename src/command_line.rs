/*! Command-line argument data structure and parser.

The CommandLineArgs structure captures all command-line arguments.
Use CommandLineArgs::from_env() to read and parse all arguments. This operation is 
expensive, so its result should be saved and reused as necessary. Accessor functions
like verbosity() should be used instead of direct field access because they
automatically handle different combinations of flags that mean the same thing.
See the usage message HELP for explanation of each flag's purpose.

The pico_args crate is used for parsing. Our argument parsing needs are simple, so
a simple argument parsing crate is preferred.
*/
use std::ffi::os_str::OsString;

/** Usage message displayed to end-users.

  Describes how each command-line argument is used. The tool name used in this
  message is not final and is expected to change.
 */
pub const HELP: &str = "\
pdlp - Propositional Dynamic Logic Programming implementation

USAGE:
  pdlp [FLAGS] [FILES]

FLAGS:
  -h, --help            Prints this help information
  -v, --verbose         Prints verbose execution information
  -d, --debug           Prints extra verbose debug information (overrides -v)
  -i, --interactive     Write dollop code interactive in a REPL. (ignores <FILES>)

ARGS:
  <FILES>              A list of files to be executed sequentially in batch mode
";

/** Specifies how much output text to produce.

NonVerbose is the default setting and should focus on printing final results
rather than showing how the results are achieved. Verbose is intended for programmers
to debug programs written in the language. Output should be detailed enough to understand
the flow of execution, but self-descriptive enough that it is understood without a knowledge
of implementation internals. DebugVerbose is intended for debugging of the implementation
itself, and output can freely refer to implementation internals.
*/
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Verbosity {
    NonVerbose,
    Verbose,
    DebugVerbose,
}

impl Verbosity {
    /** Determines whether verbose-level messages should be printed */
    pub fn is_verbose(&self) -> bool {
        *self != Self::NonVerbose
    }
    /** Determines whether debug-level messages should be printed */
    pub fn is_debug(&self) -> bool {
        *self == Self::DebugVerbose
    }
}

/** Structure containing all command-line arguments.

The help flag prints a usage message and exits. The verbose and debug flags are
used to set the verbosity level; if debug is set, the verbose flag is irrelevant.
The interactive flag starts a REPL for user interaction. The input_files, if 
non-empty, are run sequentially in batch-mode before exiting.
The synthesize flag, intended to be used in batch mode, generates a program which 
satisfies the specification given by the query.

If both interactive and input_files are specified, the input_files are ignored.
If input_files are empty, interactive is assumed by default. Thus the interactive
flag is not stricted needed, and serves only to improve clarity.
*/
#[derive(Clone, Debug)]
pub struct CommandLineArgs {
    pub help: bool,
    verbose: bool,
    debug: bool,
    interactive: bool,
    synthesize: bool,
    pub input_files: Vec<OsString>,
}

impl CommandLineArgs {
    /** Reasonable default arguments, used to initialize data structures before 
    arguments are read dynamically from environment */
    pub const DEFAULT: Self = CommandLineArgs { 
        help: false, verbose: false, debug: false, interactive: true, synthesize: false, input_files: vec![] 
    }; 

    /** Arguments appropriate for test cases that require debugger functionality */
    pub const DEBUG: CommandLineArgs = CommandLineArgs { 
        help: false, verbose: true, debug: true, interactive: false, synthesize: false, input_files: vec![]
    };

    /** Read and parse all arguments from environment. Expensive. */
    pub fn from_env() -> Self {
        let mut pargs = pico_args::Arguments::from_env();    
        let help = pargs.contains(["-h", "--help"]);
        let verbose = pargs.contains(["-v", "--verbose"]);
        let debug = pargs.contains(["-d", "--debug"]);
        let synthesize = pargs.contains(["-s", "--synthesize"]);
        let mut interactive = pargs.contains(["-i", "--interactive"]);
        let input_files: Vec<OsString> = pargs.finish();
        // For usability: if no input given, assume the programmer wants interactive
        if input_files.is_empty() {
            interactive = true;
        }
        CommandLineArgs {help, verbose, debug, interactive, input_files, synthesize}
    }
    
    /** Determine whether to use synthesizer */
    pub fn is_synthesizer_enabled(&self) -> bool {
        self.synthesize
    }

    /** Determine whether to run in batch mode */
    pub fn is_batch(&self) -> bool {
        !self.interactive
    }
    
    /** Determine whether to run in interactive mode */
    pub fn is_interactive(&self) -> bool {
        self.interactive
    }

    /** Determine how verbose text output should be */
    pub fn verbosity(&self) -> Verbosity {
        if self.debug {
            Verbosity::DebugVerbose
        } else if self.verbose {
            Verbosity::Verbose
        } else {
            Verbosity::NonVerbose
        }
    }
}