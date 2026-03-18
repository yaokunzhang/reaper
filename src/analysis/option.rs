// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
use crate::analysis::diagnostics::DiagnosticCause;
use clap::error::ErrorKind;
use clap::parser::ValueSource;
use clap::{Arg, Command};
use itertools::Itertools;

use rustc_session::EarlyDiagCtxt;

/// Creates the clap::Command metadata for argument parsing.
fn make_options_parser(running_test_harness: bool) -> Command {
    let mut parser = Command::new("BOFD")
        .no_binary_name(true)
        .version("v1.0.0")
        .arg(
            Arg::new("entry_point")
                .long("entry_point")
                .num_args(1)
                .help("Specify the entry point function name.")
                .long_help("The name of the top-level entry point function to analyze."),
        )
        .arg(
            Arg::new("unsafe_only")
                .long("unsafe_only")
                .num_args(0)
                .help("Only analyze potential unsafe function.")
                .long_help("Only analyze potential unsafe function."),
        )
        .arg(
            Arg::new("entry_def_id_index")
                .long("entry_def_id_index")
                .num_args(1)
                .help("Specify the entry point definition ID index.")
                .long_help("Optional ID index for the entry point definition."),
        )
        .arg(
            Arg::new("domain_type")
                .long("domain_type")
                .num_args(1)
                .help("Specify the abstract domain type.")
                .long_help("The type of abstract domain to use during the analysis."),
        )
        .arg(
            Arg::new("widening_delay")
                .long("widening_delay")
                .num_args(1)
                .default_value("0")
                .help("Set the widening delay.")
                .long_help("The number of iterations before widening is applied."),
        )
        .arg(
            Arg::new("cleaning_delay")
                .long("cleaning_delay")
                .num_args(1)
                .default_value("0")
                .help("Set the cleaning delay.")
                .long_help("The number of iterations before cleaning is applied."),
        )
        .arg(
            Arg::new("narrowing_iteration")
                .long("narrowing_iteration")
                .num_args(1)
                .default_value("0")
                .help("Set the narrowing iteration count.")
                .long_help("The number of iterations for narrowing after widening."),
        )
        .arg(
            Arg::new("show_entries")
                .long("show_entries")
                .num_args(0)
                .help("Show entry points during analysis.")
                .long_help("Enable this flag to print out the entry points being analyzed."),
        )
        .arg(
            Arg::new("show_entries_index")
                .long("show_entries_index")
                .num_args(0)
                .help("Show entry point indices during analysis.")
                .long_help(
                    "Enable this flag to print out the indices of entry points being analyzed.",
                ),
        )
        .arg(
            Arg::new("deny_warnings")
                .long("deny_warnings")
                .num_args(0)
                .help("Treat warnings as errors.")
                .long_help("Enable this flag to treat all warnings as errors during analysis."),
        )
        .arg(
            Arg::new("memory_safety_only")
                .long("memory_safety_only")
                .num_args(0)
                .help("Limit analysis to memory safety.")
                .long_help(
                    "Enable this flag to restrict the analysis to memory safety issues only.",
                ),
        )
        .arg(
            Arg::new("suppressed_warnings")
                .long("suppressed_warnings")
                .num_args(1)
                .help("Specify warnings to suppress.")
                .long_help("A comma-separated list of diagnostic causes to suppress warnings for."),
        );

    if running_test_harness {
        parser = parser.arg(Arg::new("test_only")
        .long("test_only")
        .num_args(0)
        .help("Focus analysis on #[test] methods.")
        .long_help("Only #[test] methods and their usage are analyzed. This must be used together with the rustc --test option."));
    }

    parser
}

#[derive(Clone, Copy, Debug)]
pub enum AbstractDomainType {
    Interval,
    Octagon,
    Polyhedra,
    LinearEqualities,
    PplPolyhedra,
    PplLinearCongruences,
    PkgridPolyhedraLinCongruences,
}

/// Represents options passed to BOFD.
#[derive(Debug, Clone)]
pub struct Options {
    pub unsafe_only: bool,
    pub entry_point: String,
    pub entry_def_id_index: Option<u32>,
    pub domain_type: AbstractDomainType,
    pub widening_delay: u32,
    pub cleaning_delay: usize,
    pub narrowing_iteration: u32,
    pub show_entries: bool,
    pub show_entries_index: bool,
    pub deny_warnings: bool,
    pub memory_safety_only: bool,
    pub suppressed_warnings: Option<Vec<DiagnosticCause>>,
}

impl Default for Options {
    fn default() -> Self {
        Self {
            unsafe_only: false,
            entry_point: String::from("main"),
            entry_def_id_index: None,
            domain_type: AbstractDomainType::Interval,
            widening_delay: 5,
            cleaning_delay: 5,
            narrowing_iteration: 1,
            show_entries: false,
            show_entries_index: false,
            deny_warnings: false,
            memory_safety_only: false,
            suppressed_warnings: None,
        }
    }
}

/// Represents diag level.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq, PartialOrd)]
pub enum DiagLevel {
    /// When a function calls a function without a body and with no foreign function summary, the call assumed to be
    /// correct and any diagnostics that depend on the result of the call in some way are suppressed.
    #[default]
    Default,
    /// Like Default, but emit a diagnostic if there is a call to a function without a body and with no foreign function summary.
    Verify,
    /// Like Verify, but issues diagnostics if non analyzed code can provide arguments that will cause
    /// the analyzed code to go wrong. I.e. it requires all preconditions to be explicit.
    /// This mode should be used for any library whose callers are not known and therefore not analyzed.
    Library,
    // Like Library, but also carries on analysis of functions after a call to an incompletely
    // analyzed function has been encountered.
    Paranoid,
}

impl Options {
    /// Parse options from an argument string. The argument string will be split using unix
    /// shell escaping rules. Any content beyond the leftmost `--` token will be returned
    /// (excluding this token).
    pub fn parse_from_str(
        &mut self,
        s: &str,
        handler: &EarlyDiagCtxt,
        running_test_harness: bool,
    ) -> Vec<String> {
        self.parse(
            &shellwords::split(s).unwrap_or_else(|e| {
                handler.early_fatal(format!("Cannot parse argument string: {e:?}"))
            }),
            handler,
            running_test_harness,
        )
    }

    /// Parses options from a list of strings. Any content beyond the leftmost `--` token
    /// will be returned (excluding this token).
    pub fn parse(
        &mut self,
        args: &[String],
        handler: &EarlyDiagCtxt,
        running_test_harness: bool,
    ) -> Vec<String> {
        let mut bofd_args_end = args.len();
        let mut rustc_args_start = 0;
        if let Some((p, _)) = args.iter().find_position(|s| s.as_str() == "--") {
            bofd_args_end = p;
            rustc_args_start = p + 1;
        }
        let bofd_args = &args[0..bofd_args_end];
        let matches = if rustc_args_start == 0 {
            match make_options_parser(running_test_harness).try_get_matches_from(bofd_args.iter()) {
                Ok(matches) => {
                    rustc_args_start = args.len();
                    matches
                }
                Err(e) => match e.kind() {
                    ErrorKind::DisplayHelp => {
                        eprintln!("{e}");
                        return args.to_vec();
                    }
                    ErrorKind::UnknownArgument => {
                        return args.to_vec();
                    }
                    _ => {
                        eprintln!("{e}");
                        e.exit();
                    }
                },
            }
        } else {
            make_options_parser(running_test_harness).get_matches_from(bofd_args.iter())
        };

        // println!("matches: {:?}", matches);

        if matches.contains_id("entry_point") {
            self.entry_point = matches
                .get_one::<String>("entry_point")
                .cloned()
                .unwrap_or_default();
        }
        if matches.contains_id("entry_def_id_index") {
            self.entry_def_id_index = matches
                .get_one::<String>("entry_def_id_index")
                .and_then(|s| s.parse::<u32>().ok());
        }
        if matches.contains_id("domain_type") {
            let domain_type_str = matches.get_one::<String>("domain_type").unwrap().as_str();
            self.domain_type = Self::get_domain_type(domain_type_str).unwrap_or_else(|| {
                handler.early_fatal("--domain_type expects a valid domain type")
            });
        }
        if matches.contains_id("widening_delay") {
            self.widening_delay = match matches.get_one::<String>("widening_delay") {
                Some(s) => s
                    .parse::<u32>()
                    .unwrap_or_else(|_| handler.early_fatal("--widening_delay expects an integer")),
                None => 0,
            };
        }
        if matches.contains_id("cleaning_delay") {
            self.cleaning_delay = match matches.get_one::<String>("cleaning_delay") {
                Some(s) => s
                    .parse::<usize>()
                    .unwrap_or_else(|_| handler.early_fatal("--cleaning_delay expects an integer")),
                None => 0,
            };
        }
        if matches.contains_id("narrowing_iteration") {
            self.narrowing_iteration = match matches.get_one::<String>("narrowing_iteration") {
                Some(s) => s.parse::<u32>().unwrap_or_else(|_| {
                    handler.early_fatal("--narrowing_iteration expects an integer")
                }),
                None => 0,
            };
        }
        if !matches!(
            matches.value_source("unsafe_only"),
            Some(ValueSource::DefaultValue)
        ) {
            // println!("show_entries is hit");
            self.unsafe_only = true;
        }
        if !matches!(
            matches.value_source("show_entries"),
            Some(ValueSource::DefaultValue)
        ) {
            // println!("show_entries is hit");
            self.show_entries = true;
        }
        if !matches!(
            matches.value_source("show_entries_index"),
            Some(ValueSource::DefaultValue)
        ) {
            // println!("show_entries_index is hit");
            self.show_entries_index = true;
        }

        if !matches!(
            matches.value_source("deny_warnings"),
            Some(ValueSource::DefaultValue)
        ) {
            // println!("deny_warnings is hit");
            self.deny_warnings = true;
        }

        if !matches!(
            matches.value_source("memory_safety_only"),
            Some(ValueSource::DefaultValue)
        ) {
            // println!("memory_safety_only is hit");
            self.memory_safety_only = true;
        }

        args[rustc_args_start..].to_vec()
    }

    #[allow(dead_code)]
    fn get_suppressed_warnings(arg: &str) -> Option<Vec<DiagnosticCause>> {
        let mut res = Vec::new();
        for ch in arg.chars() {
            match ch {
                'a' => res.push(DiagnosticCause::Arithmetic), // Arithmetic overflow
                'b' => res.push(DiagnosticCause::Bitwise),    // Bit-wise overflow
                's' => res.push(DiagnosticCause::Assembly),   // Inline assembly
                'c' => res.push(DiagnosticCause::Comparison), // Comparison operations
                'd' => res.push(DiagnosticCause::DivZero), // Division by zero / remainder by zero
                'm' => res.push(DiagnosticCause::Memory),  // Memory-safety issues
                'p' => res.push(DiagnosticCause::Panic),   // Run into panic code
                'i' => res.push(DiagnosticCause::Index),   // Out-of-bounds access
                _ => return None,                          // Invalid flags
            }
        }
        if res.is_empty() {
            None
        } else {
            Some(res)
        }
    }

    fn get_domain_type(arg: &str) -> Option<AbstractDomainType> {
        match arg {
            "interval" => Some(AbstractDomainType::Interval),
            "octagon" => Some(AbstractDomainType::Octagon),
            "polyhedra" => Some(AbstractDomainType::Polyhedra),
            "linear_equalities" => Some(AbstractDomainType::LinearEqualities),
            "ppl_polyhedra" => Some(AbstractDomainType::PplPolyhedra),
            "ppl_linear_congruences" => Some(AbstractDomainType::PplLinearCongruences),
            "pkgrid_polyhedra_linear_congruences" => {
                Some(AbstractDomainType::PkgridPolyhedraLinCongruences)
            }
            _ => None,
        }
    }

    // Remove a list of indices from a vector
    // From https://stackoverflow.com/questions/57947441/remove-a-sequence-of-values-from-a-vec-in-rust
    #[allow(dead_code)]
    fn remove_multiple<T>(source: &mut Vec<T>, indices_to_remove: &[usize]) -> Vec<T> {
        indices_to_remove
            .iter()
            .copied()
            .map(|i| source.swap_remove(i))
            .collect()
    }
}
