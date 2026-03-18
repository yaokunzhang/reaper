use crate::analysis::analyzer::analysis_trait::StaticAnalysis;
use crate::analysis::analyzer::numerical_analysis::NumericalAnalysis;
use crate::analysis::global_context::GlobalContext;
use crate::analysis::option::Options;
use log::{error, info};
use rustc_driver::Compilation;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;

pub struct CheckerCallbacks {
    pub analysis_options: Options,
    pub source_name: String,
}

impl CheckerCallbacks {
    pub fn new(options: Options) -> Self {
        Self {
            analysis_options: options,
            source_name: String::new(),
        }
    }
}

impl rustc_driver::Callbacks for CheckerCallbacks {
    /// Called before creating the compiler instance
    fn config(&mut self, config: &mut interface::Config) {
        self.source_name = config
            .input
            .source_name()
            .prefer_remapped_unconditionaly()
            .to_string();
        config.crate_cfg.push("mirai".to_string());
        info!("Source file: {}", self.source_name);
    }

    /// Called after analysis. Return value instructs the compiler whether to
    /// continue the compilation afterwards (defaults to `Compilation::Continue`)
    fn after_analysis<'compiler, 'tcx>(
        &mut self,
        compiler: &'compiler interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        self.run_analysis(compiler, tcx);
        Compilation::Continue
    }
}

impl CheckerCallbacks {
    fn run_analysis<'tcx, 'compiler>(
        &mut self,
        compiler: &'compiler interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) {
        if self.source_name.contains("/libcore")
            || self.source_name.contains("/compiler_builtins")
            || self.source_name.contains("/liballoc")
            || self.source_name.contains("/macro")
            || self.source_name.contains("/libc")
        {
            info!(
                "Find filename that should skip the analysis: {}",
                self.source_name
            );
            return;
        }

        // Initialize global analysis context
        if let Some(mut global_context) =
            GlobalContext::new(&compiler.sess, tcx, self.analysis_options.clone())
        {
            let entry_points = global_context.entry_points.clone();
            for entry_point in entry_points {
                info!("begin analyzing {:?}", entry_point.clone());

                global_context.entry_point = entry_point;
                // Initialize numerical analyzer
                let mut numerical_analysis = NumericalAnalysis::new(&mut global_context);
                // Run analyzer
                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || {
                    numerical_analysis.run()
                })) {
                    Ok(analysis_result) => match analysis_result {
                        Ok(result) => {
                            info!(
                                "Numerical Analysis Completed: {} ms",
                                result.analysis_time.as_millis()
                            );
                        }
                        Err(_) => {
                            error!(
                                "Numerical Analysis Failed in {:?}",
                                global_context.entry_point
                            );
                        }
                    },
                    Err(e) => {
                        if let Some(msg) = e.downcast_ref::<&str>() {
                            info!("Analysis panicked with message: {}", msg);
                        } else {
                            info!("Analysis panicked without a message");
                        }
                        info!("Continuing with next entry point...");
                    }
                }
            }
        } else {
            error!("GlobalContext Initialization Failed");
        }
    }
}
