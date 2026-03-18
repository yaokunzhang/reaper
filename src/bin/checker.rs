#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_session;

use checker::analysis::option::Options;
use checker::utils;
use log::*;
use std::env;
use std::path::Path;

fn main() {
    // Initialize logger
    pretty_env_logger::init();

    // println!("hello checker world!");
    let early_error_handler =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());

    // // 打印所有环境变量
    // for (key, value) in env::vars() {
    //     println!("{}: {}", key, value);
    // }
    // 初始化日志
    // if env::var("RUSTC_LOG").is_ok() {
    //     rustc_driver::init_rustc_env_logger(&early_error_handler);
    // }
    // if env::var("CHECKER_LOG").is_ok() {
    //     let e = env_logger::Env::new()
    //         .filter("CHECKER_LOG")
    //         .write_style("CHECKER_LOG_STYLE");
    //     env_logger::init_from_env(e);
    // }

    // print env CHECKER_FLAGS
    if let Ok(flags) = env::var("CHECKER_FLAGS") {
        info!("CHECKER_FLAGS: {}", flags);
    }
    // Get any options specified via the MIRAI_FLAGS environment variable
    let mut options = Options::default();
    let rustc_args = options.parse_from_str(
        &env::var("CHECKER_FLAGS").unwrap_or_default(),
        &early_error_handler,
        false,
    );
    info!("rustc_args: {:?}", rustc_args);
    info!("CHECKER options from environment: {:?}", options);

    // Let arguments supplied on the command line override the environment variable.
    let mut args = env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                early_error_handler
                    .early_fatal(format!("Argument {i} is not valid Unicode: {arg:?}"))
            })
        })
        .collect::<Vec<_>>();
    assert!(!args.is_empty());
    info!("CHECKER command line arguments: {:?}", args);

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it if present.
    if args.len() > 1 && Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
        args.remove(1);
    }

    let mut rustc_command_line_arguments = options.parse(&args[1..], &early_error_handler, false);
    info!("CHECKER options modified by command line: {:?}", options);

    rustc_driver::install_ice_hook(rustc_driver::DEFAULT_BUG_REPORT_URL, |_| ());

    let result = rustc_driver::catch_fatal_errors(|| {
        // Add back the binary name
        rustc_command_line_arguments.insert(0, args[0].clone());

        let print: String = "--print=".into();
        if rustc_command_line_arguments
            .iter()
            .any(|arg| arg.starts_with(&print))
        {
            // If a --print option is given on the command line we wont get called to analyze
            // anything. We also don't want to the caller to know that MIRAI adds configuration
            // parameters to the command line, lest the caller be cargo and it panics because
            // the output from --print=cfg is not what it expects.
        } else {
            // Add rustc arguments supplied via the MIRAI_FLAGS environment variable
            rustc_command_line_arguments.extend(rustc_args);

            let sysroot: String = "--sysroot".into();
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.starts_with(&sysroot))
            {
                // Tell compiler where to find the std library and so on.
                // The compiler relies on the standard rustc driver to tell it, so we have to do likewise.
                rustc_command_line_arguments.push(sysroot);
                rustc_command_line_arguments.push(utils::find_sysroot());
            }

            let always_encode_mir: String = "always-encode-mir".into();
            if !rustc_command_line_arguments
                .iter()
                .any(|arg| arg.ends_with(&always_encode_mir))
            {
                // Tell compiler to emit MIR into crate for every function with a body.
                rustc_command_line_arguments.push("-Z".into());
                rustc_command_line_arguments.push(always_encode_mir);
            }

            // if options.test_only {
            //     let prefix: String = "mirai_annotations=".into();
            //     let postfix: String = ".rmeta".into();

            //     if let Some((_, s)) = rustc_command_line_arguments
            //         .iter_mut()
            //         .find_position(|arg| arg.starts_with(&prefix))
            //     {
            //         if s.ends_with(&postfix) {
            //             *s = s.replace(&postfix, ".rlib");
            //         }
            //     }
            // }
        }
        let mut callbacks = checker::analysis::callback::CheckerCallbacks::new(options);
        debug!(
            "rustc_command_line_arguments {:?}",
            rustc_command_line_arguments
        );
        rustc_driver::run_compiler(&rustc_command_line_arguments, &mut callbacks);
    })
    .and_then(|result| Ok(result));
    let exit_code = match result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };
    std::process::exit(exit_code);
}
