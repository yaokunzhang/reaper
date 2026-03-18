use failure::Error;
use failure::Fail;
use std::fmt;
use std::time::Duration;

pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Debug for AnalysisInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "AnalysisInfo",)
    }
}

// Removed manual Debug implementation as we're deriving it

#[derive(Debug)]
pub enum AnalysisError {
    TimeOut,
    MaxIteration,
}

impl fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnalysisError::TimeOut => write!(f, "Analysis timeout"),
            AnalysisError::MaxIteration => write!(
                f,
                "The fixed-point algorithm reached the maximum iteration, abort"
            ),
        }
    }
}

impl Fail for AnalysisError {}

pub struct AnalysisInfo {
    pub analysis_time: Duration,
}
