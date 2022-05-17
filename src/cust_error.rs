//! This module contains all custom errors used in this library.

use std::fmt;
use std::error::Error;

#[derive(Debug)]
pub enum ImportError {
    IoError(std::io::Error),
    InputMalformedError,
    BadIntError(std::num::ParseIntError),
}

impl From<std::io::Error> for ImportError {
    fn from(e: std::io::Error) -> ImportError {
        ImportError::IoError(e)
    }
}

impl From<std::num::ParseIntError> for ImportError {
    fn from(e: std::num::ParseIntError) -> ImportError {
        ImportError::BadIntError(e)
    }
}

impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IoError(_) => write!(f, "Import: IoError"),
            Self::InputMalformedError => write!(f, "Import: Input is malformed."),
            Self::BadIntError(_) => write!(f, "Import: Integer is malformed."),
        }
    }
}

impl Error for ImportError {}

#[derive(Debug)]
pub enum ProcessingError {
    InvalidParameter(String),
    GraphError(String),
    /// Error at the conversion of placeholder from the `LinkNode`-rule in the solution set.
    ConversionError,
    RebuildError,
    InvalidSolution(String),
}

impl fmt::Display for ProcessingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidParameter(msg) => write!(f, "Invalid parameter: {}", msg),
            Self::GraphError(msg) => write!(f, "Graph error: {}", msg),
            Self::ConversionError => write!(f, "Conversion error"),
            Self::RebuildError => write!(f, "Rebuild error"),
            Self::InvalidSolution(msg) => write!(f, "InvalidSolution: {}", msg),
        }
    }
}

impl Error for ProcessingError {}
