#![deny(missing_docs)]

//! Parsing expression grammar library.

pub mod expression;
mod parser;
mod span;

pub use expression::{ExpectedChar, ExpectedEndOfInput, ExpectedString, UnexpectedEndOfInput};
pub use parser::*;
pub use span::Span;
