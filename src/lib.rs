#![deny(missing_docs)]

//! Parsing expression grammar library.

mod expression;
mod parser;
mod span;

pub use expression::*;
pub use parser::{ParseResult, Parser};
pub use span::Span;
