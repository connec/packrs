#![deny(missing_docs)]

//! Parsing expression grammar library.

mod combinators;
mod expression;
mod parser;
mod span;

pub use combinators::*;
pub use expression::{ExpectedChar, UnexpectedEndOfInput};
pub use parser::{ParseResult, Parser};
pub use span::Span;
