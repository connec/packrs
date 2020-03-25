#![deny(missing_docs)]

//! Parsing expression grammar library.

mod combinators;
mod expression;
mod parser;
mod parser_ext;
mod span;

pub use combinators::*;
pub use expression::{ExpectedChar, ExpectedEndOfInput, ExpectedString, UnexpectedEndOfInput};
pub use parser::{ParseResult, Parser};
pub use parser_ext::ParserExt;
pub use span::Span;
