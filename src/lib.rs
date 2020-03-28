#![deny(missing_docs)]

//! Parsing expression grammar library.

pub mod expression;
mod parser;
mod span;

pub use expression::all_of::all_of;
pub use expression::any::{any, UnexpectedEndOfInput};
pub use expression::chr::{chr, ExpectedChar};
pub use expression::end_of_input::{end_of_input, ExpectedEndOfInput};
pub use expression::nothing::nothing;
pub use expression::one_of::one_of;
pub use expression::string::{string, ExpectedString};
pub use parser::{ParseResult, Parser};
pub use span::Span;
