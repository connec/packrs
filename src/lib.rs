#![deny(missing_docs)]

//! Parsing expression grammar library.

pub mod expression;
mod parser;
mod span;

pub use expression::any::UnexpectedEndOfInput;
pub use expression::chr::ExpectedChar;
pub use expression::end_of_input::ExpectedEndOfInput;
pub use expression::string::ExpectedString;
pub use parser::*;
pub use span::Span;
