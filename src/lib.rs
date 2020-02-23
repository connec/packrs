#![deny(missing_docs)]

//! Parsing expression grammar library.
//!
//! Currently there are two implementations of PEG expressions:
//!
//! - [`combinators`] implements PEG expressions as parser combinators.
//! - [`expressions`] implements PEG expressions as an enum.
//!
//! Both are currently only capable of *matching* a given `&str` input, and cannot make use of the
//! structural information discovered during parsing.
//!
//! [`combinators`]: combinators/index.html
//! [`expressions`]: expressions/index.html

pub mod combinators;
pub mod combinators2;
pub mod expression;
