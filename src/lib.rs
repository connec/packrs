#![deny(missing_docs)]

//! Parsing expression grammar library.
//!
//! See [`Expression`], which represents valid parsing expression grammar expressions, and [`eval`],
//! which can evaluate them against a string.
//!
//! [`Expression`]: expression/enum.Expression.html
//! [`eval`]: expression/fn.eval.html

pub mod expression;
