//! An expression that matches at the end of an input.
//!
//! See [`end_of_input`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that matches at the end of an input.
///
/// When given an empty input, the result will be `Ok(())`. When given a non-empty input the result
/// will be an `Err` with [`ExpectedEndOfInput`].
///
/// ```
/// use packrs::{ExpectedEndOfInput, Parser, Span, UnexpectedEndOfInput, all_of, any, end_of_input};
///
/// #[derive(Debug, PartialEq)]
/// enum Error {
///     ExpectedEndOfInput,
///     UnexpectedEndOfInput,
/// }
///
/// impl From<ExpectedEndOfInput> for Error {
///     fn from(_: ExpectedEndOfInput) -> Self {
///         Error::ExpectedEndOfInput
///     }
/// }
///
/// impl From<UnexpectedEndOfInput> for Error {
///     fn from(_: UnexpectedEndOfInput) -> Self {
///         Error::UnexpectedEndOfInput
///     }
/// }
///
/// let one_char = all_of(vec![
///     any().map_err(|err| err.into()).boxed(),
///     end_of_input().map(|_| "").map_err(|err| err.into()).boxed(),
/// ])
///     .collect();
///
/// assert_eq!(one_char.parse(""), Err(Span::new(0..0, Error::UnexpectedEndOfInput)));
/// assert_eq!(one_char.parse("💩"), Ok(Span::new(0..4, "💩".to_string())));
/// assert_eq!(one_char.parse("नि"), Err(Span::new(3..6, Error::ExpectedEndOfInput)));
/// ```
pub fn end_of_input() -> EndOfInput {
    EndOfInput
}

/// A struct representing a failure due to finding input when end of input was expected.
#[derive(Debug, PartialEq)]
pub struct ExpectedEndOfInput;

/// The struct returned from [`end_of_input`].
pub struct EndOfInput;

impl<'i> Parser<'i> for EndOfInput {
    type Value = ();
    type Error = ExpectedEndOfInput;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        if input.is_empty() {
            Ok(Span::new(0..0, ()))
        } else {
            let actual = input.chars().next().unwrap(); // `unwrap` because we already know string is non-empty
            Err(Span::new(0..actual.len_utf8(), ExpectedEndOfInput))
        }
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::parser::Parser;
    use crate::span::Span;

    use super::{end_of_input, ExpectedEndOfInput};

    #[test]
    fn ok_if_empty() {
        assert_eq!(end_of_input().parse(""), Ok(Span::new(0..0, ())));
    }

    #[test]
    fn err_if_non_empty() {
        assert_eq!(
            end_of_input().parse("hello"),
            Err(Span::new(0..1, ExpectedEndOfInput))
        );
    }

    #[test]
    fn err_if_non_empty_utf8() {
        assert_eq!(
            end_of_input().parse("निello"),
            Err(Span::new(0..3, ExpectedEndOfInput))
        );
    }

    #[quickcheck]
    fn parse(input: String) {
        let result = end_of_input().parse(&input);
        if input.is_empty() {
            assert_eq!(result, Ok(Span::new(0..0, ())));
        } else {
            let first_char = input.chars().next().unwrap();
            assert_eq!(
                result,
                Err(Span::new(0..first_char.len_utf8(), ExpectedEndOfInput))
            );
        }
    }
}
