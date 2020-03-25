use crate::parser::Parser;
use crate::span::Span;

/// A struct representing a failure due to finding input when end of input was expected.
#[derive(Debug, PartialEq)]
pub struct ExpectedEndOfInput;

/// An expression for parsing an end of input.
pub struct EndOfInput;

impl<'i> Parser<'i> for EndOfInput {
    type Value = ();
    type Error = ExpectedEndOfInput;

    /// Parse an end of input.
    ///
    /// If the input is empty, this will succeed with `()`. Otherwise the result will be an `Err`
    /// with `ExpectedEndOfInput`.
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

    use super::{EndOfInput, ExpectedEndOfInput};

    #[test]
    fn ok_if_empty() {
        assert_eq!(EndOfInput.parse(""), Ok(Span::new(0..0, ())));
    }

    #[test]
    fn err_if_non_empty() {
        assert_eq!(
            EndOfInput.parse("hello"),
            Err(Span::new(0..1, ExpectedEndOfInput))
        );
    }

    #[test]
    fn err_if_non_empty_utf8() {
        assert_eq!(
            EndOfInput.parse("निello"),
            Err(Span::new(0..3, ExpectedEndOfInput))
        );
    }

    #[quickcheck]
    fn parse(input: String) {
        let result = EndOfInput.parse(&input);
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
