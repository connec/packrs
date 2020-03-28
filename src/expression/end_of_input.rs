//! An expression that matches at the end of an input.
//!
//! See [`crate::end_of_input`].

use crate::error::ExpectedEndOfInput;
use crate::parser::Parser;
use crate::span::Span;

/// The struct returned from [`crate::end_of_input`].
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

    use crate::error::ExpectedEndOfInput;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::EndOfInput;

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
