use crate::parser::Parser;
use crate::span::Span;

/// A struct representing a failure due to unexpected end of input.
#[derive(Debug, PartialEq)]
pub struct UnexpectedEndOfInput;

/// An expression for parsing an arbitrary character.
pub struct Any;

impl<'i> Parser<'i> for Any {
    type Value = &'i str;
    type Error = UnexpectedEndOfInput;

    /// Parse an arbitrary character from an `&str`.
    ///
    /// If the input is empty, this will fail with [`UnexpectedEndOfInput`]. Otherwise, the result
    /// will be a `&str` containing the first character of the string.
    ///
    /// [`UnexpectedEndOfInput`]: enum.Error.html#variant.UnexpectedEndOfInput
    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let actual = input
            .chars()
            .next()
            .ok_or_else(|| Span::new(0..0, UnexpectedEndOfInput))?;
        let len = actual.len_utf8();
        Ok(Span::new(0..len, &input[0..len]))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::parser::Parser;
    use crate::span::Span;

    use super::{Any, UnexpectedEndOfInput};

    #[test]
    fn match_ascii() {
        assert_eq!(Any.parse("hello"), Ok(Span::new(0..1, "h")));
    }

    #[test]
    fn match_utf8() {
        assert_eq!(Any.parse("💩"), Ok(Span::new(0..4, "💩")));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(Any.parse("नि"), Ok(Span::new(0..3, "न")));
    }

    #[test]
    fn error_if_empty() {
        assert_eq!(Any.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
    }

    #[quickcheck]
    fn parse(input: String) {
        let result = Any.parse(&input);
        if input.is_empty() {
            assert_eq!(result, Err(Span::new(0..0, UnexpectedEndOfInput)));
        } else {
            let first_char = input.chars().next().unwrap();
            assert_eq!(
                result,
                Ok(Span::new(
                    0..first_char.len_utf8(),
                    &format!("{}", first_char)[..]
                ))
            );
        }
    }
}
