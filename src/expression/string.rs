//! An expression that matches a string at the beginning on an input.
//!
//! See [`crate::string`].

use crate::error::ExpectedString;
use crate::parser::Parser;
use crate::span::Span;

/// The struct returned from [`crate::string`].
pub struct String<'s>(pub(crate) &'s str);

impl<'s, 'i> Parser<'i> for String<'s> {
    type Value = &'i str;
    type Error = ExpectedString<'s>;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        if input.starts_with(self.0) {
            Ok(Span::new(0..self.0.len(), &input[0..self.0.len()]))
        } else {
            let actual = input
                .chars()
                .next()
                .ok_or_else(|| Span::new(0..0, ExpectedString(self.0)))?;
            let len = actual.len_utf8();
            Err(Span::new(0..len, ExpectedString(self.0)))
        }
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::error::ExpectedString;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::String;

    #[test]
    fn match_ascii() {
        assert_eq!(String("hello").parse("hello"), Ok(Span::new(0..5, "hello")));
    }

    #[test]
    fn match_utf8() {
        assert_eq!(String("💩").parse("💩"), Ok(Span::new(0..4, "💩")));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(String("नि").parse("नि"), Ok(Span::new(0..6, "नि")));
    }

    #[test]
    fn error_if_empty() {
        assert_eq!(
            String("hello").parse(""),
            Err(Span::new(0..0, ExpectedString("hello")))
        );
    }

    #[test]
    fn error_if_wrong_char_ascii() {
        assert_eq!(
            String("hello").parse("world"),
            Err(Span::new(0..1, ExpectedString("hello")))
        );
    }

    #[test]
    fn error_if_wrong_char_grapheme() {
        assert_eq!(
            String("hello").parse("नि"),
            Err(Span::new(0..3, ExpectedString("hello")))
        );
    }

    #[quickcheck]
    fn parse(string: std::string::String, input: std::string::String) {
        let result = String(&string).parse(&input);
        if input.starts_with(&string) {
            assert_eq!(result, Ok(Span::new(0..string.len(), &string[..])));
        } else if input.is_empty() {
            assert_eq!(result, Err(Span::new(0..0, ExpectedString(&string))));
        } else {
            let actual_char = input.chars().next().unwrap();
            assert_eq!(
                result,
                Err(Span::new(
                    0..actual_char.len_utf8(),
                    ExpectedString(&string)
                ))
            );
        }
    }
}
