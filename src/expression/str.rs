use core::cmp::min;

use crate::error::ExpectedString;
use crate::parser::Parser;
use crate::span::Span;

impl<'s> Parser for &'s str {
    type Value = Self;
    type Error = ExpectedString<'s>;

    fn parse(&self, input: &'_ str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        if input.starts_with(*self) {
            Ok(Span::new(0..self.len(), *self))
        } else if input.is_empty() {
            Err(Span::new(0..0, ExpectedString(*self)))
        } else {
            let mut len = min(input.len(), self.len());
            while input.get(0..len).is_none() {
                len += 1;
            }
            Err(Span::new(0..len, ExpectedString(*self)))
        }
    }
}

#[cfg(test)]
mod tests {
    use core::cmp::min;
    use quickcheck_macros::quickcheck;

    use crate::error::ExpectedString;
    use crate::parser::Parser;
    use crate::span::Span;

    #[test]
    fn match_ascii() {
        assert_eq!(
            Parser::parse(&"hello", "hello"),
            Ok(Span::new(0..5, "hello"))
        );
    }

    #[test]
    fn match_utf8() {
        assert_eq!(Parser::parse(&"💩", "💩"), Ok(Span::new(0..4, "💩")));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(Parser::parse(&"नि", "नि"), Ok(Span::new(0..6, "नि")));
    }

    #[test]
    fn error_if_empty() {
        assert_eq!(
            Parser::parse(&"hello", ""),
            Err(Span::new(0..0, ExpectedString("hello")))
        );
    }

    #[test]
    fn error_if_wrong_char_ascii() {
        assert_eq!(
            Parser::parse(&"hello", "world"),
            Err(Span::new(0..5, ExpectedString("hello")))
        );
    }

    #[test]
    fn error_if_wrong_char_grapheme() {
        assert_eq!(
            Parser::parse(&"hello", "नि"),
            Err(Span::new(0..6, ExpectedString("hello")))
        );
    }

    #[quickcheck]
    fn parse(string: String, input: std::string::String) {
        let result = Parser::parse(&&string[..], &input);
        if input.starts_with(&string) {
            assert_eq!(result, Ok(Span::new(0..string.len(), &string[..])));
        } else if input.is_empty() {
            assert_eq!(result, Err(Span::new(0..0, ExpectedString(&string))));
        } else {
            let mut len = min(input.len(), string.len());
            while input.get(0..len).is_none() {
                len += 1;
            }
            assert_eq!(result, Err(Span::new(0..len, ExpectedString(&string))));
        }
    }
}
