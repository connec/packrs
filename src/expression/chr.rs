use crate::parser::Parser;
use crate::span::Span;

/// A struct representing a failure due to a missing expected character.
#[derive(Debug, PartialEq)]
pub struct ExpectedChar(
    /// The character that was expected.
    pub char,
);

/// An expression for parsing a specific character.
pub struct Chr(pub(crate) char);

impl<'a> Parser<'a> for Chr {
    type Value = &'a str;
    type Error = ExpectedChar;

    /// Parse a specific character from an `&str`.
    ///
    /// If the the input begins with the character then the successful result will contain the
    /// matched slice of the input. Otherwise, an [`ExpectedChar`] error is returned.
    ///
    /// [`ExpectedChar`]: enum.Error.html#variant.ExpectedChar
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let actual = input
            .chars()
            .next()
            .ok_or_else(|| Span::new(0..0, ExpectedChar(self.0)))?;
        let len = actual.len_utf8();
        if actual != self.0 {
            Err(Span::new(0..len, ExpectedChar(self.0)))
        } else {
            Ok(Span::new(0..len, &input[0..len]))
        }
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::parser::Parser;
    use crate::span::Span;

    use super::{Chr, ExpectedChar};

    #[test]
    fn match_ascii() {
        assert_eq!(Chr('h').parse("hello"), Ok(Span::new(0..1, "h")));
    }

    #[test]
    fn match_utf8() {
        assert_eq!(Chr('💩').parse("💩"), Ok(Span::new(0..4, "💩")));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(Chr('न').parse("नि"), Ok(Span::new(0..3, "न")));
    }

    #[test]
    fn error_if_empty() {
        assert_eq!(Chr('h').parse(""), Err(Span::new(0..0, ExpectedChar('h'))));
    }

    #[test]
    fn error_if_wrong_char_ascii() {
        assert_eq!(
            Chr('h').parse("world"),
            Err(Span::new(0..1, ExpectedChar('h')))
        );
    }

    #[test]
    fn error_if_wrong_char_grapheme() {
        assert_eq!(
            Chr('h').parse("नि"),
            Err(Span::new(0..3, ExpectedChar('h')))
        );
    }

    #[quickcheck]
    fn parse(char: char, input: String) {
        let result = Chr(char).parse(&input);
        if input.starts_with(char) {
            assert_eq!(
                result,
                Ok(Span::new(0..char.len_utf8(), &format!("{}", char)[..]))
            );
        } else if input.is_empty() {
            assert_eq!(result, Err(Span::new(0..0, ExpectedChar(char))));
        } else {
            let actual_char = input.chars().next().unwrap();
            assert_eq!(
                result,
                Err(Span::new(0..actual_char.len_utf8(), ExpectedChar(char)))
            );
        }
    }
}
