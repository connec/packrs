//! An expression that consumes a specific character.
//!
//! See [`crate::chr`].

use crate::error::ExpectedChar;
use crate::parser::Parser;
use crate::span::Span;

/// The struct returned from [`crate::chr`].
pub struct Chr(pub(crate) char);

impl Parser for Chr {
    type Value = char;
    type Error = ExpectedChar;

    fn parse<'i>(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let actual = input
            .chars()
            .next()
            .ok_or_else(|| Span::new(0..0, ExpectedChar(self.0)))?;
        let len = actual.len_utf8();
        if actual != self.0 {
            Err(Span::new(0..len, ExpectedChar(self.0)))
        } else {
            Ok(Span::new(0..len, actual))
        }
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::error::ExpectedChar;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::Chr;

    #[test]
    fn match_ascii() {
        assert_eq!(Chr('h').parse("hello"), Ok(Span::new(0..1, 'h')));
    }

    #[test]
    fn match_utf8() {
        assert_eq!(Chr('💩').parse("💩"), Ok(Span::new(0..4, '💩')));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(Chr('न').parse("नि"), Ok(Span::new(0..3, 'न')));
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
            assert_eq!(result, Ok(Span::new(0..char.len_utf8(), char)));
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
