//! An expression that consumes a specific character.
//!
//! See [`chr`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that consumes a specific character.
///
/// When given an input that starts with the given character, the result will be `Ok` with a
/// subslice of the input containing the character.
///
/// When given an input that does not start with the given character, the result will be an `Err`
/// with [`ExpectedChar`]`(char)`.
///
/// ```
/// use packrs::{ExpectedChar, ParserExt, Span, all_of, chr};
///
/// let hello = "hello".chars().map(chr).collect::<Vec<_>>().all_of().collect();
///
/// assert_eq!(hello.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
/// assert_eq!(hello.parse("world, hello"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
pub fn chr(char: char) -> Chr {
    Chr(char)
}

/// A struct representing a failure due to a missing expected character.
#[derive(Debug, PartialEq)]
pub struct ExpectedChar(
    /// The character that was expected.
    pub char,
);

/// The struct returned from [`chr`].
pub struct Chr(char);

impl<'i> Parser<'i> for Chr {
    type Value = &'i str;
    type Error = ExpectedChar;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
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

    use super::{chr, ExpectedChar};

    #[test]
    fn match_ascii() {
        assert_eq!(chr('h').parse("hello"), Ok(Span::new(0..1, "h")));
    }

    #[test]
    fn match_utf8() {
        assert_eq!(chr('💩').parse("💩"), Ok(Span::new(0..4, "💩")));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(chr('न').parse("नि"), Ok(Span::new(0..3, "न")));
    }

    #[test]
    fn error_if_empty() {
        assert_eq!(chr('h').parse(""), Err(Span::new(0..0, ExpectedChar('h'))));
    }

    #[test]
    fn error_if_wrong_char_ascii() {
        assert_eq!(
            chr('h').parse("world"),
            Err(Span::new(0..1, ExpectedChar('h')))
        );
    }

    #[test]
    fn error_if_wrong_char_grapheme() {
        assert_eq!(
            chr('h').parse("नि"),
            Err(Span::new(0..3, ExpectedChar('h')))
        );
    }

    #[quickcheck]
    fn parse(char: char, input: String) {
        let result = chr(char).parse(&input);
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
