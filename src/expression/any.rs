//! An expression that consumes any single character.
//!
//! See [`any`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that consumes any single character.
///
/// When given a non-empty input, the result will be `Ok` with a subslice of the input containing
/// the first character.
///
/// When given an empty input, the result will be an `Err` with [`UnexpectedEndOfInput`].
///
/// ```
/// use packrs::{Parser, ParserExt, Span, UnexpectedEndOfInput, any, chr};
///
/// let first_word = vec![
///     chr(' ')
///         .reject()
///         .map(|_| "")
///         .map_err(|_| UnexpectedEndOfInput)
///         .boxed(),
///     any().boxed(),
/// ]
///     .all_of()
///     .map(|mut v| v.pop().unwrap().take())
///     .repeat()
///     .collect();
///
/// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
/// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
/// ```
pub fn any() -> Any {
    Any
}

/// A struct representing a failure due to unexpected end of input.
#[derive(Debug, PartialEq)]
pub struct UnexpectedEndOfInput;

/// The struct returned from [`any`].
pub struct Any;

impl<'i> Parser<'i> for Any {
    type Value = &'i str;
    type Error = UnexpectedEndOfInput;

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

    use super::{any, UnexpectedEndOfInput};

    #[test]
    fn match_ascii() {
        assert_eq!(any().parse("hello"), Ok(Span::new(0..1, "h")));
    }

    #[test]
    fn match_utf8() {
        assert_eq!(any().parse("💩"), Ok(Span::new(0..4, "💩")));
    }

    #[test]
    fn match_grapheme() {
        assert_eq!(any().parse("नि"), Ok(Span::new(0..3, "न")));
    }

    #[test]
    fn error_if_empty() {
        assert_eq!(any().parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
    }

    #[quickcheck]
    fn parse(input: String) {
        let result = any().parse(&input);
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
