//! An expression that evaluates a sub-expression and rejects successful results.
//!
//! See [`reject`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that evaluates the given parser, succeeding on failure, failing on success, and
/// consuming no input.
///
/// If the given parser evaluates successfully, the result will be `Err(())`. If the given parser
/// fails, the result will be `Ok(())`.
///
/// ```
/// use packrs::{Parser, ParserExt, Span, UnexpectedEndOfInput, any, chr, reject};
///
/// let first_word = vec![
///     reject(chr(' ')).map(|_| "").map_err(|_| UnexpectedEndOfInput).boxed(),
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
pub fn reject<'i, P>(parser: P) -> Reject<P>
where
    P: Parser<'i>,
{
    Reject(parser)
}

/// The struct returned from [`reject`].
pub struct Reject<P>(P);

impl<'i, P> Parser<'i> for Reject<P>
where
    P: Parser<'i>,
{
    type Value = ();
    type Error = ();

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0
            .parse(input)
            .map_or_else(|_| Ok(Span::new(0..0, ())), |_| Err(Span::new(0..0, ())))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::reject;

    #[test]
    fn p_match() {
        assert_eq!(
            reject(TestExpr::ok(12..37)).parse("hello"),
            Err(Span::new(0..0, ()))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            reject(TestExpr::err(12..37)).parse("hello"),
            Ok(Span::new(0..0, ()))
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String) {
        assert_eq!(
            reject(&p).parse(&input),
            match p {
                ParseMatch(_, _) => Err(Span::new(0..0, ())),
                ParseError(_) => Ok(Span::new(0..0, ())),
            }
        );
    }
}
