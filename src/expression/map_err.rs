//! An expression that evaluates a sub-expression, and transforms failures.
//!
//! See [`map_err`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that will evaluate the given parser, and transform a failure with the given
/// function.
///
/// If the given parser evaluates successfully, the result will be `Ok` with the parsed value. If
/// the given parser fails, the result will be an `Err` with `transform(<parse failure>)`.
///
/// ```
/// use packrs::{ExpectedChar, Parser, ParserExt, Span, chr, map_err};
///
/// #[derive(Debug, PartialEq)]
/// enum Op {
///     Add,
///     Sub,
///     Mul,
///     Div,
/// }
///
/// #[derive(Debug, PartialEq)]
/// struct InvalidOp;
///
/// let op = map_err(
///     vec![
///         chr('+').map(|_| Op::Add).boxed(),
///         chr('-').map(|_| Op::Sub).boxed(),
///         chr('*').map(|_| Op::Mul).boxed(),
///         chr('/').map(|_| Op::Div).boxed(),
///     ].one_of(),
///     |_| InvalidOp
/// );
///
/// assert_eq!(op.parse("+"), Ok(Span::new(0..1, Op::Add)));
/// assert_eq!(op.parse("/"), Ok(Span::new(0..1, Op::Div)));
/// assert_eq!(op.parse("÷"), Err(Span::new(0..2, InvalidOp)));
/// ```
pub fn map_err<'i, P, F, E>(parser: P, transform: F) -> MapErr<P, F>
where
    P: Parser<'i>,
    F: Fn(P::Error) -> E,
{
    MapErr(parser, transform)
}

/// The struct returned from [`map_err`].
pub struct MapErr<P, F>(P, F);

impl<'i, P, F, U> Parser<'i> for MapErr<P, F>
where
    P: Parser<'i>,
    F: Fn(P::Error) -> U,
{
    type Value = P::Value;
    type Error = U;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0.parse(input).map_err(|value| value.map(&self.1))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use std::cell::Cell;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::map_err;

    #[test]
    fn p_match() {
        let called = Cell::new(false);
        let f = |_: TestError| {
            called.set(true);
            42
        };

        assert_eq!(
            (
                map_err(TestExpr::ok(23..89), f).parse("hello"),
                called.get()
            ),
            (Ok(Span::new(23..89, TestValue)), false)
        );
    }

    #[test]
    fn p_error() {
        let called = Cell::new(false);
        let f = |_: TestError| {
            called.set(true);
            42
        };

        assert_eq!(
            (
                map_err(TestExpr::err(23..89), f).parse("hello"),
                called.get()
            ),
            (Err(Span::new(23..89, 42)), true)
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String, value: usize) {
        let called = Cell::new(false);
        let f = |_: TestError| {
            called.set(true);
            value
        };

        assert_eq!(
            (map_err(&p, f).parse(&input), called.get()),
            match p {
                ParseMatch(config, _) => (Ok(Span::new(config.range(), TestValue)), false),
                ParseError(config) => (Err(Span::new(config.range(), value)), true),
            }
        );
    }
}
