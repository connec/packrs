//! An expression that evaluates a sub-expression, and transforms successful results.
//!
//! See [`map`].

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that will evaluate the given parser, and transform a successful result with the
/// given function.
///
/// If the given parser evaluates successfully, the result will be `Ok` with
/// `transform(<parsed value>)`. If the given parser fails, the result will be an `Err` with the
/// parse failure.
///
/// ```
/// use packrs::{ExpectedChar, Parser, ParserExt, Span, chr, map};
///
/// #[derive(Debug, PartialEq)]
/// enum Op {
///     Add,
///     Sub,
///     Mul,
///     Div,
/// }
///
/// let op = vec![
///     map(chr('+'), |_| Op::Add).boxed(),
///     map(chr('-'), |_| Op::Sub).boxed(),
///     map(chr('*'), |_| Op::Mul).boxed(),
///     map(chr('/'), |_| Op::Div).boxed(),
/// ].one_of();
///
/// assert_eq!(op.parse("+"), Ok(Span::new(0..1, Op::Add)));
/// assert_eq!(op.parse("/"), Ok(Span::new(0..1, Op::Div)));
/// assert_eq!(op.parse("÷"), Err(Span::new(0..2, vec![
///     Span::new(0..2, ExpectedChar('+')),
///     Span::new(0..2, ExpectedChar('-')),
///     Span::new(0..2, ExpectedChar('*')),
///     Span::new(0..2, ExpectedChar('/')),
/// ])));
/// ```
pub fn map<'i, P, F, U>(parser: P, transform: F) -> Map<P, F>
where
    P: Parser<'i>,
    F: Fn(P::Value) -> U,
{
    Map(parser, transform)
}

/// The struct returned from [`map`].
pub struct Map<P, F>(P, F);

impl<'i, P, F, U> Parser<'i> for Map<P, F>
where
    P: Parser<'i>,
    F: Fn(P::Value) -> U,
{
    type Value = U;
    type Error = P::Error;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0.parse(input).map(|value| value.map(&self.1))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use std::cell::Cell;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::map;

    #[test]
    fn p_match() {
        let called = Cell::new(false);
        let f = |_: TestValue| {
            called.set(true);
            42
        };

        assert_eq!(
            (map(TestExpr::ok(23..89), f).parse("hello"), called.get()),
            (Ok(Span::new(23..89, 42)), true)
        );
    }

    #[test]
    fn p_error() {
        let called = Cell::new(false);
        let f = |_: TestValue| {
            called.set(true);
            42
        };

        assert_eq!(
            (map(TestExpr::err(23..89), f).parse("hello"), called.get()),
            (Err(Span::new(23..89, TestError)), false)
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String, value: usize) {
        let called = Cell::new(false);
        let f = |_: TestValue| {
            called.set(true);
            value
        };

        assert_eq!(
            (map(&p, f).parse(&input), called.get()),
            match p {
                ParseMatch(config, _) => (Ok(Span::new(config.range(), value)), true),
                ParseError(config) => (Err(Span::new(config.range(), TestError)), false),
            }
        );
    }
}
