//! An expression that evaluates a sub-expression, and converts the result into an `Option`.
//!
//! See [`maybe`].

use core::marker::PhantomData;

use crate::parser::Parser;
use crate::span::Span;

/// Create a parser that will evaluate the given parser, converting the result into an `Option`.
///
/// This will always return `Ok`. If the given parser evaluates successfully, this will contain
/// `Some(<parsed value>)`. If the given parser fails, this will contain `None`.
///
/// ```
/// use packrs::{ExpectedChar, Parser, ParserExt, Span, chr, maybe, string};
///
/// let expr = vec![
///     chr('1').boxed(),
///     maybe(string("+1"))
///         .map(|opt| match opt {
///             Some(span) => span.take(),
///             None => "",
///         })
///         .boxed()
/// ]
///     .all_of()
///     .collect();
///
/// assert_eq!(expr.parse("1"), Ok(Span::new(0..1, "1".to_string())));
/// assert_eq!(expr.parse("1+1"), Ok(Span::new(0..3, "1+1".to_string())));
/// assert_eq!(expr.parse("2+1"), Err(Span::new(0..1, ExpectedChar('1'))));
/// ```
pub fn maybe<'i, P, E>(parser: P) -> Maybe<P, E>
where
    P: Parser<'i>,
{
    Maybe(parser, PhantomData)
}

/// The struct returned from [`maybe`].
pub struct Maybe<P, E>(P, PhantomData<E>);

impl<'i, P, E> Parser<'i> for Maybe<P, E>
where
    P: Parser<'i>,
{
    type Value = Option<Span<P::Value>>;
    type Error = E;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(match self.0.parse(input) {
            Ok(value) => Span::new(value.start()..value.end(), Some(value)),
            Err(_) => Span::new(0..0, None),
        })
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::expression::test_expr::*;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::maybe;

    #[test]
    fn p_match() {
        assert_eq!(
            maybe::<_, ()>(TestExpr::ok(83..98)).parse("hello"),
            Ok(Span::new(83..98, Some(Span::new(83..98, TestValue))))
        );
    }

    #[test]
    fn p_error() {
        assert_eq!(
            maybe::<_, ()>(TestExpr::err(5..458)).parse("hello"),
            Ok(Span::new(0..0, None))
        );
    }

    #[quickcheck]
    fn parse(p: TestExpr, input: String) {
        assert_eq!(
            maybe::<_, ()>(&p).parse(&input),
            Ok(match p {
                ParseMatch(config, _) =>
                    Span::new(config.range(), Some(Span::new(config.range(), TestValue))),
                ParseError(_) => Span::new(0..0, None),
            })
        );
    }
}
