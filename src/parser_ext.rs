use crate::expression::all_of::{all_of, AllOf};
use crate::expression::one_of::{one_of, OneOf};

use crate::parser::Parser;

/// A trait for convenience methods on parsers.
pub trait ParserExt {
    /// Construct a parser from a `Vec` of parser.
    ///
    /// See [`all_of`](crate::all_of) for more details.
    fn all_of<'i, P>(self) -> AllOf<P>
    where
        Self: IntoIterator<Item = P> + Sized,
        P: Parser<'i>,
    {
        all_of(self.into_iter().collect())
    }

    /// Construct a parser from a `Vec` of parser.
    ///
    /// See [`one_of`](crate::one_of) for more details.
    ///
    /// [`one_of`]: ../fn.one_of.html
    /// [`OneOf`]: ../expression/struct.OneOf.html
    fn one_of<'i, P>(self) -> OneOf<P>
    where
        Self: IntoIterator<Item = P> + Sized,
        P: Parser<'i>,
    {
        one_of(self.into_iter().collect())
    }
}

impl<'i, P> ParserExt for Vec<P> where P: Parser<'i> {}

#[cfg(test)]
mod tests {
    use crate::expression::any::{any, UnexpectedEndOfInput};

    use crate::parser::Parser;
    use crate::span::Span;

    use super::ParserExt;

    #[test]
    fn test_all_of() {
        let expr = vec![any(), any()].all_of();

        assert_eq!(
            expr.parse("ab"),
            Ok(Span::new(
                0..2,
                vec![Span::new(0..1, "a"), Span::new(1..2, "b"),]
            ))
        );
    }

    #[test]
    fn test_one_of() {
        let expr = vec![any(), any()].one_of();

        assert_eq!(expr.parse("ab"), Ok(Span::new(0..1, "a")));
        assert_eq!(
            expr.parse(""),
            Err(Span::new(
                0..0,
                vec![
                    Span::new(0..0, UnexpectedEndOfInput),
                    Span::new(0..0, UnexpectedEndOfInput),
                ]
            ))
        );
    }
}
