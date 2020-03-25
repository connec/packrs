use core::iter::FromIterator;

use crate::combinators::*;
use crate::expression::ExpectedEndOfInput;
use crate::parser::Parser;
use crate::span::Span;

/// A trait for convenience methods on parsers.
pub trait ParserExt {
    /// Construct a parser from a `Vec` of parser.
    ///
    /// See [`all_of`] and [`AllOf`] for more details.
    ///
    /// [`all_of`]: ../fn.all_of.html
    /// [`AllOf`]: ../expression/struct.AllOf.html
    fn all_of<'i, 'p, P>(self) -> BoxedParser<'i, 'p, Vec<Span<P::Value>>, P::Error>
    where
        Self: IntoIterator<Item = P> + Sized + 'p,
        P: Parser<'i> + 'p,
    {
        all_of(self.into_iter().collect())
    }

    /// Map this parser to one that discards successful results and consumes no input.
    ///
    /// See [`check`] and [`Check`] for more details.
    ///
    /// [`check`]: ../fn.check.html
    /// [`Check`]: ../expression/struct.Check.html
    fn check<'i, 'p>(self) -> BoxedParser<'i, 'p, (), Self::Error>
    where
        Self: Parser<'i> + Sized + 'p,
    {
        check(self)
    }

    /// Map this parser to one that fails if there is remaining input.
    ///
    /// See [`end_of_input`] and [`EndOfInput`] for more details.
    ///
    /// [`end_of_input`]: ../fn.end_of_input.html
    /// [`EndOfInput`]: ../expression/struct.EndOfInput.html
    fn end<'i, 'p, E>(self) -> BoxedParser<'i, 'p, Self::Value, E>
    where
        Self: Parser<'i> + Sized + 'p,
        E: From<Self::Error> + From<ExpectedEndOfInput> + 'p,
        'i: 'p,
    {
        map(join(self, end_of_input()), |(value, _)| value.take())
    }

    /// Map this parser to one producing a different value.
    ///
    /// See [`map`] and [`Map`] for more details.
    ///
    /// [`map`]: ../fn.map.html
    /// [`Map`]: ../expression/struct.Map.html
    fn map<'i, 'p, F, U>(self, transform: F) -> BoxedParser<'i, 'p, U, Self::Error>
    where
        Self: Parser<'i> + Sized + 'p,
        F: Fn(Self::Value) -> U + 'p,
    {
        map(self, transform)
    }

    /// Map this parser to one producing a different error.
    ///
    /// See [`map_err`] and [`MapErr`] for more details.
    ///
    /// [`map_err`]: ../fn.map_err.html
    /// [`MapErr`]: ../expression/struct.MapErr.html
    fn map_err<'i, 'p, F, U>(self, transform: F) -> BoxedParser<'i, 'p, Self::Value, U>
    where
        Self: Parser<'i> + Sized + 'p,
        F: Fn(Self::Error) -> U + 'p,
    {
        map_err(self, transform)
    }

    /// Convert this parser to one that produces an `Option`, with `None` replacing errors.
    ///
    /// See [`maybe`] and [`Maybe`] for more details.
    ///
    /// [`maybe`]: ../fn.maybe.html
    /// [`Maybe`]: ../expression/struct.Maybe.html
    fn maybe<'i, 'p, E>(self) -> BoxedParser<'i, 'p, Option<Span<Self::Value>>, E>
    where
        Self: Parser<'i> + Sized + 'p,
        E: 'p,
    {
        maybe(self)
    }

    /// Convert this parser to one that parses repeatedly, returning a `Vec` of results.
    ///
    /// See [`maybe_repeat`] and [`MaybeRepeat`] for more details.
    ///
    /// [`maybe_repeat`]: ../fn.maybe_repeat.html
    /// [`MaybeRepeat`]: ../expression/struct.MaybeRepeat.html
    fn maybe_repeat<'i, 'p, E>(self) -> BoxedParser<'i, 'p, Vec<Span<Self::Value>>, E>
    where
        Self: Parser<'i> + Sized + 'p,
        E: 'p,
    {
        maybe_repeat(self)
    }

    /// Construct a parser from a `Vec` of parser.
    ///
    /// See [`one_of`] and [`OneOf`] for more details.
    ///
    /// [`one_of`]: ../fn.one_of.html
    /// [`OneOf`]: ../expression/struct.OneOf.html
    fn one_of<'i, 'p, P>(self) -> BoxedParser<'i, 'p, P::Value, Vec<Span<P::Error>>>
    where
        Self: IntoIterator<Item = P> + Sized + 'p,
        P: Parser<'i> + 'p,
    {
        one_of(self.into_iter().collect())
    }

    /// Convert this parser to one that inverts the result, discarding values and consuming no
    /// input.
    ///
    /// See [`reject`] and [`Reject`] for more details.
    ///
    /// [`reject`]: ../fn.reject.html
    /// [`Reject`]: ../expression/struct.Reject.html
    fn reject<'i, 'p>(self) -> BoxedParser<'i, 'p, (), ()>
    where
        Self: Parser<'i> + Sized + 'p,
    {
        reject(self)
    }

    /// Convert this parser to one that parses repeatedly, returning a `Vec` of results. If parsing
    /// doesn't succeed at least once, the error will be returned.
    ///
    /// See [`repeat`] and [`Repeat`] for more details.
    ///
    /// [`repeat`]: ../fn.repeat.html
    /// [`Repeat`]: ../expression/struct.Repeat.html
    fn repeat<'i, 'p>(self) -> BoxedParser<'i, 'p, Vec<Span<Self::Value>>, Self::Error>
    where
        Self: Parser<'i> + Sized + 'p,
    {
        repeat(self)
    }

    /// Convert this parser to one that collects its result.
    ///
    /// This is paricularly useful for processing the results of [`all_of`], [`maybe_repeat`],
    /// [`one_of`], and [`repeat`].
    ///
    /// [`all_of`]: ../combinators/fn.all_of.html
    /// [`maybe_repeat`]: ../combinators/fn.maybe_repeat.html
    /// [`one_of`]: ../combinators/fn.one_of.html
    /// [`repeat`]: ../combinators/fn.repeat.html
    fn collect<'i, 'p, C, I>(self) -> BoxedParser<'i, 'p, C, Self::Error>
    where
        Self: Parser<'i> + Sized + 'p,
        Self::Value: IntoIterator<Item = Span<I>>,
        C: FromIterator<I>,
    {
        self.map(|v| v.into_iter().map(|i| i.take()).collect())
    }
}

impl<'i, P> ParserExt for P where P: Parser<'i> {}
impl<'i, P> ParserExt for Vec<P> where P: Parser<'i> {}

#[cfg(test)]
mod tests {
    use crate::combinators::any;
    use crate::expression::{ExpectedEndOfInput, UnexpectedEndOfInput};
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
    fn test_check() {
        let expr = any().check();

        assert_eq!(expr.parse("÷"), Ok(Span::new(0..0, ())));
    }

    #[test]
    fn test_end() {
        #[derive(Debug, PartialEq)]
        enum Error {
            ExpectedEndOfInput,
            UnexpectedEndOfInput,
        }

        impl From<ExpectedEndOfInput> for Error {
            fn from(_: ExpectedEndOfInput) -> Self {
                Error::ExpectedEndOfInput
            }
        }

        impl From<UnexpectedEndOfInput> for Error {
            fn from(_: UnexpectedEndOfInput) -> Self {
                Error::UnexpectedEndOfInput
            }
        }

        let expr = any().end();

        assert_eq!(expr.parse("न"), Ok(Span::new(0..3, "न")));
        assert_eq!(
            expr.parse("नि"),
            Err(Span::new(3..6, Error::ExpectedEndOfInput))
        );
    }

    #[test]
    fn test_map() {
        let expr = any().map(|c| c.len());

        assert_eq!(expr.parse("÷"), Ok(Span::new(0..2, 2)));
    }

    #[test]
    fn test_map_err() {
        let expr = any().map_err(|_| "oh well");

        assert_eq!(expr.parse(""), Err(Span::new(0..0, "oh well")));
    }

    #[test]
    fn test_maybe() {
        let expr = any().maybe::<()>();

        assert_eq!(expr.parse(""), Ok(Span::new(0..0, None)));
    }

    #[test]
    fn test_maybe_repeat() {
        let expr = any().maybe_repeat::<()>();

        assert_eq!(expr.parse(""), Ok(Span::new(0..0, vec![])));
        assert_eq!(
            expr.parse("÷"),
            Ok(Span::new(0..2, vec![Span::new(0..2, "÷")]))
        );
        assert_eq!(
            expr.parse("1÷2"),
            Ok(Span::new(
                0..4,
                vec![
                    Span::new(0..1, "1"),
                    Span::new(1..3, "÷"),
                    Span::new(3..4, "2"),
                ]
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

    #[test]
    fn test_reject() {
        let expr = any().reject();

        assert_eq!(expr.parse("÷"), Err(Span::new(0..0, ())));
        assert_eq!(expr.parse(""), Ok(Span::new(0..0, ())));
    }

    #[test]
    fn test_repeat() {
        let expr = any().repeat();

        assert_eq!(expr.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
        assert_eq!(
            expr.parse("÷"),
            Ok(Span::new(0..2, vec![Span::new(0..2, "÷")]))
        );
        assert_eq!(
            expr.parse("1÷2"),
            Ok(Span::new(
                0..4,
                vec![
                    Span::new(0..1, "1"),
                    Span::new(1..3, "÷"),
                    Span::new(3..4, "2"),
                ]
            ))
        );
    }

    #[test]
    fn test_collect() {
        let expr = any().repeat().collect();

        assert_eq!(
            expr.parse("hello"),
            Ok(Span::new(0..5, "hello".to_string()))
        );
    }
}
