use crate::expression::all_of::{all_of, AllOf};
use crate::expression::check::{check, Check};
use crate::expression::end_of_input::{end_of_input, ExpectedEndOfInput};
use crate::expression::join::join;
use crate::expression::map::{map, Map};
use crate::expression::map_err::{map_err, MapErr};
use crate::expression::maybe::{maybe, Maybe};
use crate::expression::maybe_repeat::{maybe_repeat, MaybeRepeat};
use crate::expression::one_of::{one_of, OneOf};
use crate::expression::reject::{reject, Reject};
use crate::expression::repeat::{repeat, Repeat};
use core::iter::FromIterator;

use crate::parser::Parser;
use crate::span::Span;

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

    /// Map this parser to one that discards successful results and consumes no input.
    ///
    /// See [`check`](crate::check) for more details.
    ///
    /// [`check`]: ../fn.check.html
    /// [`Check`]: ../expression/struct.Check.html
    fn check<'i>(self) -> Check<Self>
    where
        Self: Parser<'i> + Sized,
    {
        check(self)
    }

    /// Map this parser to one that fails if there is remaining input.
    ///
    /// See [`end_of_input`](crate::end_of_input) for more details.
    ///
    /// [`end_of_input`]: ../fn.end_of_input.html
    /// [`EndOfInput`]: ../expression/struct.EndOfInput.html
    fn end<'i, 'p, E>(self) -> Box<dyn Parser<'i, Value = Self::Value, Error = E> + 'p>
    where
        Self: Parser<'i> + Sized + 'p,
        E: From<Self::Error> + From<ExpectedEndOfInput> + 'p,
        'i: 'p,
    {
        map(
            join(self.map_err(E::from), end_of_input().map_err(E::from)),
            |(value, _)| value.take(),
        )
        .boxed()
    }

    /// Map this parser to one producing a different value.
    ///
    /// See [`map`](crate::map) for more details.
    ///
    /// [`map`]: ../fn.map.html
    /// [`Map`]: ../expression/struct.Map.html
    fn map<'i, F, U>(self, transform: F) -> Map<Self, F>
    where
        Self: Parser<'i> + Sized,
        F: Fn(Self::Value) -> U,
    {
        map(self, transform)
    }

    /// Map this parser to one producing a different error.
    ///
    /// See [`map_err`](crate::map_err) for more details.
    ///
    /// [`map_err`]: ../fn.map_err.html
    /// [`MapErr`]: ../expression/struct.MapErr.html
    fn map_err<'i, F, U>(self, transform: F) -> MapErr<Self, F>
    where
        Self: Parser<'i> + Sized,
        F: Fn(Self::Error) -> U,
    {
        map_err(self, transform)
    }

    /// Convert this parser to one that produces an `Option`, with `None` replacing errors.
    ///
    /// See [`maybe`](crate::maybe) for more details.
    ///
    /// [`maybe`]: ../fn.maybe.html
    /// [`Maybe`]: ../expression/struct.Maybe.html
    fn maybe<'i, E>(self) -> Maybe<Self, E>
    where
        Self: Parser<'i> + Sized,
    {
        maybe(self)
    }

    /// Convert this parser to one that parses repeatedly, returning a `Vec` of results.
    ///
    /// See [`maybe_repeat`](crate::maybe_repeat) for more details.
    ///
    /// [`maybe_repeat`]: ../fn.maybe_repeat.html
    /// [`MaybeRepeat`]: ../expression/struct.MaybeRepeat.html
    fn maybe_repeat<'i, E>(self) -> MaybeRepeat<Self, E>
    where
        Self: Parser<'i> + Sized,
    {
        maybe_repeat(self)
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

    /// Convert this parser to one that inverts the result, discarding values and consuming no
    /// input.
    ///
    /// See [`reject`](crate::reject) for more details.
    ///
    /// [`reject`]: ../fn.reject.html
    /// [`Reject`]: ../expression/struct.Reject.html
    fn reject<'i>(self) -> Reject<Self>
    where
        Self: Parser<'i> + Sized,
    {
        reject(self)
    }

    /// Convert this parser to one that parses repeatedly, returning a `Vec` of results. If parsing
    /// doesn't succeed at least once, the error will be returned.
    ///
    /// See [`repeat`](crate::repeat) for more details.
    ///
    /// [`repeat`]: ../fn.repeat.html
    /// [`Repeat`]: ../expression/struct.Repeat.html
    fn repeat<'i>(self) -> Repeat<Self>
    where
        Self: Parser<'i> + Sized,
    {
        repeat(self)
    }

    /// Convert this parser to one that collects its result.
    ///
    /// This is paricularly useful for processing the results of [`all_of`](crate::all_of),
    /// [`maybe_repeat`](crate::maybe_repeat), [`one_of`](crate::one_of), and
    /// [`repeat`](crate::repeat).
    fn collect<'i, 'p, C, I>(self) -> Box<dyn Parser<'i, Value = C, Error = Self::Error> + 'p>
    where
        Self: Parser<'i> + Sized + 'p,
        Self::Value: IntoIterator<Item = Span<I>>,
        C: FromIterator<I>,
    {
        self.map(|v| v.into_iter().map(|i| i.take()).collect())
            .boxed()
    }
}

impl<'i, P> ParserExt for P where P: Parser<'i> {}
impl<'i, P> ParserExt for Vec<P> where P: Parser<'i> {}

#[cfg(test)]
mod tests {
    use crate::expression::any::{any, UnexpectedEndOfInput};
    use crate::expression::end_of_input::ExpectedEndOfInput;
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
