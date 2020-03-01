//! Parsing expressions based on a [`Parser`] trait.
//!
//! [`Parser`]: trait.Parser.html

use core::cmp::{max, min};
use core::convert::Infallible;

use Error::*;

/// Represents a `value` at a given `span` of an input.
#[derive(Debug, PartialEq)]
pub struct Span<T> {
    start: usize,
    end: usize,
    value: T,
}

impl<T> Span<T> {
    fn new(start: usize, end: usize, value: T) -> Self {
        Span { start, end, value }
    }

    fn relative_to(mut self, end: usize) -> Self {
        self.start += end;
        self.end += end;
        self
    }
}

#[cfg(test)]
mod test_value {
    use super::Span;

    #[test]
    fn relative_to() {
        let value = Span::new(0, 10, ());
        assert_eq!(value.relative_to(5), Span::new(5, 15, ()));
    }
}

/// Represents the reasons the `Parser`s in this module might fail.
#[derive(Debug, PartialEq)]
pub enum Error {
    /// Indicates that parsing failed because more input was expected.
    UnexpectedEndOfInput,

    /// Indicates that parsing failed because an expected character wasn't present.
    ExpectedChar(char),
}

/// A trait for convenience methods on parse results.
trait ParseResult<V, E> {
    fn relative_to(self, end: usize) -> Result<Span<V>, Span<E>>;
}

impl<V, E> ParseResult<V, E> for Result<Span<V>, Span<E>> {
    fn relative_to(self, end: usize) -> Self {
        self.map(|value| value.relative_to(end))
            .map_err(|value| value.relative_to(end))
    }
}

/// A trait implemented by parsing expressions.
pub trait Parser<'a> {
    /// The type returned in successful parse results.
    type Value;

    /// The type returned in failed parse results.
    type Error;

    /// Parse a given input and produce a result.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>>;
}

impl<'a, P, V, E> Parser<'a> for &P
where
    P: Parser<'a, Value = V, Error = E> + ?Sized,
{
    type Value = V;
    type Error = E;

    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        (*self).parse(input)
    }
}

/// An expression for parsing nothing.
pub struct Nothing;

impl<'a> Parser<'a> for Nothing {
    type Value = ();
    type Error = Infallible;

    /// Parse nothing.
    ///
    /// This always succeeds without consuming input. It can be useful in combinators when 'nothing' is
    /// an allowed value.
    fn parse(&self, _input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(Span::new(0, 0, ()))
    }
}

#[cfg(test)]
mod test_nothing {
    use super::*;

    #[test]
    fn ok_if_input_is_empty() {
        assert_eq!(Nothing.parse(""), Ok(Span::new(0, 0, ())));
    }

    #[test]
    fn ok_if_input_is_non_empty() {
        assert_eq!(Nothing.parse("hello"), Ok(Span::new(0, 0, ())));
    }
}

/// An expression for parsing an arbitrary character.
pub struct Any;

impl<'a> Parser<'a> for Any {
    type Value = &'a str;
    type Error = Error;

    /// Parse an arbitrary character from an `&str`.
    ///
    /// If the input is empty, this will fail with [`UnexpectedEndOfInput`]. Otherwise, the result will
    /// be a `&str` containing the first character of the string.
    ///
    /// [`UnexpectedEndOfInput`]: enum.Error.html#variant.UnexpectedEndOfInput
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let actual = input
            .chars()
            .next()
            .ok_or_else(|| Span::new(0, 0, UnexpectedEndOfInput))?;
        let len = actual.len_utf8();
        Ok(Span::new(0, len, &input[0..len]))
    }
}

#[cfg(test)]
mod test_any {
    use super::*;

    #[test]
    fn ok_if_input_is_non_empty() {
        assert_eq!(Any.parse("hello"), Ok(Span::new(0, 1, "h")));
    }

    #[test]
    fn ok_if_input_begins_with_multibyte_char() {
        assert_eq!(Any.parse("\u{306}"), Ok(Span::new(0, 2, "\u{306}")));
    }

    #[test]
    fn err_if_input_is_empty() {
        assert_eq!(Any.parse(""), Err(Span::new(0, 0, UnexpectedEndOfInput)));
    }
}

/// An expression for parsing a specific character.
pub struct Char(char);

impl<'a> Parser<'a> for Char {
    type Value = &'a str;
    type Error = Error;

    /// Parse a specific character from an `&str`.
    ///
    /// If the the input begins with the character then the successful result will contain the
    /// matched slice of the input. Otherwise, an [`ExpectedChar`] error is returned.
    ///
    /// [`ExpectedChar`]: enum.Error.html#variant.ExpectedChar
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let actual = input
            .chars()
            .next()
            .ok_or_else(|| Span::new(0, 0, ExpectedChar(self.0)))?;
        let len = actual.len_utf8();
        if actual != self.0 {
            Err(Span::new(0, len, ExpectedChar(self.0)))
        } else {
            Ok(Span::new(0, len, &input[0..len]))
        }
    }
}

#[cfg(test)]
mod test_char {
    use super::*;

    #[test]
    fn ok_if_input_matches() {
        assert_eq!(Char('h').parse("hello"), Ok(Span::new(0, 1, "h")));
    }

    #[test]
    fn multibyte_ok_if_input_matches() {
        assert_eq!(
            Char('\u{306}').parse("\u{306}"),
            Ok(Span::new(0, 2, "\u{306}"))
        );
    }

    #[test]
    fn err_if_input_is_empty() {
        assert_eq!(Char('h').parse(""), Err(Span::new(0, 0, ExpectedChar('h'))));
    }

    #[test]
    fn err_if_input_does_not_match() {
        assert_eq!(
            Char('h').parse("world"),
            Err(Span::new(0, 1, ExpectedChar('h')))
        );
    }

    #[test]
    fn err_if_multibyte_input_does_not_match() {
        assert_eq!(
            Char('y').parse("\u{306}"),
            Err(Span::new(0, 2, ExpectedChar('y')))
        );
    }
}

/// An expression for parsing a sequence of sub-expressions.
pub struct Sequence<P>(Vec<P>);

impl<'a, P> Parser<'a> for Sequence<P>
where
    P: Parser<'a>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = P::Error;

    /// Parse a sequence of sub-expressions.
    ///
    /// Parsing succeeds if all sub-expressions succeed, and the result is a `Vec` of the
    /// sub-expression results. If any sub-expression fails, the failure is returned and any results
    /// up to that point are dropped.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let mut end = 0;
        let mut values = Vec::with_capacity(self.0.len());

        for expr in self.0.iter() {
            let value = expr.parse(&input[end..]).relative_to(end)?;
            end = value.end;
            values.push(value);
        }

        Ok(Span::new(0, end, values))
    }
}

#[cfg(test)]
mod test_sequence {
    use super::*;

    #[test]
    fn ok_if_all_match() {
        let expr = Sequence::<&dyn Parser<Value = _, Error = _>>(vec![&Any, &Char('e')]);
        assert_eq!(
            expr.parse("hello"),
            Ok(Span::new(
                0,
                2,
                vec![Span::new(0, 1, "h"), Span::new(1, 2, "e")]
            ))
        );
    }

    #[test]
    fn ok_with_multibyte_input() {
        let expr = Sequence(vec![Any, Any]);
        assert_eq!(
            expr.parse("y̆"),
            Ok(Span::new(
                0,
                3,
                vec![Span::new(0, 1, "y"), Span::new(1, 3, "\u{306}")]
            ))
        );
    }

    #[test]
    fn err_if_first_expr_fails() {
        let expr = Sequence(vec![Char('a'), Char('b')]);
        assert_eq!(expr.parse("hello"), Err(Span::new(0, 1, ExpectedChar('a'))));
    }

    #[test]
    fn err_if_any_expr_fails() {
        let expr = Sequence("hello".chars().map(Char).collect());
        assert_eq!(expr.parse("help"), Err(Span::new(3, 4, ExpectedChar('l'))));
    }
}

/// An expression that returns the first successful match from a sequence of sub-expressions.
pub struct OrderedChoice<P>(Vec<P>);

impl<'a, P> Parser<'a> for OrderedChoice<P>
where
    P: Parser<'a>,
{
    type Value = P::Value;
    type Error = Vec<Span<P::Error>>;

    /// Parse a sequence of sub-expressions, returning the result of the first one that succeeds.
    ///
    /// Parsing succeeds if any sub-expression succeeds, and the result is the result of the
    /// successful sub-expression (any preceeding failures are dropped). If all sub-expressions
    /// fail, all the failures are returned.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let mut start = usize::max_value();
        let mut end = 0;
        let mut errors = Vec::new();

        for expr in self.0.iter() {
            let error = match expr.parse(input) {
                Ok(value) => return Ok(value),
                Err(error) => error,
            };
            start = min(start, error.start);
            end = max(end, error.end);
            errors.push(error);
        }

        Err(Span::new(0, end, errors))
    }
}

#[cfg(test)]
mod test_ordered_choice {
    use super::*;

    #[test]
    fn ok_if_first_expr_matches() {
        let expr = OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![&Any, &Char('a')]);
        assert_eq!(expr.parse("hello"), Ok(Span::new(0, 1, "h")));
    }

    #[test]
    fn ok_if_any_expr_matches() {
        let expr = OrderedChoice(vec![Char('a'), Char('b'), Char('c')]);
        assert_eq!(expr.parse("cello"), Ok(Span::new(0, 1, "c")));
    }

    #[test]
    fn err_if_all_exprs_err() {
        let expr = OrderedChoice(vec![Char('a'), Char('b'), Char('c')]);
        assert_eq!(
            expr.parse("dello"),
            Err(Span::new(
                0,
                1,
                vec![
                    Span::new(0, 1, ExpectedChar('a')),
                    Span::new(0, 1, ExpectedChar('b')),
                    Span::new(0, 1, ExpectedChar('c'))
                ]
            ))
        );
    }
}

/// An expression that matches a sub-expression as many times as it can.
pub struct ZeroOrMore<P>(P);

impl<'a, P> Parser<'a> for ZeroOrMore<P>
where
    P: Parser<'a>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = Infallible;
    /// Repeatedly parse the sub-expression until it fails, returning an array of the sucessful
    /// results.
    ///
    /// Parsing never fails.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let mut end = 0;
        let mut values = Vec::new();

        while let Ok(value) = self.0.parse(&input[end..]).relative_to(end) {
            end = value.end;
            values.push(value);
        }

        Ok(Span::new(0, end, values))
    }
}

#[cfg(test)]
mod test_zero_or_more {
    use super::*;

    #[test]
    fn ok_if_no_matches() {
        assert_eq!(ZeroOrMore(Any).parse(""), Ok(Span::new(0, 0, vec![])));
    }

    #[test]
    fn ok_if_one_match() {
        assert_eq!(
            ZeroOrMore(Char('a')).parse("ab"),
            Ok(Span::new(0, 1, vec![Span::new(0, 1, "a")]))
        );
    }

    #[test]
    fn ok_if_many_matches() {
        assert_eq!(
            ZeroOrMore(Char('a')).parse("aaaaab"),
            Ok(Span::new(
                0,
                5,
                vec![
                    Span::new(0, 1, "a"),
                    Span::new(1, 2, "a"),
                    Span::new(2, 3, "a"),
                    Span::new(3, 4, "a"),
                    Span::new(4, 5, "a"),
                ]
            ))
        );
    }
}

/// An expression that matches a sub-expression at least once, then as many times as it can.
pub struct OneOrMore<P>(P);

impl<'a, P> Parser<'a> for OneOrMore<P>
where
    P: Parser<'a>,
{
    type Value = Vec<Span<P::Value>>;
    type Error = P::Error;
    /// Repeatedly parse the sub-expression until it fails, returning an array of the sucessful
    /// results.
    ///
    /// This fails if the first attempt to match the sub-expression fails, returning the failure.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        let value = self.0.parse(input)?;
        let mut end = value.end;
        let mut values = vec![value];

        while let Ok(value) = self.0.parse(&input[end..]).relative_to(end) {
            end = value.end;
            values.push(value);
        }

        Ok(Span::new(0, end, values))
    }
}

#[cfg(test)]
mod test_one_or_more {
    use super::*;

    #[test]
    fn err_if_no_matches() {
        assert_eq!(
            OneOrMore(Any).parse(""),
            Err(Span::new(0, 0, UnexpectedEndOfInput))
        );
    }

    #[test]
    fn ok_if_one_match() {
        assert_eq!(
            OneOrMore(Char('a')).parse("ab"),
            Ok(Span::new(0, 1, vec![Span::new(0, 1, "a")]))
        );
    }

    #[test]
    fn ok_if_many_matches() {
        assert_eq!(
            OneOrMore(Char('a')).parse("aaaaab"),
            Ok(Span::new(
                0,
                5,
                vec![
                    Span::new(0, 1, "a"),
                    Span::new(1, 2, "a"),
                    Span::new(2, 3, "a"),
                    Span::new(3, 4, "a"),
                    Span::new(4, 5, "a"),
                ]
            ))
        );
    }
}

/// An expression that tries to match a sub-expression, and succeeds regardless.
pub struct Optional<P>(P);

impl<'a, P> Parser<'a> for Optional<P>
where
    P: Parser<'a>,
{
    type Value = Option<Span<P::Value>>;
    type Error = Infallible;
    /// Attempt to parse the sub-expression and succeed with an `Option`, depending on the result.
    ///
    /// This always succeeds, returning `Some` containing the successful result or `None` if the
    /// sub-expression fails.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(match self.0.parse(input) {
            Ok(value) => Span::new(value.start, value.end, Some(value)),
            Err(_) => Span::new(0, 0, None),
        })
    }
}

#[cfg(test)]
mod test_optional {
    use super::*;

    #[test]
    fn ok_if_empty() {
        assert_eq!(Optional(Any).parse(""), Ok(Span::new(0, 0, None)));
    }

    #[test]
    fn ok_if_no_matches() {
        assert_eq!(Optional(Char('a')).parse("ba"), Ok(Span::new(0, 0, None)));
    }

    #[test]
    fn ok_if_match() {
        assert_eq!(
            Optional(Char('a')).parse("aab"),
            Ok(Span::new(0, 1, Some(Span::new(0, 1, "a"))))
        );
    }
}

/// An expression that tries to match a sub-expression, producing no result and consuming no input.
pub struct AndPredicate<P>(P);

impl<'a, P> Parser<'a> for AndPredicate<P>
where
    P: Parser<'a>,
{
    type Value = ();
    type Error = P::Error;
    /// Attempt to parse the sub-expression, and return an empty value on success.
    ///
    /// If matching the sub-expression fails, the failure is returned verbatim. If the
    /// sub-expression succeeds, the value is discarded and an empty `Span` is returned.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0.parse(input).map(|_| Span::new(0, 0, ()))
    }
}

#[cfg(test)]
mod test_and_predicate {
    use super::*;

    #[test]
    fn err_if_no_match() {
        assert_eq!(
            AndPredicate(Char('a')).parse("b"),
            Err(Span::new(0, 1, ExpectedChar('a')))
        );
    }

    #[test]
    fn ok_if_match() {
        assert_eq!(
            AndPredicate(Char('a')).parse("aab"),
            Ok(Span::new(0, 0, ()))
        );
    }
}

/// An expression that tries to match a sub-expression, producing no result and consuming no input.
pub struct NotPredicate<P>(P);

impl<'a, P> Parser<'a> for NotPredicate<P>
where
    P: Parser<'a>,
{
    type Value = ();
    type Error = ();

    /// Attempt to parse the sub-expression, and succeed if the sub-expression fails.
    ///
    /// If matching the sub-expression succeeds, a an empty failure is returned. If the
    /// sub-expression succeeds, and empty success is returned.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0
            .parse(input)
            .map_or_else(|_| Ok(Span::new(0, 0, ())), |_| Err(Span::new(0, 0, ())))
    }
}

#[cfg(test)]
mod test_not_predicate {
    use super::*;

    #[test]
    fn ok_if_no_matche() {
        assert_eq!(NotPredicate(Char('a')).parse("b"), Ok(Span::new(0, 0, ())));
    }

    #[test]
    fn err_if_match() {
        assert_eq!(
            NotPredicate(Char('a')).parse("aab"),
            Err(Span::new(0, 0, ()))
        );
    }
}

/// An expression that transforms a successful sub-expression result.
pub struct Map<P, F>(P, F);

impl<'a, P, F, V, U> Parser<'a> for Map<P, F>
where
    P: Parser<'a, Value = V>,
    F: Fn(V) -> U,
{
    type Value = U;
    type Error = P::Error;
    /// Attempt to parse the sub-expression, and map the result on success.
    ///
    /// If the sub-expression fails, the failure is returned verbatim.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0
            .parse(input)
            .map(|value| Span::new(value.start, value.end, self.1(value.value)))
    }
}

#[cfg(test)]
mod test_map {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn err_if_no_match() {
        assert_eq!(
            Map(Any, |_| ()).parse(""),
            Err(Span::new(0, 0, UnexpectedEndOfInput))
        );
    }

    #[test]
    fn fn_not_called_if_no_match() {
        let called = Cell::new(false);
        let f = |_| called.set(true);
        let _ = Map(Any, f).parse("");
        assert_eq!(called.get(), false);
    }

    #[test]
    fn ok_if_match() {
        fn map(value: Vec<Span<&str>>) -> String {
            value.into_iter().map(|Span { value, .. }| value).collect()
        }
        assert_eq!(
            Map(Sequence(vec![Any, Any]), map).parse("y̆"),
            Ok(Span::new(0, 3, "y̆".to_string()))
        );
    }
}

/// An expression that transforms a failed sub-expression result.
pub struct MapErr<P, F>(P, F);

impl<'a, P, F, E, U> Parser<'a> for MapErr<P, F>
where
    P: Parser<'a, Error = E>,
    F: Fn(E) -> U,
{
    type Value = P::Value;
    type Error = U;
    /// Attempt to parse the sub-expression, and map the result on failure.
    ///
    /// If the sub-expression succeeds, the result is returned verbatim.
    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.0
            .parse(input)
            .map_err(|value| Span::new(value.start, value.end, self.1(value.value)))
    }
}

#[cfg(test)]
mod test_map_err {
    use super::*;
    use std::cell::Cell;

    #[test]
    fn transforms_err() {
        assert_eq!(MapErr(Any, |_| ()).parse(""), Err(Span::new(0, 0, ())));
    }

    #[test]
    fn no_transform_if_match() {
        assert_eq!(MapErr(Any, |_| ()).parse("a"), Ok(Span::new(0, 1, "a")));
    }

    #[test]
    fn fn_not_called_if_match() {
        let called = Cell::new(false);
        let f = |_| called.set(true);
        let _ = MapErr(Any, f).parse("a");
        assert_eq!(called.get(), false);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_calculator() {
        #[derive(Debug, PartialEq)]
        enum Token {
            Num(i8),
            OpAdd,
            OpSub,
        }

        #[derive(Debug, PartialEq)]
        enum Expr {
            Num(i8),
            Add(Span<i8>, Span<i8>),
        }

        #[derive(Debug, PartialEq)]
        enum CalcError {
            InvalidNumber,
            InvalidOperator,
        }

        let num = MapErr(
            OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![
                &Map(Char('1'), |_| Token::Num(1)),
                &Map(Char('2'), |_| Token::Num(2)),
            ]),
            |_| CalcError::InvalidNumber,
        );
        let op = MapErr(
            OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![
                &Map(Char('+'), |_| Token::OpAdd),
                &Map(Char('-'), |_| Token::OpSub),
            ]),
            |_| CalcError::InvalidOperator,
        );
        let add = Map(
            Sequence::<&dyn Parser<Value = _, Error = _>>(vec![&num, &op, &num]),
            |mut seq: Vec<Span<Token>>| {
                let mut seq = seq.drain(0..3);
                let Span {
                    start: start_a,
                    end: end_a,
                    value: a,
                } = seq.next().unwrap();
                let op = seq.next().unwrap().value;
                let Span {
                    start: start_b,
                    end: end_b,
                    value: b,
                } = seq.next().unwrap();

                let a = match a {
                    Token::Num(a) => Span::new(start_a, end_a, a),
                    _ => unreachable!(),
                };
                let b = match (op, b) {
                    (Token::OpAdd, Token::Num(b)) => Span::new(start_b, end_b, b),
                    (Token::OpSub, Token::Num(b)) => Span::new(start_b, end_b, -b),
                    _ => unreachable!(),
                };

                Expr::Add(a, b)
            },
        );
        let expr_num = Map(&num, |token| match token {
            Token::Num(n) => Expr::Num(n),
            _ => unreachable!(),
        });
        let expr = OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![&add, &expr_num]);

        assert_eq!(
            expr.parse("1"),
            Ok(Span {
                start: 0,
                end: 1,
                value: Expr::Num(1)
            })
        );
        assert_eq!(
            expr.parse("2"),
            Ok(Span {
                start: 0,
                end: 1,
                value: Expr::Num(2)
            })
        );
        assert_eq!(
            expr.parse("1+2"),
            Ok(Span {
                start: 0,
                end: 3,
                value: Expr::Add(
                    Span {
                        start: 0,
                        end: 1,
                        value: 1
                    },
                    Span {
                        start: 2,
                        end: 3,
                        value: 2
                    }
                )
            })
        );
        assert_eq!(
            expr.parse("1-2"),
            Ok(Span {
                start: 0,
                end: 3,
                value: Expr::Add(
                    Span {
                        start: 0,
                        end: 1,
                        value: 1
                    },
                    Span {
                        start: 2,
                        end: 3,
                        value: -2
                    }
                )
            })
        );
        assert_eq!(
            expr.parse("wow"),
            Err(Span {
                start: 0,
                end: 1,
                value: vec![
                    Span {
                        start: 0,
                        end: 1,
                        value: CalcError::InvalidNumber
                    },
                    Span {
                        start: 0,
                        end: 1,
                        value: CalcError::InvalidNumber
                    }
                ]
            })
        );
    }
}
