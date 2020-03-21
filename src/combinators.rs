use core::convert::Infallible;

use crate::expression::*;
use crate::parser::Parser;
use crate::span::Span;

/// A convenience alias for a boxed parser.
///
/// The lifetimes on this are complicated by the need to distinguish the lifetime of the parser
/// (`'b`) from the lifetime of the input (`'a`).
pub type BoxedParser<'a, 'b, V, E> = Box<dyn Parser<'a, Value = V, Error = E> + 'b>;

/// Create a parser that will evaluate the given parsers in order against an input.
///
/// If all of the given parsers can be evaluated successfully, the result will be `Ok` with a `Vec`
/// of the successfully parsed values. If any parser fails, the result will be an `Err` with the
/// parse failure.
///
/// Note that all parsers must have the same `Value` and `Error` types. [`map`] and [`map_err`] can
/// be used to unify parser types.
///
/// ```
/// use packrs::{ExpectedChar, Span, all_of, chr};
///
/// let hello = all_of("hello".chars().map(chr).collect());
///
/// assert_eq!(hello.parse("hello world"), Ok(Span::new(0..5, vec![
///     Span::new(0..1, "h"),
///     Span::new(1..2, "e"),
///     Span::new(2..3, "l"),
///     Span::new(3..4, "l"),
///     Span::new(4..5, "o"),
/// ])));
///
/// assert_eq!(hello.parse("world"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
///
/// [`map`]: fn.map.html
/// [`map_err`]: fn.map_err.html
pub fn all_of<'a, 'b, P>(parsers: Vec<P>) -> BoxedParser<'a, 'b, Vec<Span<P::Value>>, P::Error>
where
    P: Parser<'a> + 'b,
{
    Box::new(AllOf(parsers))
}

/// Create a parser that consumes any single character.
///
/// When given a non-empty input, the result will be `Ok` with a subslice of the input containing
/// the first character.
///
/// When given an empty input, the result will be an `Err` with `UnexpectedEndOfInput`.
///
/// ```
/// use packrs::{ParserExt, Span, UnexpectedEndOfInput, all_of, any, chr, reject, repeat};
///
/// let first_word = repeat(
///     all_of(vec![
///         reject(chr(' ')).map(|_| "").map_err(|_| UnexpectedEndOfInput),
///         any(),
///     ])
///     .map(|mut v| v.pop().unwrap().take())
/// );
///
/// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, vec![
///     Span::new(0..1, "h"),
///     Span::new(1..2, "e"),
///     Span::new(2..3, "l"),
///     Span::new(3..4, "l"),
///     Span::new(4..5, "o"),
/// ])));
/// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
/// ```
pub fn any<'a, 'b>() -> BoxedParser<'a, 'b, &'a str, UnexpectedEndOfInput> {
    Box::new(Any)
}

/// Create a parser that will evaluate the given parser, without consuming any input.
///
/// If the given parser evaluates successfully, the result will be `Ok` with `()`. If the given
/// parser fails, the result will be an `Err` with the parse failure.
///
/// ```
/// use packrs::{ExpectedChar, Span, all_of, check, chr};
///
/// let check_hello = check(all_of("hello".chars().map(chr).collect()));
///
/// assert_eq!(check_hello.parse("hello world"), Ok(Span::new(0..0, ())));
/// assert_eq!(check_hello.parse("world, hello"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
pub fn check<'a, 'b, P>(parser: P) -> BoxedParser<'a, 'b, (), P::Error>
where
    P: Parser<'a> + 'b,
{
    Box::new(Check(parser))
}

/// Create a parser that consumes a specific character.
///
/// When given an input that starts with the given character, the result will be `Ok` with a
/// subslice of the input containing the character.
///
/// When given an input that does not start with the given character, the result will be an `Err`
/// with `ExpectedChar(char)`.
///
/// ```
/// use packrs::{ExpectedChar, Span, all_of, chr};
///
/// let hello = all_of("hello".chars().map(chr).collect());
///
/// assert_eq!(hello.parse("hello world"), Ok(Span::new(0..5, vec![
///     Span::new(0..1, "h"),
///     Span::new(1..2, "e"),
///     Span::new(2..3, "l"),
///     Span::new(3..4, "l"),
///     Span::new(4..5, "o"),
/// ])));
/// assert_eq!(hello.parse("world, hello"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
pub fn chr<'a, 'b>(char: char) -> BoxedParser<'a, 'b, &'a str, ExpectedChar> {
    Box::new(Chr(char))
}

/// Create a parser that will evaluate the given parser, and transform a successful result with the
/// given function.
///
/// If the given parser evaluates successfully, the result will be `Ok` with
/// `transform(<parsed value>)`. If the given parser fails, the result will be an `Err` with the
/// parse failure.
///
/// ```
/// use packrs::{ExpectedChar, Span, chr, map, one_of};
///
/// #[derive(Debug, PartialEq)]
/// enum Op {
///     Add,
///     Sub,
///     Mul,
///     Div,
/// }
///
/// let op = one_of(vec![
///     map(chr('+'), |_| Op::Add),
///     map(chr('-'), |_| Op::Sub),
///     map(chr('*'), |_| Op::Mul),
///     map(chr('/'), |_| Op::Div),
/// ]);
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
pub fn map<'a, 'b, P, F, V>(parser: P, transform: F) -> BoxedParser<'a, 'b, V, P::Error>
where
    P: Parser<'a> + 'b,
    F: Fn(P::Value) -> V + 'b,
{
    Box::new(Map(parser, transform))
}

/// Create a parser that will evaluate the given parser, and transform a failure with the given
/// function.
///
/// If the given parser evaluates successfully, the result will be `Ok` with the parsed value. If
/// the given parser fails, the result will be an `Err` with `transform(<parse failure>)`.
///
/// ```
/// use packrs::{ExpectedChar, ParserExt, Span, chr, map_err, one_of};
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
///     one_of(vec![
///         chr('+').map(|_| Op::Add),
///         chr('-').map(|_| Op::Sub),
///         chr('*').map(|_| Op::Mul),
///         chr('/').map(|_| Op::Div),
///     ]),
///     |_| InvalidOp
/// );
///
/// assert_eq!(op.parse("+"), Ok(Span::new(0..1, Op::Add)));
/// assert_eq!(op.parse("/"), Ok(Span::new(0..1, Op::Div)));
/// assert_eq!(op.parse("÷"), Err(Span::new(0..2, InvalidOp)));
/// ```
pub fn map_err<'a, 'b, P, F, E>(parser: P, transform: F) -> BoxedParser<'a, 'b, P::Value, E>
where
    P: Parser<'a> + 'b,
    F: Fn(P::Error) -> E + 'b,
{
    Box::new(MapErr(parser, transform))
}

/// Create a parser that will evaluate the given parser, converting the result into an `Option`.
///
/// This will always return `Ok`. If the given parser evaluates successfully, this will contain
/// `Some(<parsed value>)`. If the given parser fails, this will contain `None`.
///
/// ```
/// use packrs::{ExpectedChar, ParserExt, Span, all_of, chr, maybe};
///
/// let expr = all_of(vec![
///     chr('1').map(|s| s.to_string()),
///     maybe(all_of(vec![chr('+'), chr('1')]).map(|v| {
///         v.into_iter().map(|s| s.take()).collect::<String>()
///     }))
///         .map(|opt| match opt {
///             Some(span) => span.take(),
///             None => "".to_string(),
///         })
///         .map_err(|_| unreachable!()),
/// ]);
///
/// assert_eq!(expr.parse("1"), Ok(Span::new(0..1, vec![
///     Span::new(0..1, "1".to_string()),
///     Span::new(1..1, "".to_string())
/// ])));
/// assert_eq!(expr.parse("1+1"), Ok(Span::new(0..3, vec![
///     Span::new(0..1, "1".to_string()),
///     Span::new(1..3, "+1".to_string())
/// ])));
/// assert_eq!(expr.parse("2+1"), Err(Span::new(0..1, ExpectedChar('1'))));
/// ```
pub fn maybe<'a, 'b, P>(parser: P) -> BoxedParser<'a, 'b, Option<Span<P::Value>>, Infallible>
where
    P: Parser<'a> + 'b,
{
    Box::new(Maybe(parser))
}

/// Create a parser that will evaluate the given parser repeatedly, until it fails.
///
/// This will always return `Ok`, with a `Vec` of the parse results of all the successful
/// evaluations of the given parser. E.g., if the given parser fails the first evaluation, the
/// result will be `Ok(vec![])`.
///
/// ```
/// use packrs::{Span, chr, maybe_repeat, one_of};
///
/// let binary = maybe_repeat(one_of(vec![chr('0'), chr('1')]));
///
/// assert_eq!(binary.parse(""), Ok(Span::new(0..0, vec![])));
/// assert_eq!(binary.parse("0101"), Ok(Span::new(0..4, vec![
///     Span::new(0..1, "0"),
///     Span::new(1..2, "1"),
///     Span::new(2..3, "0"),
///     Span::new(3..4, "1"),
/// ])));
/// assert_eq!(binary.parse("012"), Ok(Span::new(0..2, vec![
///     Span::new(0..1, "0"),
///     Span::new(1..2, "1"),
/// ])));
/// ```
pub fn maybe_repeat<'a, 'b, P>(parser: P) -> BoxedParser<'a, 'b, Vec<Span<P::Value>>, Infallible>
where
    P: Parser<'a> + 'b,
{
    Box::new(MaybeRepeat(parser))
}

/// Create a parser that always succeeds, consuming no input and producing no values.
///
/// This will always return `Ok(())`. This can be useful as a fallback in alternations.
///
/// ```
/// use packrs::{Span, nothing};
///
/// assert_eq!(nothing().parse(""), Ok(Span::new(0..0, ())));
/// assert_eq!(nothing().parse("whatever"), Ok(Span::new(0..0, ())));
/// ```
pub fn nothing<'a, 'b>() -> BoxedParser<'a, 'b, (), Infallible> {
    Box::new(Nothing)
}

/// Create a parser that evaluates the given parsers in order, returning the first success.
///
/// If one of the given parsers evluates successfully, the result will be `Ok` with the parsed
/// value. If all the given parsers fail, the result will be an `Err` with a `Vec` of the parse
/// failures.
///
/// Note that all parsers must have the same `Value` and `Error` types. [`map`] and [`map_err`] can
/// be used to unify parser types.
///
/// ```
/// use packrs::{ExpectedChar, ParserExt, Span, chr, one_of};
///
/// #[derive(Debug, PartialEq)]
/// enum Op {
///     Add,
///     Sub,
///     Mul,
///     Div,
/// }
///
/// let op = one_of(vec![
///     chr('+').map(|_| Op::Add),
///     chr('-').map(|_| Op::Sub),
///     chr('*').map(|_| Op::Mul),
///     chr('/').map(|_| Op::Div),
/// ]);
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
///
/// [`map`]: fn.map.html
/// [`map_err`]: fn.map_err.html
pub fn one_of<'a, 'b, P>(parsers: Vec<P>) -> BoxedParser<'a, 'b, P::Value, Vec<Span<P::Error>>>
where
    P: Parser<'a> + 'b,
{
    Box::new(OneOf(parsers))
}

/// Create a parser that evaluates the given parser, succeeding on failure, failing on success, and
/// consuming no input.
///
/// If the given parser evaluates successfully, the result will be `Err(())`. If the given parser
/// fails, the result will be `Ok(())`.
///
/// ```
/// use packrs::{ParserExt, Span, UnexpectedEndOfInput, all_of, any, chr, reject, repeat};
///
/// let first_word = repeat(
///     all_of(vec![
///         reject(chr(' ')).map(|_| "").map_err(|_| UnexpectedEndOfInput),
///         any(),
///     ])
///     .map(|mut v| v.pop().unwrap().take()),
/// );
///
/// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, vec![
///     Span::new(0..1, "h"),
///     Span::new(1..2, "e"),
///     Span::new(2..3, "l"),
///     Span::new(3..4, "l"),
///     Span::new(4..5, "o"),
/// ])));
/// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
/// ```
pub fn reject<'a, 'b, P>(parser: P) -> BoxedParser<'a, 'b, (), ()>
where
    P: Parser<'a> + 'b,
{
    Box::new(Reject(parser))
}

/// Create a parser that will evaluate the given parser repeatedly, until it fails.
///
/// Unlike [`maybe_repeat`] this will fail if the given parser fails to match the first time it is
/// evaluated, returning an `Err` with the parse failure. If the first evaluation succeeds, the
/// result will be `Ok` with a `Vec` of the parse results of successful evaluations.
///
/// ```
/// use packrs::{ParserExt, Span, UnexpectedEndOfInput, all_of, any, chr, reject, repeat};
///
/// let first_word = repeat(
///     all_of(vec![
///         reject(chr(' ')).map(|_| "").map_err(|_| UnexpectedEndOfInput),
///         any(),
///     ])
///     .map(|mut v| v.pop().unwrap().take())
/// );
///
/// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, vec![
///     Span::new(0..1, "h"),
///     Span::new(1..2, "e"),
///     Span::new(2..3, "l"),
///     Span::new(3..4, "l"),
///     Span::new(4..5, "o"),
/// ])));
/// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
/// ```
///
/// [`maybe_repeat`]: fn.maybe_repeat.html
pub fn repeat<'a, 'b, P>(parser: P) -> BoxedParser<'a, 'b, Vec<Span<P::Value>>, P::Error>
where
    P: Parser<'a> + 'b,
{
    Box::new(Repeat(parser))
}

#[cfg(test)]
mod tests {
    use crate::parser_ext::ParserExt;

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

        let num = one_of(vec![
            chr('1').map(|_| Token::Num(1)),
            chr('2').map(|_| Token::Num(2)),
        ])
        .map_err(|_| CalcError::InvalidNumber);

        let op = one_of(vec![
            chr('+').map(|_| Token::OpAdd),
            chr('-').map(|_| Token::OpSub),
        ])
        .map_err(|_| CalcError::InvalidOperator);

        let add = all_of(vec![&num, &op, &num]).map(|mut seq| {
            let mut seq = seq.drain(0..3);
            let a = seq.next().unwrap();
            let op = seq.next().unwrap().take();
            let b = seq.next().unwrap();

            let a = a.map(|token| match token {
                Token::Num(a) => a,
                _ => unreachable!(),
            });
            let b = b.map(|token| match (op, token) {
                (Token::OpAdd, Token::Num(b)) => b,
                (Token::OpSub, Token::Num(b)) => -b,
                _ => unreachable!(),
            });

            Expr::Add(a, b)
        });
        let expr_num = (&num).map(|token| match token {
            Token::Num(n) => Expr::Num(n),
            _ => unreachable!(),
        });
        let expr = one_of(vec![&add, &expr_num]);

        assert_eq!(expr.parse("1"), Ok(Span::new(0..1, Expr::Num(1))));
        assert_eq!(expr.parse("2"), Ok(Span::new(0..1, Expr::Num(2))));
        assert_eq!(
            expr.parse("1+2"),
            Ok(Span::new(
                0..3,
                Expr::Add(Span::new(0..1, 1), Span::new(2..3, 2))
            ))
        );
        assert_eq!(
            expr.parse("1-2"),
            Ok(Span::new(
                0..3,
                Expr::Add(Span::new(0..1, 1), Span::new(2..3, -2))
            ))
        );
        assert_eq!(
            expr.parse("wow"),
            Err(Span::new(
                0..1,
                vec![
                    Span::new(0..1, CalcError::InvalidNumber),
                    Span::new(0..1, CalcError::InvalidNumber)
                ]
            ))
        );
    }
}
