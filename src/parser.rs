use core::iter::FromIterator;
use core::marker::PhantomData;

use crate::error::ExpectedEndOfInput;
use crate::expression::*;
use crate::span::Span;

type BoxedFn<I, O> = Box<dyn Fn(I) -> O>;

/// Create a parser that will evaluate the given parsers in order against an input.
///
/// If all of the given parsers can be evaluated successfully, the result will be `Ok` with a `Vec`
/// of the successfully parsed values. If any parser fails, the result will be an `Err` with the
/// parse failure.
///
/// Note that all parsers must have the same type. [`map`](Parser::map) and
/// [`map_err`](Parser::map_err) can be used to unify value and errors types, and
/// [`Parser::as_ref`](Parser::as_ref) or [`Parser::boxed`](Parser::boxed) can be used to unify
/// different parser types.
///
/// ```
/// use packrs::{Parser, Span, all_of, chr};
/// use packrs::error::ExpectedChar;
///
/// let hello = all_of("hello".chars().map(chr).collect()).collect();
///
/// assert_eq!(hello.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
/// assert_eq!(hello.parse("world"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
pub fn all_of<'i, P>(parsers: Vec<P>) -> AllOf<P>
where
    P: Parser<'i>,
{
    AllOf(parsers)
}

/// Create a parser that consumes any single character.
///
/// When given a non-empty input, the result will be `Ok` with a subslice of the input containing
/// the first character.
///
/// When given an empty input, the result will be an `Err` with
/// [`UnexpectedEndOfInput`](crate::expression::any::UnexpectedEndOfInput).
///
/// ```
/// use packrs::{Parser, Span, all_of, any, chr};
/// use packrs::error::UnexpectedEndOfInput;
///
/// let first_word = all_of(vec![
///     chr(' ')
///         .reject()
///         .map(|_| "")
///         .map_err(|_| UnexpectedEndOfInput)
///         .boxed(),
///     any().boxed(),
/// ])
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

/// Create a parser that consumes a specific character.
///
/// When given an input that starts with the given character, the result will be `Ok` with a
/// subslice of the input containing the character.
///
/// When given an input that does not start with the given character, the result will be an `Err`
/// with [`ExpectedChar`](crate::expression::chr::ExpectedChar)`(char)`.
///
/// ```
/// use packrs::{Parser, Span, all_of, chr};
/// use packrs::error::ExpectedChar;
///
/// let hello = all_of("hello".chars().map(chr).collect()).collect();
///
/// assert_eq!(hello.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
/// assert_eq!(hello.parse("world, hello"), Err(Span::new(0..1, ExpectedChar('h'))));
/// ```
pub fn chr(char: char) -> Chr {
    Chr(char)
}

/// Create a parser that matches at the end of an input.
///
/// When given an empty input, the result will be `Ok(())`. When given a non-empty input the result
/// will be an `Err` with [`ExpectedEndOfInput`].
///
/// ```
/// use packrs::{Parser, Span, all_of, any, end_of_input};
/// use packrs::error::{ExpectedEndOfInput, UnexpectedEndOfInput};
///
/// #[derive(Debug, PartialEq)]
/// enum Error {
///     ExpectedEndOfInput,
///     UnexpectedEndOfInput,
/// }
///
/// impl From<ExpectedEndOfInput> for Error {
///     fn from(_: ExpectedEndOfInput) -> Self {
///         Error::ExpectedEndOfInput
///     }
/// }
///
/// impl From<UnexpectedEndOfInput> for Error {
///     fn from(_: UnexpectedEndOfInput) -> Self {
///         Error::UnexpectedEndOfInput
///     }
/// }
///
/// let one_char = all_of(vec![
///     any().map_err(|err| err.into()).boxed(),
///     end_of_input().map(|_| "").map_err(|err| err.into()).boxed(),
/// ])
///     .collect();
///
/// assert_eq!(one_char.parse(""), Err(Span::new(0..0, Error::UnexpectedEndOfInput)));
/// assert_eq!(one_char.parse("💩"), Ok(Span::new(0..4, "💩".to_string())));
/// assert_eq!(one_char.parse("नि"), Err(Span::new(3..6, Error::ExpectedEndOfInput)));
/// ```
pub fn end_of_input() -> EndOfInput {
    EndOfInput
}

/// Create a parser that always succeeds, consuming no input and producing no values.
///
/// This will always return `Ok(())`. This can be useful as a fallback in alternations.
///
/// ```
/// use packrs::{Parser, Span, nothing};
///
/// assert_eq!(nothing::<()>().parse(""), Ok(Span::new(0..0, ())));
/// assert_eq!(nothing::<()>().parse("whatever"), Ok(Span::new(0..0, ())));
/// ```
pub fn nothing<E>() -> Nothing<E> {
    Nothing(PhantomData)
}

/// Create a parser that evaluates the given parsers in order, returning the first success.
///
/// If one of the given parsers evluates successfully, the result will be `Ok` with the parsed
/// value. If all the given parsers fail, the result will be an `Err` with a `Vec` of the parse
/// failures.
///
/// Note that all parsers must have the same type. [`map`](Parser::map) and
/// [`map_err`](Parser::map_err) can be used to unify value and errors types, and
/// [`Parser::as_ref`](Parser::as_ref) or [`Parser::boxed`](Parser::boxed) can be used to unify
/// different parser types.
///
/// ```
/// use packrs::{Parser, Span, chr, one_of};
/// use packrs::error::ExpectedChar;
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
///     chr('+').map(|_| Op::Add).boxed(),
///     chr('-').map(|_| Op::Sub).boxed(),
///     chr('*').map(|_| Op::Mul).boxed(),
///     chr('/').map(|_| Op::Div).boxed(),
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
pub fn one_of<'i, P>(parsers: Vec<P>) -> OneOf<P>
where
    P: Parser<'i>,
{
    OneOf(parsers)
}

/// Create a parser that will match the given string at the beginning on an input.
///
/// When given an input that starts with the given string, the result will be `Ok` with a subslice
/// of the input containing the matched string. When given an input that does not start with the
/// given string, the result will be an `Err` with
/// [`ExpectedString`](crate::expression::string::ExpectedString)`(string)`.
///
/// ```
/// use packrs::{Parser, Span, string};
/// use packrs::error::ExpectedString;
///
/// let check_hello = string("hello").check();
///
/// assert_eq!(check_hello.parse("hello world"), Ok(Span::new(0..0, ())));
/// assert_eq!(check_hello.parse("world, hello"), Err(Span::new(0..1, ExpectedString("hello"))));
/// ```
pub fn string(string: &str) -> String {
    String(string)
}

/// A trait implemented by parsing expressions.
pub trait Parser<'i> {
    /// The type returned in successful parse results.
    type Value;

    /// The type returned in failed parse results.
    type Error;

    /// Parses a given input and returns the result.
    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>>;

    /// Creates a parser that will evaluate without consuming input or producing a value.
    ///
    /// If the parser evaluates successfully, the result will be `Ok` with `()`. If the parser
    /// fails, the result will be an `Err` with the parse failure.
    ///
    /// ```
    /// use packrs::{Parser, Span, string};
    /// use packrs::error::ExpectedString;
    ///
    /// let check_hello = string("hello").check();
    ///
    /// assert_eq!(check_hello.parse("hello world"), Ok(Span::new(0..0, ())));
    /// assert_eq!(check_hello.parse("world, hello"), Err(Span::new(0..1, ExpectedString("hello"))));
    /// ```
    fn check(self) -> Check<Self>
    where
        Self: Sized,
    {
        Check(self)
    }

    /// Creates a parser that fails if there is remaining input.
    ///
    /// When given an empty input, the result will be `Ok(())`. When given a non-empty input the
    /// result will be an `Err` with [`crate::expression::end_of_input::ExpectedEndOfInput`].
    ///
    /// ```
    /// use packrs::{Parser, Span, any};
    /// use packrs::error::{ExpectedEndOfInput, UnexpectedEndOfInput};
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum Error {
    ///     ExpectedEndOfInput,
    ///     UnexpectedEndOfInput,
    /// }
    ///
    /// impl From<ExpectedEndOfInput> for Error {
    ///     fn from(_: ExpectedEndOfInput) -> Self {
    ///         Error::ExpectedEndOfInput
    ///     }
    /// }
    ///
    /// impl From<UnexpectedEndOfInput> for Error {
    ///     fn from(_: UnexpectedEndOfInput) -> Self {
    ///         Error::UnexpectedEndOfInput
    ///     }
    /// }
    ///
    /// let one_char = any().end();
    ///
    /// assert_eq!(one_char.parse(""), Err(Span::new(0..0, Error::UnexpectedEndOfInput)));
    /// assert_eq!(one_char.parse("💩"), Ok(Span::new(0..4, "💩")));
    /// assert_eq!(one_char.parse("नि"), Err(Span::new(3..6, Error::ExpectedEndOfInput)));
    /// ```
    fn end<'p, E>(self) -> Box<dyn Parser<'i, Value = Self::Value, Error = E> + 'p>
    where
        Self: Sized + 'p,
        E: From<Self::Error> + From<ExpectedEndOfInput> + 'p,
        'i: 'p,
    {
        Box::new(Map(
            Join(MapErr(self, E::from), MapErr(EndOfInput, E::from)),
            |(value, _): (Span<_>, _)| value.take(),
        ))
    }

    /// Creates a parser that will evaluate two parsers and combine their results.
    ///
    /// If both parsers evaluate successfully, the result will be `Ok` with a tuple of the parsed
    /// values. If either parser fails, the result will be an `Err` with the parse failure.
    ///
    /// ```
    /// use packrs::{Parser, Span, chr, string};
    /// use packrs::error::ExpectedChar;
    ///
    /// let expr = chr('1').join(string("+1").maybe());
    ///
    /// assert_eq!(expr.parse("1"), Ok(Span::new(0..1, (
    ///     Span::new(0..1, "1"),
    ///     Span::new(1..1, None)
    /// ))));
    /// assert_eq!(expr.parse("1+1"), Ok(Span::new(0..3, (
    ///     Span::new(0..1, "1"),
    ///     Span::new(1..3, Some(Span::new(0..2, "+1"))),
    /// ))));
    /// assert_eq!(expr.parse("2+1"), Err(Span::new(0..1, ExpectedChar('1'))));
    /// ```
    fn join<P>(self, other: P) -> Join<Self, P>
    where
        Self: Sized,
        P: Parser<'i, Error = Self::Error>,
    {
        Join(self, other)
    }

    /// Creates a parser that will transform a successful result with the given function.
    ///
    /// If the parser evaluates successfully, the result will be `Ok` with
    /// `transform(<parsed value>)`. If the given parser fails, the result will be an `Err` with the
    /// parse failure.
    ///
    /// ```
    /// use packrs::{Parser, Span, chr, one_of};
    /// use packrs::error::ExpectedChar;
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
    ///     chr('+').map(|_| Op::Add).boxed(),
    ///     chr('-').map(|_| Op::Sub).boxed(),
    ///     chr('*').map(|_| Op::Mul).boxed(),
    ///     chr('/').map(|_| Op::Div).boxed(),
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
    fn map<F, U>(self, transform: F) -> Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Value) -> U,
    {
        Map(self, transform)
    }

    /// Creates a parser that will transform a failure with the given function.
    ///
    /// If the parser evaluates successfully, the result will be `Ok` with the parsed value. If the
    /// parser fails, the result will be an `Err` with `transform(<parse failure>)`.
    ///
    /// ```
    /// use packrs::{Parser, Span, chr, one_of};
    /// use packrs::error::ExpectedChar;
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
    /// let op = one_of(vec![
    ///     chr('+').map(|_| Op::Add).boxed(),
    ///     chr('-').map(|_| Op::Sub).boxed(),
    ///     chr('*').map(|_| Op::Mul).boxed(),
    ///     chr('/').map(|_| Op::Div).boxed(),
    /// ])
    ///     .map_err(|_| InvalidOp);
    ///
    /// assert_eq!(op.parse("+"), Ok(Span::new(0..1, Op::Add)));
    /// assert_eq!(op.parse("/"), Ok(Span::new(0..1, Op::Div)));
    /// assert_eq!(op.parse("÷"), Err(Span::new(0..2, InvalidOp)));
    /// ```
    fn map_err<F, E>(self, transform: F) -> MapErr<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Error) -> E,
    {
        MapErr(self, transform)
    }

    /// Creates a parser that will convert the result into an `Option`.
    ///
    /// The returned parser will always evaluate successfully. If this parser evaluates
    /// successfully, the parsed value will become `Some(<parsed value>)`. If this parser fails, the
    /// parsed value will be `None`.
    ///
    /// ```
    /// use packrs::{Parser, Span, all_of, chr, string};
    /// use packrs::error::ExpectedChar;
    ///
    /// let expr = all_of(vec![
    ///     chr('1').boxed(),
    ///     string("+1")
    ///         .maybe()
    ///         .map(|opt| match opt {
    ///             Some(span) => span.take(),
    ///             None => "",
    ///         })
    ///         .boxed()
    /// ])
    ///     .collect();
    ///
    /// assert_eq!(expr.parse("1"), Ok(Span::new(0..1, "1".to_string())));
    /// assert_eq!(expr.parse("1+1"), Ok(Span::new(0..3, "1+1".to_string())));
    /// assert_eq!(expr.parse("2+1"), Err(Span::new(0..1, ExpectedChar('1'))));
    /// ```
    fn maybe<E>(self) -> Maybe<Self, E>
    where
        Self: Sized,
    {
        Maybe(self, PhantomData)
    }

    /// Creates a parser that will evaluate repeatedly, until it fails.
    ///
    /// The returned parser will always evaluate successfully, and the parsed value will be a `Vec`
    /// of the parse results of the successful evaluations of this parser. E.g., if this parser
    /// fails the first evaluation, the parsed value will be `vec![]`.
    ///
    /// ```
    /// use packrs::{Parser, Span, chr, one_of};
    ///
    /// let binary = one_of(vec![chr('0'), chr('1')]).maybe_repeat::<()>().collect();
    ///
    /// assert_eq!(binary.parse(""), Ok(Span::new(0..0, "".to_string())));
    /// assert_eq!(binary.parse("0101"), Ok(Span::new(0..4, "0101".to_string())));
    /// assert_eq!(binary.parse("012"), Ok(Span::new(0..2, "01".to_string())));
    /// ```
    fn maybe_repeat<E>(self) -> MaybeRepeat<Self, E>
    where
        Self: Sized,
    {
        MaybeRepeat(self, PhantomData)
    }

    /// Creates a parser that will invert its result, without consuming input or producing a value.
    ///
    /// If this parser evaluates successfully, the result will be `Err(())`. If this parser fails,
    /// the result will be `Ok(())`.
    ///
    /// ```
    /// use packrs::{Parser, Span, all_of, any, chr};
    /// use packrs::error::UnexpectedEndOfInput;
    ///
    /// let first_word = all_of(vec![
    ///     chr(' ').reject().map(|_| "").map_err(|_| UnexpectedEndOfInput).boxed(),
    ///     any().boxed(),
    /// ])
    ///     .map(|mut v| v.pop().unwrap().take())
    ///     .repeat()
    ///     .collect();
    ///
    /// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
    /// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
    /// ```
    fn reject(self) -> Reject<Self>
    where
        Self: Sized,
    {
        Reject(self)
    }

    /// Creates a parser that evaluates repeatedly, until it fails.
    ///
    /// Unlike [`maybe_repeat`](Parser::maybe_repeat) this will fail if the parser fails to match
    /// the first time it is evaluated, returning an `Err` with the parse failure. If the first
    /// evaluation succeeds, the result will be a `Vec` of the parse results of successful
    /// evaluations.
    ///
    /// ```
    /// use packrs::{Parser, Span, all_of, any, chr};
    /// use packrs::error::UnexpectedEndOfInput;
    ///
    /// let first_word = all_of(vec![
    ///     chr(' ').reject().map(|_| "").map_err(|_| UnexpectedEndOfInput).boxed(),
    ///     any().boxed(),
    /// ])
    ///     .map(|mut v| v.pop().unwrap().take())
    ///     .repeat()
    ///     .collect();
    ///
    /// assert_eq!(first_word.parse("hello world"), Ok(Span::new(0..5, "hello".to_string())));
    /// assert_eq!(first_word.parse(""), Err(Span::new(0..0, UnexpectedEndOfInput)));
    /// ```
    fn repeat(self) -> Repeat<Self>
    where
        Self: Sized,
    {
        Repeat(self)
    }

    /// Convert this parser to one that collects its result.
    ///
    /// This is paricularly useful for processing the results of [`all_of`](crate::all_of),
    /// [`maybe_repeat`](Parser::maybe_repeat), [`one_of`](crate::one_of), and
    /// [`repeat`](Parser::repeat).
    fn collect<C, I>(self) -> Map<Self, BoxedFn<Self::Value, C>>
    where
        Self: Sized,
        Self::Value: IntoIterator<Item = Span<I>>,
        C: FromIterator<I>,
    {
        self.map(Box::new(|v| v.into_iter().map(|i| i.take()).collect()))
    }

    /// Turn a parser into a boxed trait object.
    ///
    /// This is particularly useful when constructing `AllOf` or `OneOf` with different (but
    /// compatible) parsers.
    fn boxed<'p>(self) -> Box<dyn Parser<'i, Value = Self::Value, Error = Self::Error> + 'p>
    where
        Self: Sized + 'p,
    {
        Box::new(self)
    }

    /// Turn a parser into a trait object reference.
    ///
    /// This is particularly useful when constructing `AllOf` or `OneOf` with different (but
    /// compatible) parsers.
    fn as_ref(&self) -> &dyn Parser<'i, Value = Self::Value, Error = Self::Error>
    where
        Self: Sized,
    {
        self
    }
}

impl<'i, P> Parser<'i> for &P
where
    P: Parser<'i> + ?Sized,
{
    type Value = P::Value;

    type Error = P::Error;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        (*self).parse(input)
    }
}

impl<'i, P> Parser<'i> for Box<P>
where
    P: Parser<'i> + ?Sized,
{
    type Value = P::Value;

    type Error = P::Error;

    fn parse(&self, input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        std::convert::AsRef::as_ref(self).parse(input)
    }
}

#[cfg(test)]
mod tests {
    use crate::span::Span;

    use super::Parser;

    #[test]
    fn test_parser_collect() {
        use crate::any;

        let expr = any().repeat().collect();

        assert_eq!(
            expr.parse("hello"),
            Ok(Span::new(0..5, "hello".to_string()))
        );
    }
}
