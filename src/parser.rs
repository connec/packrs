use crate::span::Span;

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

/// A trait for convenience methods on parse results.
pub trait ParseResult<V, E> {
    fn relative_to(self, end: usize) -> Result<Span<V>, Span<E>>;
}

impl<V, E> ParseResult<V, E> for Result<Span<V>, Span<E>> {
    fn relative_to(self, end: usize) -> Self {
        self.map(|value| value.relative_to(end))
            .map_err(|value| value.relative_to(end))
    }
}
