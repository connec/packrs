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

impl<'a, P> Parser<'a> for &P
where
    P: Parser<'a> + ?Sized,
{
    type Value = P::Value;

    type Error = P::Error;

    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        (*self).parse(input)
    }
}

impl<'a, P> Parser<'a> for Box<P>
where
    P: Parser<'a> + ?Sized,
{
    type Value = P::Value;

    type Error = P::Error;

    fn parse(&self, input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.as_ref().parse(input)
    }
}

/// A trait for convenience methods on parse results.
pub trait ParseResult<V, E> {
    /// Offset the span of the result relative to the given end index.
    fn relative_to(self, end: usize) -> Result<Span<V>, Span<E>>;
}

impl<V, E> ParseResult<V, E> for Result<Span<V>, Span<E>> {
    fn relative_to(self, end: usize) -> Self {
        self.map(|value| value.relative_to(end))
            .map_err(|value| value.relative_to(end))
    }
}

#[cfg(test)]
mod tests {
    use crate::span::Span;

    use super::ParseResult;

    #[test]
    fn test_parse_result_ok_relative_to() {
        let result: Result<_, Span<()>> = Ok(Span::new(0..1, 2));
        assert_eq!(result.relative_to(5), Ok(Span::new(5..6, 2)));
    }

    #[test]
    fn test_parse_result_err_relative_to() {
        let result: Result<Span<()>, _> = Err(Span::new(0..1, 2));
        assert_eq!(result.relative_to(5), Err(Span::new(5..6, 2)));
    }
}
