use crate::combinators::{map, map_err, BoxedParser};
use crate::parser::Parser;

/// A trait for convenience methods on parsers.
pub trait ParserExt {
    /// Map this parser to one producing a different value.
    ///
    /// See [`map`] and [`Map`] for more details.
    ///
    /// [`map`]: ../fn.map.html
    /// [`Map`]: ../expression/struct.Map.html
    fn map<'a, 'b, F, U>(self, transform: F) -> BoxedParser<'a, 'b, U, Self::Error>
    where
        Self: Parser<'a> + Sized + 'b,
        F: Fn(Self::Value) -> U + 'b,
    {
        map(self, transform)
    }

    /// Map this parser to one producing a different error.
    ///
    /// See [`map_err`] and [`MapErr`] for more details.
    ///
    /// [`map_err`]: ../fn.map_err.html
    /// [`MapErr`]: ../expression/struct.MapErr.html
    fn map_err<'a, 'b, F, U>(self, transform: F) -> BoxedParser<'a, 'b, Self::Value, U>
    where
        Self: Parser<'a> + Sized + 'b,
        F: Fn(Self::Error) -> U + 'b,
    {
        map_err(self, transform)
    }
}

impl<'a, P> ParserExt for P where P: Parser<'a> {}

#[cfg(test)]
mod tests {
    use crate::combinators::any;
    use crate::span::Span;

    use super::ParserExt;

    #[test]
    fn test_parser_ext_map() {
        let expr = any().map(|c| c.len());

        assert_eq!(expr.parse("÷"), Ok(Span::new(0..2, 2)));
    }

    #[test]
    fn test_parser_ext_map_err() {
        let expr = any().map_err(|_| "oh well");

        assert_eq!(expr.parse(""), Err(Span::new(0..0, "oh well")));
    }
}
