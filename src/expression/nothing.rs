use core::convert::Infallible;

use crate::parser::Parser;
use crate::span::Span;

/// An expression for parsing nothing.
pub struct Nothing;

impl<'a> Parser<'a> for Nothing {
    type Value = ();
    type Error = Infallible;

    /// Parse nothing.
    ///
    /// This always succeeds without consuming input. It can be useful in combinators when 'nothing'
    /// is an allowed value.
    fn parse(&self, _input: &'a str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(Span::new(0..0, ()))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::parser::Parser;
    use crate::span::Span;

    use super::Nothing;

    #[quickcheck]
    fn infallible(input: String) {
        assert_eq!(Nothing.parse(&input), Ok(Span::new(0..0, ())));
    }
}
