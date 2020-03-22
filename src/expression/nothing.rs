use core::marker::PhantomData;

use crate::parser::Parser;
use crate::span::Span;

/// An expression for parsing nothing.
pub struct Nothing<E>(pub(crate) PhantomData<E>);

impl<'i, E> Parser<'i> for Nothing<E> {
    type Value = ();
    type Error = E;

    /// Parse nothing.
    ///
    /// This always succeeds without consuming input. It can be useful in combinators when 'nothing'
    /// is an allowed value.
    fn parse(&self, _input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(Span::new(0..0, ()))
    }
}

#[cfg(test)]
mod tests {
    use core::marker::PhantomData;
    use quickcheck_macros::quickcheck;

    use crate::parser::Parser;
    use crate::span::Span;

    use super::Nothing;

    #[quickcheck]
    fn infallible(input: String) {
        assert_eq!(
            Nothing::<()>(PhantomData).parse(&input),
            Ok(Span::new(0..0, ()))
        );
    }
}
