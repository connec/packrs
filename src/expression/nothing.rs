//! An expression that always succeeds, consuming no input and producing no values.
//!
//! See [`crate::nothing`].

use core::marker::PhantomData;

use crate::parser::Parser;
use crate::span::Span;

/// The struct returned from [`crate::nothing`].
pub struct Nothing<E>(pub(crate) PhantomData<E>);

impl<E> Parser for Nothing<E> {
    type Value = ();
    type Error = E;

    fn parse(&self, _input: &'_ str) -> Result<Span<Self::Value>, Span<Self::Error>> {
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
            Nothing(PhantomData::<()>).parse(&input),
            Ok(Span::new(0..0, ()))
        );
    }
}
