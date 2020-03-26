//! An expression that always succeeds, consuming no input and producing no values.
//!
//! See [`nothing`].

use core::marker::PhantomData;

use crate::parser::Parser;
use crate::span::Span;

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

/// The struct returned from [`nothing`].
pub struct Nothing<E>(PhantomData<E>);

impl<'i, E> Parser<'i> for Nothing<E> {
    type Value = ();
    type Error = E;

    fn parse(&self, _input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        Ok(Span::new(0..0, ()))
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;

    use crate::parser::Parser;
    use crate::span::Span;

    use super::nothing;

    #[quickcheck]
    fn infallible(input: String) {
        assert_eq!(nothing::<()>().parse(&input), Ok(Span::new(0..0, ())));
    }
}
