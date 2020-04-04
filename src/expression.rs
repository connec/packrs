//! Parsing expressions that implement the [`Parser`](crate::Parser) trait.

mod all_of;
mod any;
mod check;
mod end_of_input;
mod join;
mod map;
mod map_err;
mod maybe;
mod maybe_repeat;
mod nothing;
mod one_of;
mod reject;
mod repeat;
mod str;

use crate::Span;

pub use all_of::*;
pub use any::*;
pub use check::*;
pub use end_of_input::*;
pub use join::*;
pub use map::*;
pub use map_err::*;
pub use maybe::*;
pub use maybe_repeat::*;
pub use nothing::*;
pub use one_of::*;
pub use reject::*;
pub use repeat::*;

#[cfg(test)]
mod test_expr;

trait ParseResultExt<V, E> {
    fn relative_to(self, end: usize) -> Result<Span<V>, Span<E>>;
}

impl<V, E> ParseResultExt<V, E> for Result<Span<V>, Span<E>> {
    fn relative_to(self, end: usize) -> Self {
        self.map(|value| value.relative_to(end))
            .map_err(|value| value.relative_to(end))
    }
}

#[cfg(test)]
mod tests {
    use crate::error::ExpectedString;
    use crate::parser::Parser;
    use crate::span::Span;

    use super::{AllOf, Map, MapErr, OneOf, ParseResultExt};

    #[test]
    fn test_span_ext_result_ok_relative_to() {
        let result: Result<_, Span<()>> = Ok(Span::new(0..1, 2));
        assert_eq!(result.relative_to(5), Ok(Span::new(5..6, 2)));
    }

    #[test]
    fn test_span_ext_result_err_relative_to() {
        let result: Result<Span<()>, _> = Err(Span::new(0..1, 2));
        assert_eq!(result.relative_to(5), Err(Span::new(5..6, 2)));
    }

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
            OneOf::<Box<dyn Parser<Value = _, Error = _>>>(vec![
                Box::new(Map("1", |_| Token::Num(1))),
                Box::new(Map("2", |_| Token::Num(2))),
            ]),
            |_: Vec<Span<ExpectedString>>| CalcError::InvalidNumber,
        );
        let op = MapErr(
            OneOf::<Box<dyn Parser<Value = _, Error = _>>>(vec![
                Box::new(Map("+", |_| Token::OpAdd)),
                Box::new(Map("-", |_| Token::OpSub)),
            ]),
            |_: Vec<Span<ExpectedString>>| CalcError::InvalidOperator,
        );
        let add = Map(
            AllOf::<&dyn Parser<Value = _, Error = _>>(vec![&num, &op, &num]),
            |mut seq: Vec<Span<Token>>| {
                let mut seq = seq.drain(0..3);
                let a = seq.next().unwrap();
                let op = seq.next().unwrap().take();
                let b = seq.next().unwrap();

                let a = a.map(|token| match token {
                    Token::Num(a) => a,
                    _ => unreachable!(),
                });
                let b = b.map(move |token| match (op, token) {
                    (Token::OpAdd, Token::Num(b)) => b,
                    (Token::OpSub, Token::Num(b)) => -b,
                    _ => unreachable!(),
                });

                Expr::Add(a, b)
            },
        );
        let expr_num = Map(&num, |token| match token {
            Token::Num(n) => Expr::Num(n),
            _ => unreachable!(),
        });
        let expr = OneOf::<&dyn Parser<Value = _, Error = _>>(vec![&add, &expr_num]);

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
