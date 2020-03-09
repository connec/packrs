//! Parsing expressions based on a [`Parser`] trait.
//!
//! [`Parser`]: trait.Parser.html

mod and_predicate;
mod any;
mod char;
mod map;
mod map_err;
mod not_predicate;
mod nothing;
mod one_or_more;
mod optional;
mod ordered_choice;
mod sequence;
mod zero_or_more;

#[cfg(test)]
mod test_expr;

pub use self::and_predicate::*;
pub use self::any::*;
pub use self::char::*;
pub use self::map::*;
pub use self::map_err::*;
pub use self::not_predicate::*;
pub use self::nothing::*;
pub use self::one_or_more::*;
pub use self::optional::*;
pub use self::ordered_choice::*;
pub use self::sequence::*;
pub use self::zero_or_more::*;

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::parser::Parser;
//     use crate::span::Span;

//     #[test]
//     fn trivial_calculator() {
//         #[derive(Debug, PartialEq)]
//         enum Token {
//             Num(i8),
//             OpAdd,
//             OpSub,
//         }

//         #[derive(Debug, PartialEq)]
//         enum Expr {
//             Num(i8),
//             Add(Span<i8>, Span<i8>),
//         }

//         #[derive(Debug, PartialEq)]
//         enum CalcError {
//             InvalidNumber,
//             InvalidOperator,
//         }

//         let num = MapErr(
//             OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![
//                 &Map(Char('1'), |_| Token::Num(1)),
//                 &Map(Char('2'), |_| Token::Num(2)),
//             ]),
//             |_| CalcError::InvalidNumber,
//         );
//         let op = MapErr(
//             OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![
//                 &Map(Char('+'), |_| Token::OpAdd),
//                 &Map(Char('-'), |_| Token::OpSub),
//             ]),
//             |_| CalcError::InvalidOperator,
//         );
//         let add = Map(
//             Sequence::<&dyn Parser<Value = _, Error = _>>(vec![&num, &op, &num]),
//             |mut seq: Vec<Span<Token>>| {
//                 let mut seq = seq.drain(0..3);
//                 let a = seq.next().unwrap();
//                 let op = seq.next().unwrap().take();
//                 let b = seq.next().unwrap();

//                 let a = a.map(|token| match token {
//                     Token::Num(a) => a,
//                     _ => unreachable!(),
//                 });
//                 let b = b.map(move |token| match (op, token) {
//                     (Token::OpAdd, Token::Num(b)) => b,
//                     (Token::OpSub, Token::Num(b)) => -b,
//                     _ => unreachable!(),
//                 });

//                 Expr::Add(a, b)
//             },
//         );
//         let expr_num = Map(&num, |token| match token {
//             Token::Num(n) => Expr::Num(n),
//             _ => unreachable!(),
//         });
//         let expr = OrderedChoice::<&dyn Parser<Value = _, Error = _>>(vec![&add, &expr_num]);

//         assert_eq!(expr.parse("1"), Ok(Span::new(0..1, Expr::Num(1))));
//         assert_eq!(expr.parse("2"), Ok(Span::new(0..1, Expr::Num(2))));
//         assert_eq!(
//             expr.parse("1+2"),
//             Ok(Span::new(
//                 0..3,
//                 Expr::Add(Span::new(0..1, 1), Span::new(2..3, 2))
//             ))
//         );
//         assert_eq!(
//             expr.parse("1-2"),
//             Ok(Span::new(
//                 0..3,
//                 Expr::Add(Span::new(0..1, 1), Span::new(2..3, -2))
//             ))
//         );
//         assert_eq!(
//             expr.parse("wow"),
//             Err(Span::new(
//                 0..1,
//                 vec![
//                     Span::new(0..1, CalcError::InvalidNumber),
//                     Span::new(0..1, CalcError::InvalidNumber)
//                 ]
//             ))
//         );
//     }
// }
