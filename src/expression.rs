//! Enum-based PEG expression library.
//!
//! This module centres around the [`Expression`] enum, which can be used to define parse trees.
//! Constructed parse trees can then be given to [`parse`], along with an input `&str`, which will
//! recursively evaluate the expressions in the tree against the input.
//!
//! ```
//! use packrs::expression::{parse, Expression::*};
//!
//! let string = OrderedChoice(
//!     &Sequence(
//!         &Terminal('\''),
//!         &Sequence(
//!             &ZeroOrMore(&Sequence(
//!                 &OrderedChoice(&Terminal('\\'), &NotPredicate(&Terminal('\''))),
//!                 &Any,
//!             )),
//!             &Terminal('\''),
//!         ),
//!     ),
//!     &Sequence(
//!         &Terminal('"'),
//!         &Sequence(
//!             &ZeroOrMore(&Sequence(
//!                 &OrderedChoice(&Terminal('\\'), &NotPredicate(&Terminal('"'))),
//!                 &Any,
//!             )),
//!             &Terminal('"'),
//!         ),
//!     ),
//! );
//!
//! assert_eq!(
//!     parse("'hello \\' world'", &string),
//!     Ok("'hello \\' world'"),
//! );
//! ```
//!
//! [`Expression`]: enum.Expression.html

use Expression::*;

/// A PEG expression.
///
/// Each variant, apart from the terminals `Empty` and `Terminal`, contains references to
/// sub-expressions.
///
/// See each variant's documentation for how the expression should be evaluated.
pub enum Expression<'a> {
    /// Always matches, regardless of the input (even if empty). Outputs an empty string.
    Empty,

    /// Matches any character and returns it as output. Fails if the input is empty, with
    /// 'unexpected end of input'.
    Any,

    /// Matches the given `char` and returns it as output, or fails with "expected '<char>'".
    Terminal(char),

    /// Matches the two given sub-expressions in sequence and concatenates their output. If any
    /// sub-expression fails, the whole sequence expression fails with that error.
    Sequence(&'a Expression<'a>, &'a Expression<'a>),

    /// Matches the the given sub-expressions one after the other, returning the first successful
    /// result. If neither sub-expression matches the ordered choice fails with the two expression's
    /// errors joined by " or ".
    OrderedChoice(&'a Expression<'a>, &'a Expression<'a>),

    /// Matches the given sub-expression zero or more times. Outputs the sub-expression outputs
    /// concatenated together. Like `Empty`, this can't fail.
    ZeroOrMore(&'a Expression<'a>),

    /// Matches the given sub-expression one or more times. Outputs the sub-expression outputs
    /// concatenated together. If the first attempt to match the sub-expression fails, this failure
    /// is returned.
    OneOrMore(&'a Expression<'a>),

    /// Matches the given sub-expression, or else succeeds, outputing an empty string.
    Optional(&'a Expression<'a>),

    /// Matches the given sub-expression without consuming any input. If the sub-expression fails,
    /// the failure is returned.
    AndPredicate(&'a Expression<'a>),

    /// Matches the given sub-expression without consuming any input. If the sub-expression
    /// succeeds, a failure is returned. If the sub-expression fails, the not-predicate expression
    /// succeeds without consuming.
    NotPredicate(&'a Expression<'a>),
}

/// Evaluate a given `Expression` against a given input string.
///
/// This will work rescursively to match the expression and evaluate any sub-expressions. If there
/// is any unconsumed input once the expression has been evaluated then an "expected end of input"
/// error is returned.
///
/// **Note:** this implementation will likely be vulnerable to stack overflows, unless LLVM is very
pub fn parse<'a>(input: &'a str, expression: &'a Expression) -> Result<&'a str, String> {
    let (output, remainder) = eval(input, expression)?;
    if remainder.is_empty() {
        Ok(output)
    } else {
        Err("expected end of input".to_string())
    }
}

/// Evaluate a given `Expression` against a given input string.
///
/// This will work rescursively to match the expression and evaluate any sub-expressions. Once the
/// terminals are reached, the outputs will propagate back up the stack until the overall result is
/// worked out.
///
/// **Note:** this implementation will likely be vulnerable to stack overflows, unless LLVM is very
/// clever.
fn eval<'a>(input: &'a str, expression: &Expression) -> Result<(&'a str, &'a str), String> {
    match expression {
        Empty => Ok(("", input)),
        Any => {
            let mut chars = input.char_indices();
            let _ = chars
                .next()
                .ok_or_else(|| "unexpected end of input".to_string())?;
            chars
                .next()
                .map_or_else(|| Ok((input, "")), |(idx, _)| Ok(input.split_at(idx)))
        }
        Terminal(char) => {
            let mut chars = input.char_indices();
            let (_, actual) = chars
                .next()
                .ok_or_else(|| "unexpected end of input".to_string())?;
            if actual == *char {
                chars
                    .next()
                    .map_or_else(|| Ok((input, "")), |(idx, _)| Ok(input.split_at(idx)))
            } else {
                Err(format!("expected '{}'", char))
            }
        }
        Sequence(expr1, expr2) => {
            let (output1, input2) = eval(input, expr1)?;
            let (output2, _remainder) = eval(input2, expr2)?;
            Ok(input.split_at(output1.len() + output2.len()))
        }
        OrderedChoice(expr1, expr2) => eval(input, expr1).or_else(|mut error| {
            eval(input, expr2).map_err(|error2| {
                error.push_str(" or ");
                error.push_str(&error2);
                error
            })
        }),
        ZeroOrMore(expr) => {
            let mut remaining = input;
            while let Ok((_, remaining_)) = eval(remaining, expr) {
                remaining = remaining_;
            }
            Ok(input.split_at(input.len() - remaining.len()))
        }
        OneOrMore(expr) => {
            let (_, mut remaining) = eval(input, expr)?;
            while let Ok((_, remaining_)) = eval(remaining, expr) {
                remaining = remaining_;
            }
            Ok(input.split_at(input.len() - remaining.len()))
        }
        Optional(expr) => eval(input, expr).or_else(|_| Ok(("", input))),
        AndPredicate(expr) => {
            eval(input, expr)?;
            Ok(("", input))
        }
        NotPredicate(expr) => eval(input, expr)
            .map_or_else(|_| Ok(("", input)), |_| Err("unexpected input".to_string())),
    }
}

#[cfg(test)]
mod tests {
    use super::{eval, parse, Expression::*};

    #[test]
    fn construct_empty() {
        let _ = Empty;
    }

    #[test]
    fn eval_empty() {
        let expr = Empty;
        assert_eq!(eval("", &expr), Ok(("", "")));
    }

    #[test]
    fn construct_any() {
        let _ = Any;
    }

    #[test]
    fn eval_any_ok() {
        let expr = Any;
        assert_eq!(eval("a", &expr), Ok(("a", "")));
    }

    #[test]
    fn eval_any_err() {
        let expr = Any;
        assert_eq!(eval("", &expr), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn construct_terminal() {
        let _ = Terminal('a');
    }

    #[test]
    fn eval_terminal_ok() {
        let expr = Terminal('a');
        assert_eq!(eval("a", &expr), Ok(("a", "")));
    }

    #[test]
    fn eval_terminal_err() {
        let expr = Terminal('a');
        assert_eq!(eval("", &expr), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn construct_sequence() {
        let a = Terminal('a');
        let b = Terminal('b');
        let _ = Sequence(&a, &b);
    }

    #[test]
    fn eval_sequence_ok() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = Sequence(&a, &b);
        assert_eq!(eval("ab", &expr), Ok(("ab", "")));
    }

    #[test]
    fn eval_sequence_err1() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = Sequence(&a, &b);
        assert_eq!(eval("bb", &expr), Err("expected 'a'".to_string()));
    }

    #[test]
    fn eval_sequence_err2() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = Sequence(&a, &b);
        assert_eq!(eval("aa", &expr), Err("expected 'b'".to_string()));
    }

    #[test]
    fn construct_ordered_choice() {
        let a = Terminal('a');
        let b = Terminal('b');
        let _ = OrderedChoice(&a, &b);
    }

    #[test]
    fn eval_ordered_choice_ok1() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = OrderedChoice(&a, &b);
        assert_eq!(eval("ab", &expr), Ok(("a", "b")));
    }

    #[test]
    fn eval_ordered_choice_ok2() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = OrderedChoice(&a, &b);
        assert_eq!(eval("ba", &expr), Ok(("b", "a")));
    }

    #[test]
    fn eval_ordered_choice_err() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = OrderedChoice(&a, &b);
        assert_eq!(
            eval("c", &expr),
            Err("expected 'a' or expected 'b'".to_string())
        );
    }

    #[test]
    fn construct_zero_or_more() {
        let a = Terminal('a');
        let _ = ZeroOrMore(&a);
    }

    #[test]
    fn eval_zero_or_more_ok_empty() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("", &expr), Ok(("", "")));
    }

    #[test]
    fn eval_zero_or_more_ok_no_match() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("b", &expr), Ok(("", "b")));
    }

    #[test]
    fn eval_zero_or_more_ok_one() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("ab", &expr), Ok(("a", "b")));
    }

    #[test]
    fn eval_zero_or_more_ok_more() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("aaab", &expr), Ok(("aaa", "b")));
    }

    #[test]
    fn construct_one_or_more() {
        let a = Terminal('a');
        let _ = OneOrMore(&a);
    }

    #[test]
    fn eval_one_or_more_err_empty() {
        let a = Terminal('a');
        let expr = OneOrMore(&a);
        assert_eq!(eval("", &expr), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn eval_one_or_more_err_no_match() {
        let a = Terminal('a');
        let expr = OneOrMore(&a);
        assert_eq!(eval("b", &expr), Err("expected 'a'".to_string()));
    }

    #[test]
    fn eval_one_or_more_ok_one() {
        let a = Terminal('a');
        let expr = OneOrMore(&a);
        assert_eq!(eval("ab", &expr), Ok(("a", "b")));
    }

    #[test]
    fn eval_one_or_more_ok_more() {
        let a = Terminal('a');
        let expr = OneOrMore(&a);
        assert_eq!(eval("aaab", &expr), Ok(("aaa", "b")));
    }

    #[test]
    fn construct_optional() {
        let a = Terminal('a');
        let _ = Optional(&a);
    }

    #[test]
    fn eval_optional_ok_empty() {
        let a = Terminal('a');
        let expr = Optional(&a);
        assert_eq!(eval("", &expr), Ok(("", "")));
    }

    #[test]
    fn eval_optional_ok_no_match() {
        let a = Terminal('a');
        let expr = Optional(&a);
        assert_eq!(eval("b", &expr), Ok(("", "b")));
    }

    #[test]
    fn eval_optional_ok_match() {
        let a = Terminal('a');
        let expr = Optional(&a);
        assert_eq!(eval("ab", &expr), Ok(("a", "b")));
    }

    #[test]
    fn construct_and_predicate() {
        let a = Terminal('a');
        let _ = AndPredicate(&a);
    }

    #[test]
    fn eval_and_predicate_ok() {
        let a = Terminal('a');
        let expr = AndPredicate(&a);
        assert_eq!(eval("a", &expr), Ok(("", "a")));
    }

    #[test]
    fn eval_and_predicate_err() {
        let a = Terminal('a');
        let expr = AndPredicate(&a);
        assert_eq!(eval("b", &expr), Err("expected 'a'".to_string()));
    }

    #[test]
    fn construct_not_predicate() {
        let a = Terminal('a');
        let _ = NotPredicate(&a);
    }

    #[test]
    fn eval_not_predicate_ok() {
        let a = Terminal('a');
        let expr = NotPredicate(&a);
        assert_eq!(eval("b", &expr), Ok(("", "b")));
    }

    #[test]
    fn eval_not_predicate_err() {
        let a = Terminal('a');
        let expr = NotPredicate(&a);
        assert_eq!(eval("a", &expr), Err("unexpected input".to_string()));
    }

    #[test]
    fn parse_err_no_match() {
        let a = Terminal('a');
        assert_eq!(parse("b", &a), Err("expected 'a'".to_string()));
    }

    #[test]
    fn parse_err_match_and_remainder() {
        let a = Terminal('a');
        assert_eq!(parse("ab", &a), Err("expected end of input".to_string()));
    }

    #[test]
    fn parse_ok_match_no_remainder() {
        let a = Terminal('a');
        assert_eq!(parse("a", &a), Ok("a"));
    }

    #[test]
    fn parse_strings() {
        let expr = OrderedChoice(
            &Sequence(
                &Terminal('\''),
                &Sequence(
                    &ZeroOrMore(&Sequence(
                        &OrderedChoice(&Terminal('\\'), &NotPredicate(&Terminal('\''))),
                        &Any,
                    )),
                    &Terminal('\''),
                ),
            ),
            &Sequence(
                &Terminal('"'),
                &Sequence(
                    &ZeroOrMore(&Sequence(
                        &OrderedChoice(&Terminal('\\'), &NotPredicate(&Terminal('"'))),
                        &Any,
                    )),
                    &Terminal('"'),
                ),
            ),
        );

        assert_eq!(eval("'hello world'", &expr), Ok(("'hello world'", "")));
        assert_eq!(eval("'hello\\''", &expr), Ok(("'hello\\''", "")));
        assert_eq!(eval("'hello\\'world'", &expr), Ok(("'hello\\'world'", "")));

        assert_eq!(eval("\"hello world\"", &expr), Ok(("\"hello world\"", "")));
        assert_eq!(eval("\"hello\\\"\"", &expr), Ok(("\"hello\\\"\"", "")));
        assert_eq!(
            eval("\"hello\\\"world\"", &expr),
            Ok(("\"hello\\\"world\"", ""))
        );
    }
}
