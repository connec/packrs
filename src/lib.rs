#![deny(missing_docs)]

//! Parsing expression grammar library.
//!
//! See [`Expression`], which represents valid parsing expression grammar expressions, and [`eval`],
//! which can evaluate them against a string.
//!
//! [`Expression`]: enum.Expression.html
//! [`eval`]: fn.eval.html

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
/// This will work rescursively to match the expression and evaluate any sub-expressions. Once the
/// terminals are reached, the outputs will propagate back up the stack until the overall result is
/// worked out.
///
/// **Note:** this implementation will likely be vulnerable to stack overflows, unless LLVM is very
/// clever.
pub fn eval<'a>(input: &'a str, expression: &Expression) -> Result<(&'a str, String), String> {
    match expression {
        Empty => Ok((input, "".to_string())),
        Any => input.chars().next().map_or_else(
            || Err("unexpected end of input".to_string()),
            |char| Ok((&input[1..], format!("{}", char))),
        ),
        Terminal(char) => {
            if input.starts_with(*char) {
                Ok((&input[1..], format!("{}", char)))
            } else {
                Err(format!("expected '{}'", char))
            }
        }
        Sequence(expr1, expr2) => {
            let (input1, mut result) = eval(input, expr1)?;
            let (input2, result2) = eval(input1, expr2)?;
            result.push_str(result2.as_str());
            Ok((input2, result))
        }
        OrderedChoice(expr1, expr2) => eval(input, expr1).or_else(|mut error| {
            eval(input, expr2).map_err(|error2| {
                error.push_str(" or ");
                error.push_str(&error2);
                error
            })
        }),
        ZeroOrMore(expr) => {
            let mut input = input;
            let mut output = String::new();
            while let Ok((input_, result)) = eval(input, expr) {
                input = input_;
                output.push_str(&result);
            }
            Ok((input, output))
        }
        OneOrMore(expr) => {
            let (mut input, mut output) = eval(input, expr)?;
            while let Ok((input_, result)) = eval(input, expr) {
                input = input_;
                output.push_str(&result);
            }
            Ok((input, output))
        }
        Optional(expr) => eval(input, expr).or_else(|_| Ok((input, "".to_string()))),
        AndPredicate(expr) => {
            eval(input, expr)?;
            Ok((input, "".to_string()))
        }
        NotPredicate(expr) => eval(input, expr).map_or_else(
            |_| Ok((input, "".to_string())),
            |_| Err("unexpected input".to_string()),
        ),
    }
}

#[cfg(test)]
mod tests {
    use crate::{eval, Expression::*};

    #[test]
    fn construct_empty() {
        let _ = Empty;
    }

    #[test]
    fn eval_empty() {
        let expr = Empty;
        assert_eq!(eval("", &expr), Ok(("", "".to_string())));
    }

    #[test]
    fn construct_any() {
        let _ = Any;
    }

    #[test]
    fn eval_any_ok() {
        let expr = Any;
        assert_eq!(eval("a", &expr), Ok(("", "a".to_string())));
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
        assert_eq!(eval("a", &expr), Ok(("", "a".to_string())));
    }

    #[test]
    fn eval_terminal_err() {
        let expr = Terminal('a');
        assert_eq!(eval("", &expr), Err("expected 'a'".to_string()));
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
        assert_eq!(eval("ab", &expr), Ok(("", "ab".to_string())));
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
        assert_eq!(eval("ab", &expr), Ok(("b", "a".to_string())));
    }

    #[test]
    fn eval_ordered_choice_ok2() {
        let a = Terminal('a');
        let b = Terminal('b');
        let expr = OrderedChoice(&a, &b);
        assert_eq!(eval("ba", &expr), Ok(("a", "b".to_string())));
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
        assert_eq!(eval("", &expr), Ok(("", "".to_string())));
    }

    #[test]
    fn eval_zero_or_more_ok_no_match() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("b", &expr), Ok(("b", "".to_string())));
    }

    #[test]
    fn eval_zero_or_more_ok_one() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("ab", &expr), Ok(("b", "a".to_string())));
    }

    #[test]
    fn eval_zero_or_more_ok_more() {
        let a = Terminal('a');
        let expr = ZeroOrMore(&a);
        assert_eq!(eval("aaab", &expr), Ok(("b", "aaa".to_string())));
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
        assert_eq!(eval("", &expr), Err("expected 'a'".to_string()));
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
        assert_eq!(eval("ab", &expr), Ok(("b", "a".to_string())));
    }

    #[test]
    fn eval_one_or_more_ok_more() {
        let a = Terminal('a');
        let expr = OneOrMore(&a);
        assert_eq!(eval("aaab", &expr), Ok(("b", "aaa".to_string())));
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
        assert_eq!(eval("", &expr), Ok(("", "".to_string())));
    }

    #[test]
    fn eval_optional_ok_no_match() {
        let a = Terminal('a');
        let expr = Optional(&a);
        assert_eq!(eval("b", &expr), Ok(("b", "".to_string())));
    }

    #[test]
    fn eval_optional_ok_match() {
        let a = Terminal('a');
        let expr = Optional(&a);
        assert_eq!(eval("ab", &expr), Ok(("b", "a".to_string())));
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
        assert_eq!(eval("a", &expr), Ok(("a", "".to_string())));
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
        assert_eq!(eval("b", &expr), Ok(("b", "".to_string())));
    }

    #[test]
    fn eval_not_predicate_err() {
        let a = Terminal('a');
        let expr = NotPredicate(&a);
        assert_eq!(eval("a", &expr), Err("unexpected input".to_string()));
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

        assert_eq!(
            eval("'hello world'", &expr),
            Ok(("", "'hello world'".to_string()))
        );
        assert_eq!(
            eval("'hello\\''", &expr),
            Ok(("", "'hello\\''".to_string()))
        );
        assert_eq!(
            eval("'hello\\'world'", &expr),
            Ok(("", "'hello\\'world'".to_string()))
        );

        assert_eq!(
            eval("\"hello world\"", &expr),
            Ok(("", "\"hello world\"".to_string()))
        );
        assert_eq!(
            eval("\"hello\\\"\"", &expr),
            Ok(("", "\"hello\\\"\"".to_string()))
        );
        assert_eq!(
            eval("\"hello\\\"world\"", &expr),
            Ok(("", "\"hello\\\"world\"".to_string()))
        );
    }
}
