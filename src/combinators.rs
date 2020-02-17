//! Parsing combinator based PEG expression library.
//!
//! The functions in this module, apart from [`parse`], are all
//! `impl Fn(..., &str) -> Match`. The first arguments, if any, configure
//! the matching behaviour, and the `&str` argument is the input to match against.
//!
//! If matches succeed, the function will return a [`Match`] enum. The `Success` variant includes
//! the length of the match in the input string, and the `value` of the match. The `Failure` variant
//! includes a `String` explaining the error.
//!
//! [`parse`] is special – it takes a matching function
//! (`impl Fn(&str) -> Match`), performs the match, and then checks that there's no remaining input
//! after the match.
//!
//! This is even less ergonomic than [`Expression`] for creating parsers, but it's significantly
//! more composable, e.g.;
//!
//! ```
//! use packrs::combinators::{self, any, choose, chr, parse, reject, seq, zero_or_more, Match};
//!
//! fn string(input: &str) -> Result<&str, String> {
//!     parse(
//!         |i| choose(
//!             |i| quoted(|i| chr('\'', i), i),
//!             |i| quoted(|i| chr('"', i), i),
//!             i
//!         ),
//!         input
//!     )
//! }
//!
//! fn quoted(quote: impl Fn(&str) -> Match, input: &str) -> Match {
//!     seq(&quote, |i| seq(|i| string_inner(&quote, i), &quote, i), input)
//! }
//!
//! fn string_inner(quote: impl Fn(&str) -> Match, input: &str) -> Match {
//!     zero_or_more(
//!         |i| seq(
//!             |i| choose(|i| chr('\\', i), |i| reject(&quote, i), i),
//!             any,
//!             i,
//!         ),
//!         input,
//!     )
//! }
//!
//! assert_eq!(
//!     string("'hello \\' world'"),
//!     Ok("'hello \\' world'"),
//! );
//! ```
//!
//! [`parse`]: fn.parse.html
//! [`Match`]: enum.Match.html
//! [`Expression`]: ../expression/enum.Expression.html

use self::Match::*;

/// Represents an intermediate parse result.
///
/// This should be made private at some point.
#[derive(Debug, PartialEq)]
pub enum Match<'a> {
    /// Indicates a successful match.
    Success {
        /// The length of this match in the input.
        length: usize,

        /// The value of this match.
        value: &'a str,
    },

    /// Indicates a failed match.
    Failure {
        /// A message hinting the cause of the failure.
        message: String,
    },
}

/// Always matches, regardless of the input (even if empty).
///
/// Outputs an empty string.
pub fn empty(_input: &str) -> Match {
    Success {
        length: 0,
        value: "",
    }
}

/// Matches any single character.
///
/// Outputs the matched character, as a string, as output.
///
/// Fails if the input is empty (with "unexpected end of input").
pub fn any(input: &str) -> Match {
    let length = match input.chars().next() {
        Some(chr) => chr.len_utf8(),
        None => {
            return Failure {
                message: "unexpected end of input".to_string(),
            }
        }
    };
    Success {
        length,
        value: &input[..length],
    }
}

/// Matches a specific character.
///
/// Outputs the matched character, as a string, as output.
///
/// Fails if the input does not start with the given character (with "expected '{expected}'").
/// Fails if the input is empty (with 'unexpected end of input').
pub fn chr(expected: char, input: &str) -> Match {
    let actual = match input.chars().next() {
        Some(actual) => actual,
        None => {
            return Failure {
                message: "unexpected end of input".to_string(),
            }
        }
    };

    if actual != expected {
        Failure {
            message: format!("expected '{}'", expected),
        }
    } else {
        Success {
            length: actual.len_utf8(),
            value: &input[..actual.len_utf8()],
        }
    }
}

/// Matches two given sub-expressions in sequence.
///
/// Outputs the concatenated outputs of the sub-expressions.
///
/// If either of the sub-expressions fail, the failure is propagated.
pub fn seq(expr1: impl Fn(&str) -> Match, expr2: impl Fn(&str) -> Match, input: &str) -> Match {
    let (length1, _) = match expr1(input) {
        Success { length, value } => (length, value),
        failure => return failure,
    };
    let (length2, _) = match expr2(&input[length1..]) {
        Success { length, value } => (length, value),
        failure => return failure,
    };

    Success {
        length: length1 + length2,
        value: &input[..length1 + length2],
    }
}

/// Matches one of the given sub-expressions.
///
/// The sub-expressions are attempted in order – when one succeeds the result is returned.
///
/// If both of the sub-expressions fail, the failure messages are combined with " or ".
pub fn choose(expr1: impl Fn(&str) -> Match, expr2: impl Fn(&str) -> Match, input: &str) -> Match {
    let message1 = match expr1(input) {
        Failure { message } => message,
        match_ => return match_,
    };
    let message2 = match expr2(input) {
        Failure { message } => message,
        match_ => return match_,
    };
    Failure {
        message: message1 + " or " + &message2,
    }
}

/// Matches the given sub-expression zero or more times.
///
/// Outputs the concatenated outputs from successful matches of the sub-expression.
///
/// This expression never fails.
pub fn zero_or_more(expr: impl Fn(&str) -> Match, input: &str) -> Match {
    let mut length = 0;
    while let Success {
        length: length_, ..
    } = expr(&input[length..])
    {
        length += length_;
    }
    Success {
        length,
        value: &input[..length],
    }
}

/// Matches the given sub-expression one or more times.
///
/// Outputs the concatenated outputs from successful matches of the sub-expression.
///
/// If the sub-expression fails the first match, the failure is propagated.
pub fn one_or_more(expr: impl Fn(&str) -> Match, input: &str) -> Match {
    let mut length = match expr(input) {
        Success { length, .. } => length,
        failure => return failure,
    };
    while let Success {
        length: length_, ..
    } = expr(&input[length..])
    {
        length += length_;
    }
    Success {
        length,
        value: &input[..length],
    }
}

/// Matches the given sub-expression once, without propagating failure.
///
/// Outputs the result of the sub-expression on a successful match, or an empty string otherwise.
///
/// This expression never fails.
pub fn optional(expr: impl Fn(&str) -> Match, input: &str) -> Match {
    match expr(input) {
        match_ @ Success { .. } => match_,
        _ => Success {
            length: 0,
            value: "",
        },
    }
}

/// Matches the given sub-expression without consuming input.
///
/// Outputs the empty string.
///
/// If the sub-expression fails, the failure is propagated.
pub fn check(expr: impl Fn(&str) -> Match, input: &str) -> Match {
    if let failure @ Failure { .. } = expr(input) {
        failure
    } else {
        Success {
            length: 0,
            value: "",
        }
    }
}

/// Matches the given sub-expression without consuming input and inverts the result.
///
/// Outputs an empty string if the sub-expression fails.
///
/// Fail with "unexpected input" if the sub-expression matches.
pub fn reject(expr: impl Fn(&str) -> Match, input: &str) -> Match {
    if let Success { .. } = expr(input) {
        Failure {
            message: "unexpected input".to_string(),
        }
    } else {
        Success {
            length: 0,
            value: "",
        }
    }
}

/// Matches the given sub-expression and checks there's no input left.
///
/// Returns the sub-expression output if it succeeds.
///
/// Fails with the sub-expression failure, or with "expected end of input" if there is input left after running sub-expression.
pub fn parse(expr: impl Fn(&str) -> Match, input: &str) -> std::result::Result<&str, String> {
    match expr(input) {
        Success { length, value } if length == input.len() => Ok(value),
        Success { .. } => Err("expected end of input".to_string()),
        Failure { message } => Err(message),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_ok_when_input_is_empty() {
        assert_eq!(
            empty(""),
            Success {
                length: 0,
                value: ""
            }
        );
    }

    #[test]
    fn empty_ok_when_input_is_nonempty() {
        assert_eq!(
            empty("hello"),
            Success {
                length: 0,
                value: ""
            }
        );
    }

    #[test]
    fn any_err_when_input_is_empty() {
        assert_eq!(
            any(""),
            Failure {
                message: "unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn any_ok_when_input_is_nonempty() {
        assert_eq!(
            any("hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn any_ok_when_input_contains_multibyte_char() {
        let input1 = "y̆";
        let (length1, value1) = match any(input1) {
            Success { length, value } => (length, value),
            Failure { message } => panic!(message),
        };
        let (length2, value2) = match any(&input1[length1..]) {
            Success { length, value } => (length, value),
            Failure { message } => panic!(message),
        };

        assert_eq!(value1, "y");
        assert_eq!(length1, 1);
        assert_eq!(value2, "\u{306}");
        assert_eq!(length2, 2);
        assert_eq!(value1.to_string() + value2, "y̆".to_string());
    }

    #[test]
    fn chr_err_when_input_is_empty() {
        assert_eq!(
            chr('a', ""),
            Failure {
                message: "unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn chr_err_when_input_does_not_match() {
        assert_eq!(
            chr('a', "hello"),
            Failure {
                message: "expected 'a'".to_string()
            }
        );
    }

    #[test]
    fn chr_ok_when_input_matches() {
        assert_eq!(
            chr('h', "hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn chr_ok_when_multibyte_input_matches() {
        assert_eq!(
            chr('y', "y̆"),
            Success {
                length: 1,
                value: "y"
            }
        );
        assert_eq!(
            chr('\u{306}', "\u{306}"),
            Success {
                length: 2,
                value: "\u{306}"
            }
        );
    }

    #[test]
    fn seq_err_when_first_expr_err() {
        assert_eq!(
            seq(any, empty, ""),
            Failure {
                message: "unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn seq_err_when_second_expr_err() {
        assert_eq!(
            seq(empty, any, ""),
            Failure {
                message: "unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn seq_ok_when_both_expr_ok() {
        assert_eq!(
            seq(|i| chr('y', i), |i| chr('\u{306}', i), "y̆o"),
            Success {
                length: 3,
                value: "y̆"
            }
        );
    }

    #[test]
    fn choose_err_when_both_expr_err() {
        assert_eq!(
            choose(any, any, ""),
            Failure {
                message: "unexpected end of input or unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn choose_ok_when_first_expr_ok() {
        assert_eq!(
            choose(any, |i| chr('a', i), "hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn choose_ok_when_second_expr_ok() {
        assert_eq!(
            choose(|i| chr('a', i), any, "hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn zero_or_more_ok_when_no_match() {
        assert_eq!(
            zero_or_more(any, ""),
            Success {
                length: 0,
                value: ""
            }
        );
    }

    #[test]
    fn zero_or_more_ok_when_one_match() {
        assert_eq!(
            zero_or_more(|i| chr('h', i), "hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn zero_or_more_ok_when_multi_match() {
        assert_eq!(
            zero_or_more(|i| seq(|i| chr('y', i), |i| chr('\u{306}', i), i), "y̆o"),
            Success {
                length: 3,
                value: "y̆"
            }
        );
    }

    #[test]
    fn zero_or_more_ok_when_all_match() {
        assert_eq!(
            zero_or_more(any, "hello"),
            Success {
                length: 5,
                value: "hello"
            }
        );
    }

    #[test]
    fn one_or_more_err_when_no_match() {
        assert_eq!(
            one_or_more(any, ""),
            Failure {
                message: "unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn one_or_more_ok_when_one_match() {
        assert_eq!(
            one_or_more(|i| chr('h', i), "hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn one_or_more_ok_when_multi_match() {
        assert_eq!(
            one_or_more(|i| seq(|i| chr('y', i), |i| chr('\u{306}', i), i), "y̆o"),
            Success {
                length: 3,
                value: "y̆"
            }
        );
    }

    #[test]
    fn one_or_more_ok_when_all_match() {
        assert_eq!(
            one_or_more(any, "hello"),
            Success {
                length: 5,
                value: "hello"
            }
        );
    }

    #[test]
    fn optional_ok_when_no_match() {
        assert_eq!(
            optional(any, ""),
            Success {
                length: 0,
                value: ""
            }
        );
    }

    #[test]
    fn optional_ok_when_match() {
        assert_eq!(
            optional(any, "hello"),
            Success {
                length: 1,
                value: "h"
            }
        );
    }

    #[test]
    fn check_err_when_no_match() {
        assert_eq!(
            check(any, ""),
            Failure {
                message: "unexpected end of input".to_string()
            }
        );
    }

    #[test]
    fn check_ok_when_match() {
        assert_eq!(
            check(any, "hello"),
            Success {
                length: 0,
                value: ""
            }
        );
    }

    #[test]
    fn reject_err_when_match() {
        assert_eq!(
            reject(any, "hello"),
            Failure {
                message: "unexpected input".to_string()
            }
        );
    }

    #[test]
    fn reject_ok_when_no_match() {
        assert_eq!(
            reject(|i| chr('a', i), "hello"),
            Success {
                length: 0,
                value: ""
            }
        );
    }

    #[test]
    fn parse_err_when_no_match() {
        assert_eq!(parse(any, ""), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn parse_err_when_match_and_remainder() {
        assert_eq!(
            parse(any, "hello"),
            Err("expected end of input".to_string())
        );
    }

    #[test]
    fn parse_ok_when_match_and_no_remainder() {
        assert_eq!(parse(any, "h"), Ok("h"));
    }

    #[test]
    fn parse_quoted_strings() {
        // String:
        //   '\'' ( ( '\\' / !'\'' ) . )* '\''
        // / '"'  ( ( '\\' / !'"'  ) . )* '"'

        fn inner(quote: impl Fn(&str) -> Match, input: &str) -> Match {
            zero_or_more(
                |i| {
                    seq(
                        |i| choose(|i| chr('\\', i), |i| reject(&quote, i), i),
                        any,
                        i,
                    )
                },
                input,
            )
        }

        fn quoted(quote: impl Fn(&str) -> Match, input: &str) -> Match {
            seq(&quote, |i| seq(|i| inner(&quote, i), &quote, i), input)
        }

        fn string(input: &str) -> std::result::Result<&str, String> {
            fn sq(input: &str) -> Match {
                chr('\'', input)
            }
            fn dq(input: &str) -> Match {
                chr('"', input)
            }
            parse(|i| choose(|i| quoted(sq, i), |i| quoted(dq, i), i), input)
        }

        assert_eq!(string("'hello world'"), Ok("'hello world'"));
        assert_eq!(string("'hello\\''"), Ok("'hello\\''"));
        assert_eq!(string("'hello\\'world'"), Ok("'hello\\'world'"));

        assert_eq!(string("\"hello world\""), Ok("\"hello world\""));
        assert_eq!(string("\"hello\\\"\""), Ok("\"hello\\\"\""));
        assert_eq!(string("\"hello\\\"world\""), Ok("\"hello\\\"world\""));

        assert_eq!(
            string("'hello \\'"),
            Err("unexpected end of input or expected '\"'".to_string())
        );
        assert_eq!(
            string("'hello'world"),
            Err("expected end of input".to_string())
        );
    }
}
