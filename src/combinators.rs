//! Parsing combinator based PEG expression library.
//!
//! The parsing functions in this module, apart from [`parse`], are all
//! `impl Fn(..., &str) -> Result<V, E>`. The first arguments, if any, configure
//! the matching behaviour, and the `&str` argument is the input to match against.
//!
//! The [`Result<V, E>`] return value is a `std::result::Result` with either a [`Value`]`<V>` or a
//! [`Value`]`<E>`, depending on whether the parser matched successfully or not. See [`ParseResult`]
//! for convenience functions for working with them.
//!
//! [`parse`] is special – it takes a parsing function (`impl Fn(&str) -> Result<V, E>`), performs
//! the match, and then checks that there's no remaining input after the match, and returns a
//! [`ParseError`].
//!
//! [`Result<V, E>`]: type.Result.html
//! [`Value`]: struct.Value.html
//! [`ParseResult`]: trait.ParseResult.html
//! [`parse`]: fn.parse.html
//! [`ParseError`]: enum.ParseError.html

use std::cmp::{max, min};
use std::ops::Range;

/// A value generated from a parser.
///
/// This is used to record the `span` within the input that generated the value.
#[derive(Debug, PartialEq)]
pub struct Value<V> {
    /// The range in the input from which the `value` was derived.
    span: Range<usize>,

    /// The value.
    value: V,
}

impl<V> Value<V> {
    /// Offset the `span` of a value by the given amount.
    pub fn offset(mut self, offset: usize) -> Self {
        self.span.start += offset;
        self.span.end += offset;
        self
    }

    /// Replace this value with another.
    pub fn replace<U>(self, value: U) -> Value<U> {
        Value {
            span: self.span,
            value,
        }
    }

    /// Update the contained `value`.
    pub fn map<U>(self, f: impl Fn(V) -> U) -> Value<U> {
        Value {
            span: self.span,
            value: f(self.value),
        }
    }

    /// Merge another value into this one.
    ///
    /// The merged value will have the maximal span and the values will be combined using the given
    /// `merge` fn.
    pub fn merge<U, W>(self, other: Value<U>, merge: impl FnOnce(V, U) -> W) -> Value<W> {
        Value {
            span: min(self.span.start, other.span.start)..max(self.span.end, other.span.end),
            value: merge(self.value, other.value),
        }
    }
}

/// Convenience alias for parse results.
pub type Result<V, E> = std::result::Result<Value<V>, Value<E>>;

/// Represents the possible ways parsing might fail.
///
/// Parsing could fail for only two reasons:
/// - The combinator failed, or
/// - The combinator succeeded but didn't consume all the input.
#[derive(Debug, PartialEq)]
pub enum ParseError<E> {
    /// Indicates that parsing failed due to excess input.
    ExpectedEndOfInput,

    /// Indicates that parsing failed due to unexpected input.
    UnexpectedInput(E),
}

trait ParseResult<V, E> {
    fn map_value<U>(self, f: impl FnOnce(V) -> U) -> Result<U, E>;
    fn map_err_value<F>(self, f: impl FnOnce(E) -> F) -> Result<V, F>;
}

impl<V, E> ParseResult<V, E> for Result<V, E> {
    fn map_value<U>(self, f: impl FnOnce(V) -> U) -> Result<U, E> {
        self.map(|value| Value {
            span: value.span,
            value: f(value.value),
        })
    }

    fn map_err_value<F>(self, f: impl FnOnce(E) -> F) -> Result<V, F> {
        self.map_err(|value| Value {
            span: value.span,
            value: f(value.value),
        })
    }
}

/// Always matches, regardless of the input (even if empty).
///
/// Outputs an empty string.
pub fn empty<E>(_input: &str) -> Result<(), E> {
    Ok(Value {
        span: 0..0,
        value: (),
    })
}

/// Matches any single character.
///
/// Outputs the matched character, as a string, as output.
///
/// Fails if the input is empty (with "unexpected end of input").
pub fn any(input: &str) -> Result<&str, &'static str> {
    let length = match input.chars().next() {
        Some(chr) => chr.len_utf8(),
        None => {
            return Err(Value {
                span: 0..0,
                value: "unexpected end of input",
            })
        }
    };
    Ok(Value {
        span: 0..length,
        value: &input[..length],
    })
}

/// Matches a specific character.
///
/// Outputs the matched character, as a string, as output.
///
/// Fails if the input does not start with the given character (with "expected '{expected}'").
/// Fails if the input is empty (with 'unexpected end of input').
pub fn chr(expected: char, input: &str) -> Result<&str, String> {
    let actual = match input.chars().next() {
        Some(actual) => actual,
        None => {
            return Err(Value {
                span: 0..0,
                value: "unexpected end of input".to_string(),
            })
        }
    };

    let length = actual.len_utf8();
    if actual != expected {
        Err(Value {
            span: 0..length,
            value: format!("expected '{}'", expected),
        })
    } else {
        Ok(Value {
            span: 0..length,
            value: &input[..length],
        })
    }
}

/// Matches two given sub-expressions in sequence.
///
/// Outputs the concatenated outputs of the sub-expressions.
///
/// If either of the sub-expressions fail, the failure is propagated.
pub fn seq<'a, V1, V2, E>(
    expr1: impl Fn(&'a str) -> Result<V1, E>,
    expr2: impl Fn(&'a str) -> Result<V2, E>,
    input: &'a str,
) -> Result<(V1, V2), E> {
    let value1 = expr1(input)?;
    let value2 = expr2(&input[value1.span.end..]).map_err(|err| err.offset(value1.span.end))?;

    Ok(Value {
        span: 0..(value1.span.end + value2.span.end),
        value: (value1.value, value2.value),
    })
}

/// Matches one of the given sub-expressions.
///
/// The sub-expressions are attempted in order – when one succeeds the result is returned.
///
/// If both of the sub-expressions fail, the failure messages are returned as a tuple.
pub fn choose<'a, V, E1, E2>(
    expr1: impl Fn(&'a str) -> Result<V, E1>,
    expr2: impl Fn(&'a str) -> Result<V, E2>,
    input: &'a str,
) -> std::result::Result<Value<V>, (Value<E1>, Value<E2>)> {
    let error1 = match expr1(input) {
        Ok(value) => return Ok(value),
        Err(error) => error,
    };
    let error2 = match expr2(input) {
        Ok(value) => return Ok(value),
        Err(error) => error,
    };
    Err((error1, error2))
}

/// Matches the given sub-expression zero or more times.
///
/// Outputs the concatenated outputs from successful matches of the sub-expression.
///
/// This expression never fails.
pub fn zero_or_more<'a, V, E>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    input: &'a str,
) -> Result<Vec<V>, E> {
    let mut values = vec![];
    let mut last_end = 0;
    while let Ok(value) = expr(&input[last_end..]) {
        let value = value.offset(last_end);
        values.push(value.value);
        last_end = value.span.end;
    }
    Ok(Value {
        span: 0..last_end,
        value: values,
    })
}

/// Matches the given sub-expression one or more times.
///
/// Outputs the concatenated outputs from successful matches of the sub-expression.
///
/// If the sub-expression fails the first match, the failure is propagated.
pub fn one_or_more<'a, V, E>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    input: &'a str,
) -> Result<Vec<V>, E> {
    let value = expr(input)?;
    let mut values = vec![value.value];
    let mut last_end = value.span.end;
    while let Ok(value) = expr(&input[last_end..]) {
        let value = value.offset(last_end);
        values.push(value.value);
        last_end = value.span.end;
    }
    Ok(Value {
        span: 0..last_end,
        value: values,
    })
}

/// Matches the given sub-expression once, without propagating failure.
///
/// Outputs the result of the sub-expression on a successful match, or an empty string otherwise.
///
/// This expression never fails.
pub fn optional<'a, V, E>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    input: &'a str,
) -> Result<Option<V>, E> {
    expr(input).map(|v| v.map(Some)).or_else(|_| {
        Ok(Value {
            span: 0..0,
            value: None,
        })
    })
}

/// Matches the given sub-expression without consuming input.
///
/// Outputs the empty string.
///
/// If the sub-expression fails, the failure is propagated.
pub fn check<'a, V, E>(expr: impl Fn(&'a str) -> Result<V, E>, input: &'a str) -> Result<(), E> {
    expr(input)?;
    Ok(Value {
        span: 0..0,
        value: (),
    })
}

/// Matches the given sub-expression without consuming input and inverts the result.
///
/// Outputs an empty string if the sub-expression fails.
///
/// Fail with "unexpected input" if the sub-expression matches.
pub fn reject<'a, V, E>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    input: &'a str,
) -> Result<(), &'static str> {
    match expr(input) {
        Ok(value) => Err(Value {
            span: value.span,
            value: "unexpected input",
        }),
        Err(_) => Ok(Value {
            span: 0..0,
            value: (),
        }),
    }
}

/// Matches the given sub-expression and checks there's no input left.
///
/// Returns the sub-expression output if it succeeds.
///
/// Fails with the sub-expression failure, or with "expected end of input" if there is input left
/// after running the sub-expression.
pub fn parse<'a, V, E>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    input: &'a str,
) -> std::result::Result<V, Value<ParseError<E>>> {
    expr(input)
        .map_err_value(ParseError::UnexpectedInput)
        .and_then(|value| {
            if value.span.end == input.len() {
                Ok(value.value)
            } else {
                Err(Value {
                    span: value.span.end..value.span.end,
                    value: ParseError::ExpectedEndOfInput,
                })
            }
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::convert::Infallible;

    #[test]
    fn empty_ok_when_input_is_empty() {
        assert_eq!(
            empty::<Infallible>(""),
            Ok(Value {
                span: 0..0,
                value: ()
            })
        );
    }

    #[test]
    fn empty_ok_when_input_is_nonempty() {
        assert_eq!(
            empty::<Infallible>("hello"),
            Ok(Value {
                span: 0..0,
                value: ()
            })
        );
    }

    #[test]
    fn any_err_when_input_is_empty() {
        assert_eq!(
            any(""),
            Err(Value {
                span: 0..0,
                value: "unexpected end of input"
            })
        );
    }

    #[test]
    fn any_ok_when_input_is_nonempty() {
        assert_eq!(
            any("hello"),
            Ok(Value {
                span: 0..1,
                value: "h"
            })
        );
    }

    #[test]
    fn any_ok_when_input_contains_multibyte_char() {
        let input = "y̆";
        let value1 = any(input).unwrap();
        let value2 = any(&input[value1.span.end..]).unwrap();

        assert_eq!(value1.value, "y");
        assert_eq!(value1.span, 0..1);
        assert_eq!(value2.value, "\u{306}");
        assert_eq!(value2.span, 0..2);
        assert_eq!(&format!("{}{}", value1.value, value2.value), "y̆");
    }

    #[test]
    fn chr_err_when_input_is_empty() {
        assert_eq!(
            chr('a', ""),
            Err(Value {
                span: 0..0,
                value: "unexpected end of input".to_string()
            })
        );
    }

    #[test]
    fn chr_err_when_input_does_not_match() {
        assert_eq!(
            chr('a', "hello"),
            Err(Value {
                span: 0..1,
                value: "expected 'a'".to_string()
            })
        );
    }

    #[test]
    fn chr_ok_when_input_matches() {
        assert_eq!(
            chr('h', "hello"),
            Ok(Value {
                span: 0..1,
                value: "h"
            })
        );
    }

    #[test]
    fn chr_ok_when_multibyte_input_matches() {
        assert_eq!(
            chr('y', "y̆"),
            Ok(Value {
                span: 0..1,
                value: "y"
            })
        );
        assert_eq!(
            chr('\u{306}', "\u{306}"),
            Ok(Value {
                span: 0..2,
                value: "\u{306}"
            })
        );
    }

    #[test]
    fn seq_err_when_first_expr_err() {
        assert_eq!(
            seq(any, empty, ""),
            Err(Value {
                span: 0..0,
                value: "unexpected end of input"
            })
        );
    }

    #[test]
    fn seq_err_when_second_expr_err() {
        assert_eq!(
            seq(any, any, "\u{306}"),
            Err(Value {
                span: 2..2,
                value: "unexpected end of input"
            })
        );
    }

    #[test]
    fn seq_ok_when_both_expr_ok() {
        assert_eq!(
            seq(|i| chr('y', i), |i| chr('\u{306}', i), "y̆o"),
            Ok(Value {
                span: 0..3,
                value: ("y", "\u{306}")
            })
        );
    }

    #[test]
    fn choose_err_when_both_expr_err() {
        assert_eq!(
            choose(any, any, ""),
            Err((
                Value {
                    span: 0..0,
                    value: "unexpected end of input"
                },
                Value {
                    span: 0..0,
                    value: "unexpected end of input"
                }
            ))
        );
    }

    #[test]
    fn choose_ok_when_first_expr_ok() {
        assert_eq!(
            choose(any, |i| chr('a', i), "hello"),
            Ok(Value {
                span: 0..1,
                value: "h"
            })
        );
    }

    #[test]
    fn choose_ok_when_second_expr_ok() {
        assert_eq!(
            choose(|i| chr('a', i), any, "hello"),
            Ok(Value {
                span: 0..1,
                value: "h"
            })
        );
    }

    #[test]
    fn zero_or_more_ok_when_no_match() {
        assert_eq!(
            zero_or_more(any, ""),
            Ok(Value {
                span: 0..0,
                value: vec![],
            })
        );
    }

    #[test]
    fn zero_or_more_ok_when_one_match() {
        assert_eq!(
            zero_or_more(|i| chr('h', i), "hello"),
            Ok(Value {
                span: 0..1,
                value: vec!["h"]
            })
        );
    }

    #[test]
    fn zero_or_more_ok_when_multi_match() {
        assert_eq!(
            zero_or_more(|i| seq(|i| chr('y', i), |i| chr('\u{306}', i), i), "y̆o"),
            Ok(Value {
                span: 0..3,
                value: vec![("y", "\u{306}")]
            })
        );
    }

    #[test]
    fn zero_or_more_ok_when_all_match() {
        assert_eq!(
            zero_or_more(any, "hello"),
            Ok(Value {
                span: 0..5,
                value: vec!["h", "e", "l", "l", "o"]
            })
        );
    }

    #[test]
    fn one_or_more_err_when_no_match() {
        assert_eq!(
            one_or_more(any, ""),
            Err(Value {
                span: 0..0,
                value: "unexpected end of input"
            })
        );
    }

    #[test]
    fn one_or_more_ok_when_one_match() {
        assert_eq!(
            one_or_more(|i| chr('h', i), "hello"),
            Ok(Value {
                span: 0..1,
                value: vec!["h"]
            })
        );
    }

    #[test]
    fn one_or_more_ok_when_multi_match() {
        assert_eq!(
            one_or_more(|i| seq(|i| chr('y', i), |i| chr('\u{306}', i), i), "y̆o"),
            Ok(Value {
                span: 0..3,
                value: vec![("y", "\u{306}")]
            })
        );
    }

    #[test]
    fn one_or_more_ok_when_all_match() {
        assert_eq!(
            one_or_more(any, "hello"),
            Ok(Value {
                span: 0..5,
                value: vec!["h", "e", "l", "l", "o"]
            })
        );
    }

    #[test]
    fn optional_ok_when_no_match() {
        assert_eq!(
            optional(any, ""),
            Ok(Value {
                span: 0..0,
                value: None
            })
        );
    }

    #[test]
    fn optional_ok_when_match() {
        assert_eq!(
            optional(any, "hello"),
            Ok(Value {
                span: 0..1,
                value: Some("h")
            })
        );
    }

    #[test]
    fn check_err_when_no_match() {
        assert_eq!(
            check(any, ""),
            Err(Value {
                span: 0..0,
                value: "unexpected end of input"
            })
        );
    }

    #[test]
    fn check_ok_when_match() {
        assert_eq!(
            check(any, "hello"),
            Ok(Value {
                span: 0..0,
                value: ()
            })
        );
    }

    #[test]
    fn reject_err_when_match() {
        assert_eq!(
            reject(any, "hello"),
            Err(Value {
                span: 0..1,
                value: "unexpected input"
            })
        );
    }

    #[test]
    fn reject_ok_when_no_match() {
        assert_eq!(
            reject(|i| chr('a', i), "hello"),
            Ok(Value {
                span: 0..0,
                value: ()
            })
        );
    }

    #[test]
    fn parse_err_when_no_match() {
        assert_eq!(
            parse(any, ""),
            Err(Value {
                span: 0..0,
                value: ParseError::UnexpectedInput("unexpected end of input")
            })
        );
    }

    #[test]
    fn parse_err_when_match_and_remainder() {
        assert_eq!(
            parse(any, "hello"),
            Err(Value {
                span: 1..1,
                value: ParseError::ExpectedEndOfInput
            })
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
        use StringError::*;

        #[derive(Debug, PartialEq)]
        enum StringError {
            InvalidOpener,
            MissingCloser(char),
        }

        fn inner<'a>(
            quote: impl Fn(&'a str) -> Result<(), String>,
            input: &'a str,
        ) -> Value<String> {
            zero_or_more(
                |i| {
                    seq(
                        |i| {
                            choose(
                                |i| chr('\\', i),
                                |i| reject(&quote, i).map_value(|()| ""),
                                i,
                            )
                            .map_err(|(e1, e2)| e1.merge(e2, |_, _| ()))
                        },
                        |i| any(i).map_err_value(|_| ()),
                        i,
                    )
                    .map_value(|v| match v {
                        ("\\", s) => s.to_string(),
                        (s1, s2) => format!("{}{}", s1, s2),
                    })
                },
                input,
            )
            .map_value(|v| v.into_iter().collect())
            .unwrap_or_else(|v| v.replace(String::new()))
        }

        fn quoted(quote: char, input: &str) -> Result<String, StringError> {
            let quote_ = |i| chr(quote, i).map_value(|_| ());
            seq(
                |i| quote_(i).map_err_value(|_| InvalidOpener),
                |i| {
                    seq(
                        |i| Ok(inner(&quote_, i)),
                        |i| quote_(i).map_err_value(|_| MissingCloser(quote)),
                        i,
                    )
                },
                input,
            )
            .map_value(|(_, (s, _))| s)
            .map_err(|e| e)
        }

        fn string(input: &str) -> std::result::Result<String, Value<ParseError<StringError>>> {
            parse(
                |i| {
                    choose(|i| quoted('\'', i), |i| quoted('"', i), i).map_err(
                        |errors| match errors {
                            (
                                error
                                @
                                Value {
                                    value: MissingCloser(_),
                                    ..
                                },
                                _,
                            ) => error,
                            (
                                _,
                                error
                                @
                                Value {
                                    value: MissingCloser(_),
                                    ..
                                },
                            ) => error,
                            (error, _) => error,
                        },
                    )
                },
                input,
            )
        }

        assert_eq!(string("'hello world'"), Ok("hello world".to_string()));
        assert_eq!(string("'hello\\''"), Ok("hello'".to_string()));
        assert_eq!(string("'hello\\'world'"), Ok("hello'world".to_string()));

        assert_eq!(string("\"hello world\""), Ok("hello world".to_string()));
        assert_eq!(string("\"hello\\\"\""), Ok("hello\"".to_string()));
        assert_eq!(string("\"hello\\\"world\""), Ok("hello\"world".to_string()));

        assert_eq!(
            string("'hello \\'"),
            Err(Value {
                span: 9..9,
                value: ParseError::UnexpectedInput(MissingCloser('\''))
            })
        );
        assert_eq!(
            string("'hello'world"),
            Err(Value {
                span: 7..7,
                value: ParseError::ExpectedEndOfInput,
            })
        );
        assert_eq!(
            string("wow"),
            Err(Value {
                span: 0..1,
                value: ParseError::UnexpectedInput(InvalidOpener),
            })
        );
    }

    #[test]
    fn trivial_calculator() {
        #[derive(Debug, PartialEq)]
        enum Error {
            InvalidNumber,
            InvalidOperator,
        }
        impl std::fmt::Display for Error {
            fn fmt(
                &self,
                fmt: &mut std::fmt::Formatter<'_>,
            ) -> std::result::Result<(), std::fmt::Error> {
                write!(fmt, "{:?}", self)
            }
        }
        enum Op {
            Add,
            Subtract,
        }
        fn num(input: &str) -> Result<i32, Error> {
            choose(
                |i| chr('1', i).map_value(|_| 1),
                |i| chr('2', i).map_value(|_| 2),
                input,
            )
            .map_err(|(e1, e2)| e1.merge(e2, |_, _| Error::InvalidNumber))
        }
        fn op(input: &str) -> Result<Op, Error> {
            choose(
                |i| chr('+', i).map_value(|_| Op::Add),
                |i| chr('-', i).map_value(|_| Op::Subtract),
                input,
            )
            .map_err(|(e1, e2)| e1.merge(e2, |_, _| Error::InvalidOperator))
        }
        fn expr(input: &str) -> Result<i32, Error> {
            seq(|i| num(i), |i| seq(|i| op(i), |i| num(i), i), input).map_value(|v| match v {
                (a, (Op::Add, b)) => a + b,
                (a, (Op::Subtract, b)) => a - b,
            })
        }
        assert_eq!(parse(expr, "1+1"), Ok(2));
        assert_eq!(parse(expr, "1-2"), Ok(-1));
        assert_eq!(
            parse(expr, "hello"),
            Err(Value {
                span: 0..1,
                value: ParseError::UnexpectedInput(Error::InvalidNumber)
            })
        );
        assert_eq!(
            parse(expr, "1/2"),
            Err(Value {
                span: 1..2,
                value: ParseError::UnexpectedInput(Error::InvalidOperator)
            })
        );
        assert_eq!(
            parse(expr, "1-x"),
            Err(Value {
                span: 2..3,
                value: ParseError::UnexpectedInput(Error::InvalidNumber)
            })
        );
    }
}
