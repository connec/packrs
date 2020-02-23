//! A test to see if 'curried' combinators are possible.
//!
//! Ultimately, the goal with this is to support something like:
//!
//! ```
//! use packrs::combinators2::{chr, map, or, Value};
//! let num = or(map(chr('1'), |_| 1), map(chr('2'), |_| 2));
//! assert_eq!(num("1"), Ok(Value { span: 0..1, value: 1 }));
//! ```

use core::cmp::{max, min};
use core::ops::Range;

/// A value generated from a parser.
///
/// This is used to record the `span` within the input that generated the value.
#[derive(Debug, PartialEq)]
pub struct Value<T> {
    /// The range within an input.
    ///
    /// Given the `input`, the source for the value can be retrieved with:
    ///
    /// ```
    /// # use packrs::combinators2::Value;
    /// let input = "hello world";
    /// let value = Value {
    ///     span: 6..11,
    ///     value: ()
    /// };
    /// let source = &input[value.span];
    /// ```
    pub span: Range<usize>,

    /// The value.
    pub value: T,
}

impl<T> Value<T> {
    /// Offset the value's `span` based on the given `end`.
    fn offset(mut self, end: usize) -> Self {
        self.span.start += end;
        self.span.end += end;
        self
    }

    /// Combine two values into a single value containing a tuple of the given values.
    fn join<U>(self, other: Value<U>) -> Value<(Self, Value<U>)> {
        Value {
            span: min(self.span.start, other.span.start)..max(self.span.end, other.span.end),
            value: (self, other),
        }
    }
}

/// Represents the possible ways parsers might fail.
///
/// This is used to unify the error types from the parse functions.
#[derive(Debug, PartialEq)]
pub enum ParseError {
    /// Indicates that parsing failed because an expected character was not present.
    ExpectedChar(char),

    /// Indicates that parsing failed due to extraneous input.
    ExpectedEndOfInput,
}

type Result<V, E = ParseError> = std::result::Result<Value<V>, Value<E>>;

trait ParseResult {
    fn offset(self, end: usize) -> Self;
}

impl<V, E> ParseResult for Result<V, E> {
    fn offset(self, end: usize) -> Self {
        self.map(|value| value.offset(end))
            .map_err(|value| value.offset(end))
    }
}

/// Match end of input.
///
/// When given an input, this will check if it is empty. If it is, the parse will succeed with an
/// empty tuple (`()`). If it is not, the parse will fail with `ParseError::ExpectedEndOfInput`.
pub fn end() -> impl Fn(&str) -> Result<()> {
    move |input| {
        if input.is_empty() {
            Ok(Value {
                span: 0..0,
                value: (),
            })
        } else {
            Err(Value {
                span: 0..0,
                value: ParseError::ExpectedEndOfInput,
            })
        }
    }
}

/// Match a specific character.
///
/// When given an input, this will check if it begins with the `expected` character. If it does, the
/// parse will succeed with the slice of the input containing the character. If it does not, the
/// parse will fail with `ParseError::ExpectedChar(expected)`.
pub fn chr(expected: char) -> impl Fn(&str) -> Result<&str> {
    move |input| {
        let actual = match input.chars().next() {
            Some(actual) => actual,
            None => {
                return Err(Value {
                    span: 0..0,
                    value: ParseError::ExpectedChar(expected),
                })
            }
        };

        let length = actual.len_utf8();
        if actual != expected {
            Err(Value {
                span: 0..length,
                value: ParseError::ExpectedChar(expected),
            })
        } else {
            Ok(Value {
                span: 0..length,
                value: &input[..length],
            })
        }
    }
}

/// Match the first sub-expression and the second sub-expression.
///
/// When given an input, the input will be evaluated against the first sub-expression. If it
/// succeeds, the remaining input will be evaluated against the second sub-expression. If that also
/// succeeds, a tuple of the two results is returned. If either fails, the failure is returned.
pub fn and<'a, V1, V2, E>(
    expr1: impl Fn(&'a str) -> Result<V1, E>,
    expr2: impl Fn(&'a str) -> Result<V2, E>,
) -> impl Fn(&'a str) -> Result<(Value<V1>, Value<V2>), E> {
    move |input| {
        let value1 = expr1(input)?;
        let value2 = expr2(&input[value1.span.end..]).offset(value1.span.end)?;
        Ok(Value::join(value1, value2))
    }
}

/// Match the first sub-expression or the second sub-expression.
///
/// When given an input, the input will be evaluated against the first sub-expression. If it
/// succeeds, the successful result will be returned. If it fails, the input will be evaluated
/// against the second sub-expression. If that succeeds, the successful result will be returned.
/// If it also fails, the `or` expression will fail with a tuple of the two errors.
pub fn or<'a, V, E1, E2>(
    expr1: impl Fn(&'a str) -> Result<V, E1>,
    expr2: impl Fn(&'a str) -> Result<V, E2>,
) -> impl Fn(&'a str) -> Result<V, (Value<E1>, Value<E2>)> {
    move |input| {
        let error1 = match expr1(input) {
            Ok(value) => return Ok(value),
            Err(error) => error,
        };
        let error2 = match expr2(input) {
            Ok(value) => return Ok(value),
            Err(error) => error,
        };
        Err(Value::join(error1, error2))
    }
}

/// Transform a successful parse result.
///
/// When given an input, the input will be evaluated against the sub-expression. If it succeeds, the
/// given `mapper` function will be applied to the value to produce a new result.
pub fn map<'a, V, E, U>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    mapper: impl Fn(V) -> U,
) -> impl Fn(&'a str) -> Result<U, E> {
    move |input| {
        let value = expr(input)?;
        Ok(Value {
            span: value.span,
            value: mapper(value.value),
        })
    }
}

/// Transform a failed parse result.
///
/// When given an input, the input will be evaluated against the sub-expression. If it fails, the
/// given `mapper` function will be applied to the value to produce a new result.
pub fn map_err<'a, V, E, F>(
    expr: impl Fn(&'a str) -> Result<V, E>,
    mapper: impl Fn(E) -> F,
) -> impl Fn(&'a str) -> Result<V, F> {
    move |input| {
        let result = expr(input);
        result.map_err(|value| Value {
            span: value.span,
            value: mapper(value.value),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_calculator() {
        #[derive(Debug, PartialEq)]
        enum Expr {
            Num(i8),
            Add(Value<i8>, Value<i8>),
        }

        #[derive(Debug, PartialEq)]
        enum CalcError {
            InvalidNumber,
            InvalidOperator,
        }

        let num = map_err(or(map(chr('1'), |_| 1), map(chr('2'), |_| 2)), |_| {
            CalcError::InvalidNumber
        });
        let add = map(
            and(
                &num,
                and(map_err(chr('+'), |_| CalcError::InvalidOperator), &num),
            ),
            |(a, Value { value: (_, b), .. })| {
                let a_end = a.span.end;
                Expr::Add(a, b.offset(a_end))
            },
        );
        let sub = map(
            and(
                &num,
                and(map_err(chr('-'), |_| CalcError::InvalidOperator), &num),
            ),
            |(
                a,
                Value {
                    value: (_, mut b), ..
                },
            )| {
                let a_end = a.span.end;
                b.value = -b.value;
                Expr::Add(a, b.offset(a_end))
            },
        );
        let expr = or(&add, or(&sub, map(&num, Expr::Num)));

        assert_eq!(
            expr("1"),
            Ok(Value {
                span: 0..1,
                value: Expr::Num(1)
            })
        );
        assert_eq!(
            expr("2"),
            Ok(Value {
                span: 0..1,
                value: Expr::Num(2)
            })
        );
        assert_eq!(
            expr("1+2"),
            Ok(Value {
                span: 0..3,
                value: Expr::Add(
                    Value {
                        span: 0..1,
                        value: 1
                    },
                    Value {
                        span: 2..3,
                        value: 2
                    }
                )
            })
        );
        assert_eq!(
            expr("1-2"),
            Ok(Value {
                span: 0..3,
                value: Expr::Add(
                    Value {
                        span: 0..1,
                        value: 1
                    },
                    Value {
                        span: 2..3,
                        value: -2
                    }
                )
            })
        );
        assert_eq!(
            expr("wow"),
            Err(Value {
                span: 0..1,
                value: (
                    Value {
                        span: 0..1,
                        value: CalcError::InvalidNumber
                    },
                    Value {
                        span: 0..1,
                        value: (
                            Value {
                                span: 0..1,
                                value: CalcError::InvalidNumber
                            },
                            Value {
                                span: 0..1,
                                value: CalcError::InvalidNumber
                            }
                        )
                    }
                )
            })
        );
    }
}
