//! Parsing combinator based PEG expression library.
//!
//! The functions in this module, apart from [`parse`], are all
//! `impl Fn(..., &str) -> Result<(&str, &str), String>`. The first arguments, if any, configure
//! the matching behaviour, and the `&str` argument is the input to match against.
//!
//! If matches succeed, the function will return a tuple of the output from the match and the
//! remaining input after the match. If they fail, the function will return a `String` explaining
//! the error. There is a [`Result`] type alias provided for convenience.
//!
//! [`parse`] is special – it takes a matching function
//! (`impl Fn(&str) -> Result`), performs the match, and then checks that there's no remaining input
//! after the match.
//!
//! This is even less ergonomic than [`Expression`] for creating parsers, but it's significantly
//! more composable, e.g.;
//!
//! ```
//! use packrs::combinators::{self, any, choose, chr, parse, reject, seq, zero_or_more};
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
//! fn quoted(quote: impl Fn(&str) -> combinators::Result, input: &str) -> combinators::Result {
//!     seq(&quote, |i| seq(|i| string_inner(&quote, i), &quote, i), input)
//! }
//!
//! fn string_inner(quote: impl Fn(&str) -> combinators::Result, input: &str) -> combinators::Result {
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
//! [`Result`]: type.Result.html
//! [`Expression`]: ../expression/enum.Expression.html

/// Convenience alias for the result of combinators.
pub type Result<'a> = std::result::Result<(&'a str, &'a str), String>;

/// Always matches, regardless of the input (even if empty).
///
/// Outputs an empty string.
pub fn empty(input: &str) -> Result {
    Ok(("", input))
}

/// Matches any single character.
///
/// Outputs the matched character, as a string, as output.
///
/// Fails if the input is empty (with "unexpected end of input").
pub fn any(input: &str) -> Result {
    let mut chars = input.char_indices();
    let _ = chars
        .next()
        .ok_or_else(|| "unexpected end of input".to_string())?;
    chars
        .next()
        .map_or_else(|| Ok((input, "")), |(idx, _)| Ok(input.split_at(idx)))
}

/// Matches a specific character.
///
/// Outputs the matched character, as a string, as output.
///
/// Fails if the input does not start with the given character (with "expected '{expected}'").
/// Fails if the input is empty (with 'unexpected end of input').
pub fn chr(expected: char, input: &str) -> Result {
    let mut chars = input.char_indices();
    let (_, actual) = chars
        .next()
        .ok_or_else(|| "unexpected end of input".to_string())?;
    if actual == expected {
        chars
            .next()
            .map_or_else(|| Ok((input, "")), |(idx, _)| Ok(input.split_at(idx)))
    } else {
        Err(format!("expected '{}'", expected))
    }
}

/// Matches two given sub-expressions in sequence.
///
/// Outputs the concatenated outputs of the sub-expressions.
///
/// If either of the sub-expressions fail, the failure is propagated.
pub fn seq(expr1: impl Fn(&str) -> Result, expr2: impl Fn(&str) -> Result, input: &str) -> Result {
    let (output1, input2) = expr1(input)?;
    let (output2, _remainder) = expr2(input2)?;
    Ok(input.split_at(output1.len() + output2.len()))
}

/// Matches one of the given sub-expressions.
///
/// The sub-expressions are attempted in order – when one succeeds the result is returned.
///
/// If both of the sub-expressions fail, the failure messages are combined with " or ".
pub fn choose(
    expr1: impl Fn(&str) -> Result,
    expr2: impl Fn(&str) -> Result,
    input: &str,
) -> Result {
    expr1(input).or_else(|error1| expr2(input).or_else(|error2| Err(error1 + " or " + &error2)))
}

/// Matches the given sub-expression zero or more times.
///
/// Outputs the concatenated outputs from successful matches of the sub-expression.
///
/// This expression never fails.
pub fn zero_or_more(expr: impl Fn(&str) -> Result, input: &str) -> Result {
    let mut remaining = input;
    while let Ok((_, remaining_)) = expr(remaining) {
        remaining = remaining_;
    }
    Ok(input.split_at(input.len() - remaining.len()))
}

/// Matches the given sub-expression one or more times.
///
/// Outputs the concatenated outputs from successful matches of the sub-expression.
///
/// If the sub-expression fails the first match, the failure is propagated.
pub fn one_or_more(expr: impl Fn(&str) -> Result, input: &str) -> Result {
    let (_, mut remaining) = expr(input)?;
    while let Ok((_, remaining_)) = expr(remaining) {
        remaining = remaining_;
    }
    Ok(input.split_at(input.len() - remaining.len()))
}

/// Matches the given sub-expression once, without propagating failure.
///
/// Outputs the result of the sub-expression on a successful match, or an empty string otherwise.
///
/// This expression never fails.
pub fn optional(expr: impl Fn(&str) -> Result, input: &str) -> Result {
    expr(input).or_else(|_| Ok(("", input)))
}

/// Matches the given sub-expression without consuming input.
///
/// Outputs the empty string.
///
/// If the sub-expression fails, the failure is propagated.
pub fn check(expr: impl Fn(&str) -> Result, input: &str) -> Result {
    expr(input)?;
    Ok(("", input))
}

/// Matches the given sub-expression without consuming input and inverts the result.
///
/// Outputs an empty string if the sub-expression fails.
///
/// Fail with "unexpected input" if the sub-expression matches.
pub fn reject(expr: impl Fn(&str) -> Result, input: &str) -> Result {
    expr(input).map_or_else(|_| Ok(("", input)), |_| Err("unexpected input".to_string()))
}

/// Matches the given sub-expression and checks there's no input left.
///
/// Returns the sub-expression output if it succeeds.
///
/// Fails with the sub-expression failure, or with "expected end of input" if there is input left after running sub-expression.
pub fn parse(expr: impl Fn(&str) -> Result, input: &str) -> std::result::Result<&str, String> {
    let (output, remainder) = expr(input)?;
    if remainder.is_empty() {
        Ok(output)
    } else {
        Err("expected end of input".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type Result = std::result::Result<(), String>;

    #[test]
    fn empty_ok_when_input_is_empty() -> Result {
        assert_eq!(empty("")?, ("", ""));
        Ok(())
    }

    #[test]
    fn empty_ok_when_input_is_nonempty() -> Result {
        assert_eq!(empty("hello")?, ("", "hello"));
        Ok(())
    }

    #[test]
    fn any_err_when_input_is_empty() {
        assert_eq!(any(""), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn any_ok_when_input_is_nonempty() -> Result {
        assert_eq!(any("hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn any_ok_when_input_contains_multibyte_char() -> Result {
        let input1 = "y̆";
        let (output1, input2) = any(input1)?;
        let (output2, remainder) = any(input2)?;

        assert_eq!(output1, "y");
        assert_eq!(input2, "\u{306}");
        assert_eq!(output2, "\u{306}");
        assert_eq!(remainder, "");
        assert_eq!(output1.to_string() + output2, "y̆");

        Ok(())
    }

    #[test]
    fn chr_err_when_input_is_empty() {
        assert_eq!(chr('a', ""), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn chr_err_when_input_does_not_match() {
        assert_eq!(chr('a', "hello"), Err("expected 'a'".to_string()));
    }

    #[test]
    fn chr_ok_when_input_matches() -> Result {
        assert_eq!(chr('h', "hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn chr_ok_when_multibyte_input_matches() -> Result {
        assert_eq!(chr('y', "y̆")?, ("y", "\u{306}"));
        assert_eq!(chr('\u{306}', "\u{306}")?, ("\u{306}", ""));
        Ok(())
    }

    #[test]
    fn seq_err_when_first_expr_err() {
        assert_eq!(
            seq(any, empty, ""),
            Err("unexpected end of input".to_string())
        );
    }

    #[test]
    fn seq_err_when_second_expr_err() {
        assert_eq!(
            seq(empty, any, ""),
            Err("unexpected end of input".to_string())
        );
    }

    #[test]
    fn seq_ok_when_both_expr_ok() -> Result {
        assert_eq!(
            seq(|i| chr('y', i), |i| chr('\u{306}', i), "y̆o")?,
            ("y̆", "o")
        );
        Ok(())
    }

    #[test]
    fn choose_err_when_both_expr_err() {
        assert_eq!(
            choose(any, any, ""),
            Err("unexpected end of input or unexpected end of input".to_string())
        );
    }

    #[test]
    fn choose_ok_when_first_expr_ok() -> Result {
        assert_eq!(choose(any, |i| chr('a', i), "hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn choose_ok_when_second_expr_ok() -> Result {
        assert_eq!(choose(|i| chr('a', i), any, "hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn zero_or_more_ok_when_no_match() -> Result {
        assert_eq!(zero_or_more(any, "")?, ("", ""));
        Ok(())
    }

    #[test]
    fn zero_or_more_ok_when_one_match() -> Result {
        assert_eq!(zero_or_more(|i| chr('h', i), "hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn zero_or_more_ok_when_multi_match() -> Result {
        assert_eq!(
            zero_or_more(|i| seq(|i| chr('y', i), |i| chr('\u{306}', i), i), "y̆o")?,
            ("y̆", "o")
        );
        Ok(())
    }

    #[test]
    fn zero_or_more_ok_when_all_match() -> Result {
        assert_eq!(zero_or_more(any, "hello")?, ("hello", ""));
        Ok(())
    }

    #[test]
    fn one_or_more_err_when_no_match() {
        assert_eq!(
            one_or_more(any, ""),
            Err("unexpected end of input".to_string())
        );
    }

    #[test]
    fn one_or_more_ok_when_one_match() -> Result {
        assert_eq!(one_or_more(|i| chr('h', i), "hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn one_or_more_ok_when_multi_match() -> Result {
        assert_eq!(
            one_or_more(|i| seq(|i| chr('y', i), |i| chr('\u{306}', i), i), "y̆o")?,
            ("y̆", "o")
        );
        Ok(())
    }

    #[test]
    fn one_or_more_ok_when_all_match() -> Result {
        assert_eq!(one_or_more(any, "hello")?, ("hello", ""));
        Ok(())
    }

    #[test]
    fn optional_ok_when_no_match() -> Result {
        assert_eq!(optional(any, "")?, ("", ""));
        Ok(())
    }

    #[test]
    fn optional_ok_when_match() -> Result {
        assert_eq!(optional(any, "hello")?, ("h", "ello"));
        Ok(())
    }

    #[test]
    fn check_err_when_no_match() {
        assert_eq!(check(any, ""), Err("unexpected end of input".to_string()));
    }

    #[test]
    fn check_ok_when_match() -> Result {
        assert_eq!(check(any, "hello")?, ("", "hello"));
        Ok(())
    }

    #[test]
    fn reject_err_when_match() {
        assert_eq!(reject(any, "hello"), Err("unexpected input".to_string()));
    }

    #[test]
    fn reject_ok_when_no_match() -> Result {
        assert_eq!(reject(|i| chr('a', i), "hello")?, ("", "hello"));
        Ok(())
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
    fn parse_ok_when_match_and_no_remainder() -> Result {
        assert_eq!(parse(any, "h")?, "h");
        Ok(())
    }

    #[test]
    fn parse_quoted_strings() {
        // String:
        //   '\'' ( ( '\\' / !'\'' ) . )* '\''
        // / '"'  ( ( '\\' / !'"'  ) . )* '"'

        fn inner(quote: impl Fn(&str) -> super::Result, input: &str) -> super::Result {
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

        fn quoted(quote: impl Fn(&str) -> super::Result, input: &str) -> super::Result {
            seq(&quote, |i| seq(|i| inner(&quote, i), &quote, i), input)
        }

        fn string(input: &str) -> std::result::Result<&str, String> {
            fn sq(input: &str) -> super::Result {
                chr('\'', input)
            }
            fn dq(input: &str) -> super::Result {
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
