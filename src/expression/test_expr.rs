use core::cell::Cell;
use core::ops::Range;
use quickcheck::{Arbitrary, Gen};

use crate::parser::Parser;
use crate::span::Span;

pub use TestExpr::*;

#[derive(Clone, Debug, PartialEq)]
pub struct TestValue;

#[derive(Clone, Debug, PartialEq)]
pub struct TestError;

#[derive(Clone, Debug)]
pub struct TestConfig {
    start: usize,
    end: usize,
    calls: Cell<usize>,
}

impl TestConfig {
    fn new(range: Range<usize>) -> Self {
        TestConfig {
            start: range.start,
            end: range.end,
            calls: Cell::new(0),
        }
    }

    pub fn range(&self) -> Range<usize> {
        self.start..self.end
    }

    pub fn calls(&self) -> usize {
        self.calls.get()
    }
}

impl Arbitrary for TestConfig {
    fn arbitrary<G: Gen>(g: &mut G) -> Self {
        TestConfig::new(Range::arbitrary(g))
    }
}

#[derive(Clone, Debug)]
pub enum TestExpr {
    ParseMatch(TestConfig, u8),
    ParseError(TestConfig),
}

impl TestExpr {
    pub fn ok(range: Range<usize>) -> Self {
        ParseMatch(TestConfig::new(range), 0)
    }

    pub fn ok_iters(range: Range<usize>, max_calls: u8) -> Self {
        ParseMatch(TestConfig::new(range), max_calls)
    }

    pub fn err(range: Range<usize>) -> Self {
        ParseError(TestConfig::new(range))
    }

    pub fn is_ok(&self) -> bool {
        match self {
            ParseMatch(_, _) => true,
            ParseError(_) => false,
        }
    }

    pub fn config(&self) -> &TestConfig {
        match self {
            ParseMatch(config, _) => config,
            ParseError(config) => config,
        }
    }
}

impl Parser for TestExpr {
    type Value = TestValue;
    type Error = TestError;

    fn parse<'i>(&self, _input: &'i str) -> Result<Span<Self::Value>, Span<Self::Error>> {
        self.config().calls.set(self.config().calls() + 1);
        match self {
            ParseMatch(config, max_calls) => {
                if *max_calls == 0 || config.calls() <= *max_calls as usize {
                    Ok(Span::new(config.range(), TestValue))
                } else {
                    Err(Span::new(0..0, TestError))
                }
            }
            ParseError(config) => Err(Span::new(config.range(), TestError)),
        }
    }
}

impl Arbitrary for TestExpr {
    fn arbitrary<G: Gen>(g: &mut G) -> TestExpr {
        if bool::arbitrary(g) {
            ParseMatch(TestConfig::arbitrary(g), 0)
        } else {
            ParseError(TestConfig::arbitrary(g))
        }
    }
}

mod tests {
    use quickcheck_macros::quickcheck;

    use super::*;
    use crate::span::Span;

    #[test]
    fn test_match() {
        assert_eq!(
            TestExpr::ok(16..43).parse("arbitrary"),
            Ok(Span::new(16..43, TestValue))
        );
    }

    #[test]
    fn test_match_limit() {
        let expr = TestExpr::ok_iters(32..53, u8::max_value() - 2);
        while let Ok(_) = expr.parse("arbitrary") {}

        assert_eq!(expr.config().calls(), u8::max_value() as usize - 1);
        assert_eq!(expr.parse("arbitrary"), Err(Span::new(0..0, TestError)));
    }

    #[test]
    fn test_error() {
        assert_eq!(
            TestExpr::err(12..31).parse("arbitrary"),
            Err(Span::new(12..31, TestError))
        );
    }

    #[quickcheck]
    fn parse(expr: TestExpr, input: String) {
        let result = expr.parse(&input);
        assert_eq!(
            result,
            match expr {
                ParseMatch(config, _) => Ok(Span::new(config.range(), TestValue)),
                ParseError(config) => Err(Span::new(config.range(), TestError)),
            }
        );
    }

    #[quickcheck]
    fn parse_iters(range: Range<usize>, iters: u8, input: String) {
        let expr = TestExpr::ok_iters(range, iters);
        for _ in 0..iters {
            assert_eq!(
                expr.parse(&input),
                Ok(Span::new(expr.config().range(), TestValue))
            );
        }
        assert_eq!(expr.config().calls(), iters as usize);
        assert_eq!(
            expr.parse(&input),
            if iters == 0 {
                Ok(Span::new(expr.config().range(), TestValue))
            } else {
                Err(Span::new(0..0, TestError))
            }
        );
    }

    #[quickcheck]
    fn is_ok(expr: TestExpr) {
        assert_eq!(
            expr.is_ok(),
            match expr {
                ParseMatch(_, _) => true,
                ParseError(_) => false,
            }
        );
    }
}
