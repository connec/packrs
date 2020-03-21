use core::ops::{Bound, RangeBounds};

/// Represents a `value` at a given `span` of an input.
#[derive(Clone, Debug, PartialEq)]
pub struct Span<T> {
    start: usize,
    end: usize,
    value: T,
}

impl<T> Span<T> {
    /// Construct a new `Span` from a range and a value.
    pub fn new<R: RangeBounds<usize>>(range: R, value: T) -> Self {
        Span {
            start: match range.start_bound() {
                Bound::Included(n) => *n,
                Bound::Excluded(n) => *n + 1,
                _ => panic!("Span cannot be constructed with unbounded ranges"),
            },
            end: match range.end_bound() {
                Bound::Included(n) => *n + 1,
                Bound::Excluded(n) => *n,
                _ => panic!("Span cannot be constructed with unbounded ranges"),
            },
            value,
        }
    }

    /// Get the (inclusive) start index of the span.
    pub fn start(&self) -> usize {
        self.start
    }

    /// Get the (exclusive) end index of the span.
    pub fn end(&self) -> usize {
        self.end
    }

    /// Retrieve the value from the span, discarding the range information.
    pub fn take(self) -> T {
        self.value
    }

    /// Transform the value in a span using the given function.
    pub fn map<U>(self, f: impl FnOnce(T) -> U) -> Span<U> {
        Span {
            start: self.start,
            end: self.end,
            value: f(self.value),
        }
    }

    /// Offset the range of the span relative to the given end index.
    ///
    /// This just adds `end` to the span's range `start` and `end`.
    pub fn relative_to(mut self, end: usize) -> Self {
        self.start += end;
        self.end += end;
        self
    }
}

#[cfg(test)]
mod tests {
    use super::Span;

    #[derive(Debug, PartialEq)]
    struct Value;

    #[test]
    fn test_start() {
        let span = Span::new(0..1, Value);
        assert_eq!(span.start(), 0);
    }

    #[test]
    fn test_end() {
        let span = Span::new(0..1, Value);
        assert_eq!(span.end(), 1);
    }

    #[test]
    fn test_take() {
        let span = Span::new(0..1, Value);
        assert_eq!(span.take(), Value);
    }

    #[test]
    fn test_map() {
        let span = Span::new(0..1, Value);
        assert_eq!(span.map(|_| 2), Span::new(0..1, 2));
    }

    #[test]
    fn test_relative_to() {
        let span = Span::new(0..10, ());
        assert_eq!(span.relative_to(5), Span::new(5..15, ()));
    }
}
