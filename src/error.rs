//! Structs returned by parsers on failure.

/// A struct representing a failure due to a missing expected character.
///
/// This is returned by [`chr`](crate::chr) on parse failures.
#[derive(Debug, PartialEq)]
pub struct ExpectedChar(
    /// The character that was expected.
    pub char,
);

/// A struct representing a failure due to finding input when end of input was expected.
///
/// This is returned by [`end_of_input`](crate::end_of_input) on parse failures.
#[derive(Debug, PartialEq)]
pub struct ExpectedEndOfInput;

/// A struct representing a failure due to a missing expected character.
///
/// This is returned by [`string`](crate::string) on parse failures.
#[derive(Debug, PartialEq)]
pub struct ExpectedString<'s>(
    /// The character that was expected.
    pub &'s str,
);

/// A struct representing a failure due to unexpected end of input.
///
/// This is returned by [`any`](crate::any) on parse failures.
#[derive(Debug, PartialEq)]
pub struct UnexpectedEndOfInput;
