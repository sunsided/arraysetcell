//! Error types.

use std::any::Any;
use std::error::Error;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

/// Error value indicating insufficient capacity
#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
pub struct CapacityError<T = ()> {
    element: T,
}

impl<T> CapacityError<T> {
    /// Create a new `CapacityError` from `element`.
    pub const fn new(element: T) -> CapacityError<T> {
        CapacityError { element }
    }

    /// Extract the overflowing element
    pub fn element(self) -> T {
        self.element
    }

    /// Convert into a `CapacityError` that does not carry an element.
    pub fn simplify(self) -> CapacityError {
        CapacityError { element: () }
    }
}

impl<T: Any> Error for CapacityError<T> {}

impl<T> Display for CapacityError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", "insufficient capacity")
    }
}

impl<T> Debug for CapacityError<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}: {}", "CapacityError", "insufficient capacity")
    }
}
