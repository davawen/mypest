//! From https://stackoverflow.com/questions/67852867/rust-calling-fmt-function-directly

use std::fmt::{Display, Debug, self};

pub struct CustomFormatWrapper<'a, 'b, F, T: CustomFormat<F> + ?Sized>(&'a T, &'b F);

impl<'a, 'b, F, T: CustomFormat<F>> Debug for CustomFormatWrapper<'a, 'b, F, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as CustomFormat<F>>::fmt(self.0, f, self.1)
    }
}

impl<'a, 'b, F, T: CustomFormat<F>> Display for CustomFormatWrapper<'a, 'b, F, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as CustomFormat<F>>::fmt(self.0, f, self.1)
    }
}

/// Objects for which alternate textual representations can be generated.
/// These are analogous to [`Display`] and [`Debug`], but have additional options.
pub trait CustomFormat<F> {
    /// Wrap this value so that when formatted with [`Debug`] or [`Display`] it uses
    /// the given custom format instead.
    fn my_fmt<'a, 'b>(&'a self, data: &'b F) -> CustomFormatWrapper<'a, 'b, F, Self> {
        CustomFormatWrapper(self, data)
    }

    /// Implement this to provide custom formatting for this type.
    fn fmt(&self, f: &mut fmt::Formatter<'_>, data: &F) -> fmt::Result;
}
