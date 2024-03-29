use super::*;

/// A shorthand trait for a collection of `LocalCell`s.
///
/// This trait cannot be implemented by users.
pub trait BorrowExt<'a>: private::Sealed {
    /// The output for borrowed references.
    type Output: 'a;

    /// Borrows a collection of `LocalCell`s.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::{LocalCell, cell::BorrowExt};
    ///
    /// let array = LocalCell::new([1, 2, 3, 4, 5]);
    /// let each_ref = array.as_array().each_ref();
    /// reentrant::with(|token| {
    ///     assert_eq!(each_ref.borrow(token), [&1, &2, &3, &4, &5]);
    /// })
    /// ```
    fn borrow(self, token: &'a Token) -> Self::Output;
}

impl<'a, T: ?Sized> private::Sealed for &'a LocalCell<T> {}
impl<'a, T: ?Sized> BorrowExt<'a> for &'a LocalCell<T> {
    type Output = &'a T;

    fn borrow(self, token: &'a Token) -> Self::Output {
        self.borrow(token)
    }
}

impl<'a, T> private::Sealed for &'a [LocalCell<T>] {}
impl<'a, T> BorrowExt<'a> for &'a [LocalCell<T>] {
    type Output = &'a [T];

    fn borrow(self, token: &'a Token) -> Self::Output {
        LocalCell::from_slice(self).borrow(token)
    }
}

impl<'a, T, const N: usize> private::Sealed for &'a [LocalCell<T>; N] {}
impl<'a, T, const N: usize> BorrowExt<'a> for &'a [LocalCell<T>; N] {
    type Output = &'a [T; N];

    fn borrow(self, token: &'a Token) -> Self::Output {
        LocalCell::from_array(self).borrow(token)
    }
}

impl<'a, T, const N: usize> private::Sealed for [&'a LocalCell<T>; N] {}
impl<'a, T, const N: usize> BorrowExt<'a> for [&'a LocalCell<T>; N] {
    type Output = [&'a T; N];

    fn borrow(self, token: &'a Token) -> Self::Output {
        self.map(|cell| cell.borrow(token))
    }
}