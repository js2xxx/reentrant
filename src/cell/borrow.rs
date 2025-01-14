use super::*;

/// A shorthand trait for immutably borrowing a collection of `LocalCell`s.
///
/// This trait cannot be implemented by users.
pub trait BorrowExt<'a>: private::Sealed {
    /// The output for borrowed references.
    type Output: 'a;

    /// Immutably borrows a collection of `LocalCell`s.
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

impl<T: ?Sized> private::Sealed for &LocalCell<T> {}
impl<'a, T: ?Sized> BorrowExt<'a> for &'a LocalCell<T> {
    type Output = &'a T;

    fn borrow(self, token: &'a Token) -> Self::Output {
        self.borrow(token)
    }
}

impl<T> private::Sealed for &[LocalCell<T>] {}
impl<'a, T> BorrowExt<'a> for &'a [LocalCell<T>] {
    type Output = &'a [T];

    fn borrow(self, token: &'a Token) -> Self::Output {
        LocalCell::from_slice(self).borrow(token)
    }
}

impl<T, const N: usize> private::Sealed for &[LocalCell<T>; N] {}
impl<'a, T, const N: usize> BorrowExt<'a> for &'a [LocalCell<T>; N] {
    type Output = &'a [T; N];

    fn borrow(self, token: &'a Token) -> Self::Output {
        LocalCell::from_array(self).borrow(token)
    }
}

impl<T: ?Sized, const N: usize> private::Sealed for [&LocalCell<T>; N] {}
impl<'a, T: ?Sized, const N: usize> BorrowExt<'a> for [&'a LocalCell<T>; N] {
    type Output = [&'a T; N];

    fn borrow(self, token: &'a Token) -> Self::Output {
        self.map(|cell| cell.borrow(token))
    }
}

macro_rules! impl_borrow {
    ($($t:ident,)*) => {
        impl<'a, $($t,)*> private::Sealed for &'a ($(LocalCell<$t>,)*) {}
        impl<'a, $($t,)*> BorrowExt<'a> for &'a ($(LocalCell<$t>,)*) {
            type Output = &'a ($($t,)*);

            fn borrow(self, token: &'a Token) -> Self::Output {
                LocalCell::from_tuple(self).borrow(token)
            }
        }

        impl<'a, $($t: ?Sized,)*> private::Sealed for ($(&'a LocalCell<$t>,)*) {}
        impl<'a, $($t: ?Sized,)*> BorrowExt<'a> for ($(&'a LocalCell<$t>,)*) {
            type Output = ($(&'a $t,)*);

            #[allow(non_snake_case)]
            fn borrow(self, token: &'a Token) -> Self::Output {
                let ($($t,)*) = self;
                ($($t.borrow(token),)*)
            }
        }
    };
}
impl_tuples!(impl_borrow);
