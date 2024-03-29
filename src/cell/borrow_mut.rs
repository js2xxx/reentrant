use super::*;

/// A shorthand trait for mutably borrowing a collection of `LocalCell`s.
///
/// This trait cannot be implemented by users.
///
/// This trait is similar to [`BorrowExt`] but have additional performance costs
/// on arrays/tuples of references of local cells (`[&LocalCell<T>; N]` or
/// `(&LocalCell<T>, ..)`) because of aliasing checks.
///
/// # Zero-sized types
///
/// Due to the inability of aliasing checks on different instances of ZSTs,
/// whose pointer addresses are all the same dangling yet well-aligned value,
/// all ZSTs are treated as they are different instances. Hence, arrays/tuples
/// which contain more than 1 ZST fail on the aliasing checks.
pub trait BorrowMutExt<'a>: private::Sealed + Sized {
    /// The output for borrowed references.
    type Output: 'a;

    /// Mutably borrows a collection of `LocalCell`s.
    ///
    /// # Panics
    ///
    /// This function panics if some local cells in the collection are partially
    /// aliased.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::{LocalCell, cell::BorrowMutExt};
    ///
    /// let array = LocalCell::new([1, 2, 3, 4, 5]);
    /// let each_ref = array.as_array().each_ref();
    /// reentrant::with_mut(|token| {
    ///     assert_eq!(
    ///         each_ref.borrow_mut(token),
    ///         [&mut 1, &mut 2, &mut 3, &mut 4, &mut 5]
    ///     );
    /// });
    /// ```
    ///
    /// ```rust,should_panic
    /// use reentrant::{LocalCell, cell::BorrowMutExt};
    ///
    /// let cell = LocalCell::new(1);
    /// let aliased_refs = [&cell, &cell, &cell];
    /// reentrant::with_mut(|token| {
    ///     let _ = aliased_refs.borrow_mut(token);
    /// });
    /// ```
    fn borrow_mut(self, token: &'a mut Token) -> Self::Output {
        self.try_borrow_mut(token)
            .expect("some local cells in the collection are partially aliased")
    }

    /// Tries to mutably borrow a collection of `LocalCell`s.
    ///
    /// # Errors
    ///
    /// This function returns en error if some local cells in the collection are
    /// partially aliased.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::{LocalCell, cell::BorrowMutExt};
    ///
    /// let array = LocalCell::new([1, 2, 3, 4, 5]);
    /// let each_ref = array.as_array().each_ref();
    /// reentrant::with_mut(|token| {
    ///     assert_eq!(
    ///         each_ref.try_borrow_mut(token).unwrap(),
    ///         [&mut 1, &mut 2, &mut 3, &mut 4, &mut 5]
    ///     );
    /// });
    ///
    /// let cell = LocalCell::new(1);
    /// let aliased_refs = [&cell, &cell, &cell];
    /// reentrant::with_mut(|token| {
    ///     assert!(aliased_refs.try_borrow_mut(token).is_err());
    /// });
    /// ```
    fn try_borrow_mut(self, token: &'a mut Token) -> Result<Self::Output, AliasedError> {
        Ok(self.borrow_mut(token))
    }

    /// Mutably borrows a collection of `LocalCell`s without aliasing checks.
    ///
    /// # Safety
    ///
    /// Undefined behavior will occur if some local cells in the collection are
    /// partially aliased.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::{LocalCell, cell::BorrowMutExt};
    ///
    /// let array = LocalCell::new([1, 2, 3, 4, 5]);
    /// let each_ref = array.as_array().each_ref();
    /// reentrant::with_mut(|token| unsafe {
    ///     assert_eq!(
    ///         each_ref.borrow_mut_unchecked(token),
    ///         [&mut 1, &mut 2, &mut 3, &mut 4, &mut 5]
    ///     );
    /// });
    ///
    /// let cell = LocalCell::new(1);
    /// let aliased_refs = [&cell, &cell, &cell];
    /// reentrant::with_mut(|token| unsafe {
    ///     // Undefined behavior!!!
    ///     // let _ = aliased_refs.borrow_mut_unchecked(token);
    /// });
    /// ```
    unsafe fn borrow_mut_unchecked(self, token: &'a mut Token) -> Self::Output {
        self.borrow_mut(token)
    }
}

/// An error returned by [`try_borrow_mut`](BorrowMutExt::try_borrow_mut).
#[derive(Debug)]
#[non_exhaustive]
pub struct AliasedError {}

impl<'a, T: ?Sized> BorrowMutExt<'a> for &'a LocalCell<T> {
    type Output = &'a mut T;

    fn borrow_mut(self, token: &'a mut Token) -> Self::Output {
        (*self).borrow_mut(token)
    }
}

impl<'a, T> BorrowMutExt<'a> for &'a [LocalCell<T>] {
    type Output = &'a mut [T];

    fn borrow_mut(self, token: &'a mut Token) -> Self::Output {
        LocalCell::from_slice(self).borrow_mut(token)
    }
}

impl<'a, T, const N: usize> BorrowMutExt<'a> for &'a [LocalCell<T>; N] {
    type Output = &'a mut [T; N];

    fn borrow_mut(self, token: &'a mut Token) -> Self::Output {
        LocalCell::from_array(self).borrow_mut(token)
    }
}

impl<'a, T, const N: usize> BorrowMutExt<'a> for [&'a LocalCell<T>; N] {
    type Output = [&'a mut T; N];

    fn try_borrow_mut(self, token: &'a mut Token) -> Result<Self::Output, AliasedError> {
        check_aliasing(self.map(Span::of))?;
        // SAFETY: All the local cells in the array are not aliased.
        Ok(unsafe { self.borrow_mut_unchecked(token) })
    }

    unsafe fn borrow_mut_unchecked(self, _: &'a mut Token) -> Self::Output {
        // SAFETY: All the local cells in the array are not aliased.
        unsafe { mem::transmute_copy(&self) }
    }
}

macro_rules! impl_borrow_mut {
    ($($t:ident,)*) => {
        impl<'a, $($t,)*> BorrowMutExt<'a> for &'a ($(LocalCell<$t>,)*) {
            type Output = &'a mut ($($t,)*);

            fn borrow_mut(self, token: &'a mut Token) -> Self::Output {
                LocalCell::from_tuple(self).borrow_mut(token)
            }
        }

        impl<'a, $($t,)*> BorrowMutExt<'a> for ($(&'a LocalCell<$t>,)*) {
            type Output = ($(&'a mut $t,)*);

            #[allow(non_snake_case)]
            fn try_borrow_mut(self, token: &'a mut Token) -> Result<Self::Output, AliasedError> {
                let ($($t,)*) = self;
                check_aliasing([$(Span::of($t),)*])?;
                // SAFETY: All the local cells in the tuple are not aliased.
                Ok(unsafe { self.borrow_mut_unchecked(token) })
            }

            unsafe fn borrow_mut_unchecked(self, _: &'a mut Token) -> Self::Output {
                // SAFETY: All the local cells in the tuple are not aliased.
                unsafe { mem::transmute_copy(&self) }
            }
        }
    };
}
impl_tuples!(impl_borrow_mut);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Span {
    start: usize,
    end: usize,
}

impl Span {
    fn of<T: ?Sized>(cell: &LocalCell<T>) -> Self {
        let start = cell.as_ptr().addr();
        Span {
            start,
            end: start + mem::size_of_val(cell).min(1),
        }
    }
}

fn check_aliasing<const N: usize>(mut spans: [Span; N]) -> Result<(), AliasedError> {
    if N > 1 {
        spans.sort_unstable();
        if spans.array_windows::<2>().any(|[a, b]| a.end >= b.start) {
            return Err(AliasedError {});
        }
    }
    Ok(())
}
