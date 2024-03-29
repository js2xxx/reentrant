//! The module for [`LocalCell`].

macro_rules! impl_tuples {
    ($macro:ident: ) => {};
    ($macro:ident: $head:ident $(,$tail:ident)* $(,)?) => {
        $macro!($head, $($tail,)*);
        impl_tuples!($macro: $($tail,)*);
    };
    ($macro:ident) => {
        impl_tuples!($macro: A, B, C, D, E, F, G, H, I, J, K, L);
    };
}

mod borrow;
mod borrow_mut;

use core::{cell::UnsafeCell, mem, ptr};

pub use self::{
    borrow::BorrowExt,
    borrow_mut::{AliasedError, BorrowMutExt},
};
use crate::Token;

/// A wrapper for a possibly non-reentrant data.
///
/// - Unique access to the cell allows unimpeded access to the wrapped value.
/// - Shared access to the cell requires access through the associated
///   [non-reentrant token](Token) which will enforce at compile-time the
///   aliasing XOR mutability safety property.
///
/// Unlike ghost cells, this wrapper is not `Sync`, since `Token`s from
/// different threads cannot be distinguished.
#[repr(transparent)]
pub struct LocalCell<T: ?Sized>(UnsafeCell<T>);

impl<T> LocalCell<T> {
    /// Wraps a possibly non-reentrant value into a `LocalCell`.
    pub const fn new(value: T) -> Self {
        LocalCell(UnsafeCell::new(value))
    }

    /// Unwrap the previouly wrapped value from the `LocalCell`.
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T: ?Sized> LocalCell<T> {
    /// Immutably borrows the non-reentrant data branded with the current
    /// non-reentrant token.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let my_data = LocalCell::new(String::from("A"));
    /// let another_data = LocalCell::new(Vec::new());
    ///
    /// reentrant::with_mut(|token| {
    ///     // Multiple mutable borrows can be taken out at the same time.
    ///     my_data.borrow_mut(token).push_str("Hello, world!");
    ///     another_data.borrow_mut(token).extend([1, 2, 3, 4, 5]);
    ///
    ///     println!("{} {:?}", my_data.borrow(token), another_data.borrow(token));
    /// });
    /// ```
    pub fn borrow<'a>(&'a self, _: &'a Token) -> &'a T {
        unsafe { &*self.0.get() }
    }

    /// Mutably borrows the non-reentrant data branded with the current
    /// non-reentrant token.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let my_data = LocalCell::new(String::from("A"));
    /// let another_data = LocalCell::new(Vec::new());
    ///
    /// reentrant::with_mut(|token| {
    ///     // Multiple mutable borrows can be taken out at the same time.
    ///     my_data.borrow_mut(token).push_str("Hello, world!");
    ///     another_data.borrow_mut(token).extend([1, 2, 3, 4, 5]);
    ///
    ///     println!("{} {:?}", my_data.borrow(token), another_data.borrow(token));
    /// });
    /// ```
    pub fn borrow_mut<'a>(&'a self, _: &'a mut Token) -> &'a mut T {
        unsafe { &mut *self.0.get() }
    }

    /// Obtains the pointer to the underlying wrapped value.
    pub fn as_ptr(&self) -> *mut T {
        self.0.get()
    }

    /// Get the mutable reference of the underlying wrapped value from a mutable
    /// reference of `LocalCell`.
    pub fn get_mut(&mut self) -> &mut T {
        self.0.get_mut()
    }

    /// Wraps a mutably borrowed value into a mutably borrowed `LocalCell`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut value = 42;
    ///
    /// let cell = LocalCell::from_mut(&mut value);
    /// let array = [&cell, &cell];
    ///
    /// let ret = reentrant::with_mut(|token| {
    ///     *array[0].borrow_mut(token) = 51;
    ///     *array[0].borrow(token)
    /// });
    ///
    /// assert_eq!(ret, 51);
    /// assert_eq!(value, 51);
    /// ```
    pub fn from_mut(value: &mut T) -> &mut Self {
        unsafe { &mut *(ptr::from_mut(value) as *mut Self) }
    }
}

impl<T> LocalCell<T> {
    /// Replaces the wrapped value with a new one, returning the old one.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut value = 42;
    ///
    /// let cell = LocalCell::from_mut(&mut value);
    /// let array = [&cell, &cell];
    ///
    /// let ret = reentrant::with_mut(|token| array[0].replace(51, token));
    ///
    /// assert_eq!(ret, 42);
    /// assert_eq!(value, 51);
    /// ```
    pub fn replace<'a>(&'a self, src: T, token: &'a mut Token) -> T {
        mem::replace(self.borrow_mut(token), src)
    }

    /// Takes the wrapped value out of the `LocalCell`, leaving it as
    /// `Default::default`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut value = 42;
    ///
    /// let cell = LocalCell::from_mut(&mut value);
    /// let array = [&cell, &cell];
    ///
    /// let ret = reentrant::with_mut(|token| array[0].take(token));
    ///
    /// assert_eq!(ret, 42);
    /// assert_eq!(value, 0);
    /// ```
    pub fn take<'a>(&'a self, token: &'a mut Token) -> T
    where
        T: Default,
    {
        mem::take(self.borrow_mut(token))
    }

    /// Gets the wrapped value, without moving it.
    ///
    /// This function is a shorthand for `*self.borrow(token)`.
    pub fn get<'a>(&'a self, token: &'a Token) -> T
    where
        T: Copy,
    {
        *self.borrow(token)
    }

    /// Sets the wrapped value.
    ///
    /// This function is a shorthand for `*self.borrow_mut(token) = src`.
    pub fn set<'a>(&'a self, src: T, token: &'a mut Token) {
        *self.borrow_mut(token) = src;
    }
}

impl<T> LocalCell<T> {
    /// Swaps the wrapped value with another `LocalCell`.
    ///
    /// # Panics
    ///
    /// Panics if the two `LocalCell`s are aliased.
    pub fn swap<'a>(&'a self, other: &'a Self, token: &'a mut Token) {
        let (a, b) = (self, other).borrow_mut(token);
        mem::swap(a, b);
    }

    /// Tries to swap the wrapped value with another `LocalCell`.
    ///
    /// # Errors
    ///
    /// Returns an error if the two `LocalCell`s are aliased.
    pub fn try_swap<'a>(
        &'a self,
        other: &'a Self,
        token: &'a mut Token,
    ) -> Result<(), AliasedError> {
        let (a, b) = (self, other).try_borrow_mut(token)?;
        mem::swap(a, b);
        Ok(())
    }

    /// Swaps the wrapped value with another `LocalCell`, without alias
    /// checking.
    ///
    /// # Safety
    ///
    /// Undefined behavior will occur if the two `LocalCell`s are aliased.
    pub unsafe fn swap_unchecked<'a>(&'a self, other: &'a Self, token: &'a mut Token) {
        // SAFETY: The two `LocalCells` are not aliased by contract.
        let (a, b) = unsafe { (self, other).borrow_mut_unchecked(token) };
        mem::swap(a, b);
    }
}

impl<T> LocalCell<T> {
    /// Transforms a `LocalCell` of a tuple into a tuple of `LocalCell`s by
    /// reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut data = (b'0', "123", 456);
    /// let cell = LocalCell::from_mut(&mut data);
    /// let slice = cell.as_tuple();
    ///
    /// let ret = reentrant::with_mut(|token| {
    ///     *slice.1.borrow_mut(token) = "789";
    ///     slice.0.replace(b'8', token)
    /// });
    /// assert_eq!(ret, b'0');
    /// assert_eq!(data, (b'8', "789", 456));
    /// ```
    pub fn as_tuple(&self) -> &<Self as TupleExt>::Tuple
    where
        Self: TupleExt,
    {
        TupleExt::as_tuple(self)
    }

    /// Transforms a `LocalCell` of a tuple into a tuple of `LocalCell`s.
    pub fn into_tuple(self) -> <Self as TupleExt>::Tuple
    where
        Self: TupleExt,
    {
        TupleExt::into_tuple(self)
    }

    /// Transforms a tuple of `LocalCell`s into a `LocalCell` of a tuple.
    ///
    /// Note that due to the lack of support for partial tuple binding patterns
    /// (`let (a, b @ ..) = tuple`), the split operation is not available for
    /// tuples.
    pub fn from_tuple(tuple: &<Self as TupleExt>::Tuple) -> &Self
    where
        Self: TupleExt,
    {
        TupleExt::from_tuple(tuple)
    }
}

impl<T> LocalCell<[T]> {
    /// Transforms a `LocalCell` of a slice into a slice of `LocalCell`s.
    ///
    /// # Example
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut data = [1, 2, 3];
    /// let cell = LocalCell::from_mut(&mut data[..]);
    /// let slice = cell.as_slice();
    ///
    /// let ret = reentrant::with_mut(|token| {
    ///     *slice[1].borrow_mut(token) = 0;
    ///     *slice[1].borrow(token)
    /// });
    /// assert_eq!(ret, 0);
    /// assert_eq!(data, [1, 0, 3]);
    /// ```
    pub fn as_slice(&self) -> &[LocalCell<T>] {
        unsafe { &*(self.as_ptr() as *const [LocalCell<T>]) }
    }

    /// Transforms a slice of `LocalCell`s into a `LocalCell` of a slice.
    ///
    /// # Example
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut data = [1, 2, 3];
    /// let cell = LocalCell::from_mut(&mut data[..]);
    /// let slice = cell.as_slice();
    /// let last_two = LocalCell::from_slice(&slice[1..]);
    ///
    /// reentrant::with_mut(|token| {
    ///     last_two.borrow_mut(token).copy_from_slice(&[4, 5]);
    /// });
    /// assert_eq!(data, [1, 4, 5]);
    /// ```
    pub fn from_slice(slice: &[LocalCell<T>]) -> &Self {
        unsafe { &*(ptr::from_ref(slice) as *const Self) }
    }
}

impl<T, const N: usize> LocalCell<[T; N]> {
    /// Transforms a `LocalCell` of an array into an array of `LocalCell`s by
    /// reference.
    ///
    /// # Example
    ///
    /// ```rust
    /// use reentrant::LocalCell;
    ///
    /// let mut data = [1, 2, 3];
    /// let cell = LocalCell::from_mut(&mut data);
    /// let array = cell.as_array();
    ///
    /// let ret = reentrant::with_mut(|token| {
    ///     *array[1].borrow_mut(token) = 0;
    ///     *array[1].borrow(token)
    /// });
    /// assert_eq!(ret, 0);
    /// assert_eq!(data, [1, 0, 3]);
    /// ```
    pub fn as_array(&self) -> &[LocalCell<T>; N] {
        unsafe { &*self.as_ptr().cast::<[LocalCell<T>; N]>() }
    }

    /// Transforms a `LocalCell` of an array into an array of `LocalCell`s.
    pub fn into_array(self) -> [LocalCell<T>; N] {
        self.into_inner().map(LocalCell::new)
    }

    /// Transforms a slice of `LocalCell`s into a `LocalCell` of a slice.
    ///
    /// # Example
    ///
    /// ```rust
    /// #![feature(split_array)]
    ///
    /// use reentrant::LocalCell;
    ///
    /// let mut data = [1, 2, 3];
    /// let cell = LocalCell::from_mut(&mut data);
    /// let array = cell.as_array();
    /// let first_two = LocalCell::from_array(array.split_array_ref::<2>().0);
    ///
    /// reentrant::with_mut(|token| {
    ///     *first_two.borrow_mut(token) = [4, 5];
    /// });
    /// assert_eq!(data, [4, 5, 3]);
    /// ```
    pub fn from_array(array: &[LocalCell<T>; N]) -> &Self {
        unsafe { &*(ptr::from_ref(array).cast::<Self>()) }
    }
}

#[doc(hidden)]
pub trait TupleExt {
    type Tuple;

    fn as_tuple(&self) -> &Self::Tuple;

    fn into_tuple(self) -> Self::Tuple;

    fn from_tuple(tuple: &Self::Tuple) -> &Self;
}

macro_rules! impl_tuples_ext {
    ($($t:ident,)*) => {
        impl<$($t,)*> TupleExt for LocalCell<($($t,)*)> {
            type Tuple = ($(LocalCell<$t>,)*);

            fn as_tuple(&self) -> &($(LocalCell<$t>,)*) {
                unsafe { &*(self.as_ptr().cast::<($(LocalCell<$t>,)*)>()) }
            }

            #[allow(non_snake_case)]
            fn into_tuple(self) -> Self::Tuple {
                let ($($t,)*) = self.into_inner();
                ($(LocalCell::new($t),)*)
            }

            fn from_tuple(tuple: &($(LocalCell<$t>,)*)) -> &Self {
                unsafe { &*(ptr::from_ref(tuple).cast::<Self>()) }
            }
        }
    };
}
impl_tuples!(impl_tuples_ext);

mod private {
    #[doc(hidden)]
    pub trait Sealed {}
}
