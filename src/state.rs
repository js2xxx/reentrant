//! The module for managing the reentrancy state & non-reentrant tokens of the
//! current execution unit.
//!
//! See [the crate-level documentation](crate) for more information.

#[cfg(feature = "debug")]
use core::panic::Location;
use core::{
    cell::Cell,
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    sync::atomic::{self, Ordering::*},
};

use crate::Global;

/// A data structure which controls the reentrancy of the current execution
/// unit.
///
/// # Safety
///
/// The implementation of this trait must ensure that the reentrancy state is
/// not corrupted.
pub unsafe trait Reentrancy {
    /// Enables reentrancy for the current execution unit.
    ///
    /// # Safety
    ///
    /// The caller must ensure that no data which requires the reentrancy to be
    /// disabled are live in the current scope.
    unsafe fn enable(&self);

    /// Disables reentrancy for the current execution unit.
    fn disable(&self);

    /// Returns whether the current execution unit is reentrant.
    fn is_reentrant(&self) -> bool;
}

/// A token indicating that the current execution unit is not reentrant.
pub struct Token(PhantomData<*mut ()>);

/// The state of the current borrowing of [non-reentrant token](Token)s.
#[derive(Debug, Clone, Copy)]
pub enum BorrowState {
    /// The current token is borrowed immutably, from which only shared
    /// references of values from [`LocalCell`](crate::LocalCell)s can be
    /// created.
    BorrowedRef {
        /// The number of immutable borrows.
        num_borrows: usize,
    },
    /// The current token is borrowed mutably, from which both shared &
    /// exclusive references of values from [`LocalCell`](crate::LocalCell)s can
    /// be created.
    BorrowedMut,
    /// The current token is not borrowed, which indicates that the current
    /// execution unit is reentrant.
    NotBorrowed,
}

/// A [`RefCell`](core::cell::RefCell)-like structure which provides borrowing
/// to the [non-reentrant token](Token)s.
pub struct State<T: Reentrancy + ?Sized = Global> {
    inner: Cell<isize>,
    #[cfg(feature = "debug")]
    last_location: Cell<Option<&'static Location<'static>>>,
    marker: PhantomData<*mut ()>,
    controller: T,
}

impl<T: Reentrancy> fmt::Debug for State<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("State")
            .field("state", &self.borrow_state())
            .finish()
    }
}

impl<T: Reentrancy> State<T> {
    /// Creates a new [`State<T>`].
    ///
    /// # Safety
    ///
    /// This structure must be unique per execution unit.
    pub const unsafe fn new(controller: T) -> Self {
        State {
            inner: Cell::new(0),
            #[cfg(feature = "debug")]
            last_location: Cell::new(None),
            controller,
            marker: PhantomData,
        }
    }
}

impl<T: Reentrancy + ?Sized> State<T> {
    /// Immutably borrows the non-reentrant token of the current execution unit,
    /// returning an error if the token is currently mutably borrowed.
    ///
    /// The borrow lasts until the returned `TokenRef` exits scope. Multiple
    /// immutable borrows can be taken out at the same time.
    ///
    /// This is the non-panicking variant of [`borrow`](Self::borrow), which
    /// shares the same sematics as [the one in
    /// `RefCell`](core::cell::RefCell::try_borrow).
    #[track_caller]
    pub fn try_borrow(&self) -> Result<TokenRef<'_, T>, BorrowError> {
        self.controller.disable();
        let state = self.inner.get();
        if state >= 0 {
            self.inner.set(state + 1);
            #[cfg(feature = "debug")]
            if state == 0 {
                self.last_location.set(Some(Location::caller()));
            }
            atomic::compiler_fence(Acquire);
            Ok(TokenRef { state: self })
        } else {
            Err(BorrowError {
                #[cfg(feature = "debug")]
                location: self.last_location.get().unwrap(),
            })
        }
    }

    /// Mutably borrows the non-reentrant token of the current execution unit,
    /// returning an error if the token is currently borrowed.
    ///
    /// The borrow lasts until the returned `TokenMut` exits scope. Multiple
    /// immutable borrows can be taken out at the same time.
    ///
    /// This is the non-panicking variant of [`borrow_mut`](Self::borrow_mut),
    /// which shares the same sematics as [the one in
    /// `RefCell`](core::cell::RefCell::try_borrow_mut).
    #[track_caller]
    pub fn try_borrow_mut(&self) -> Result<TokenMut<'_, T>, BorrowMutError> {
        self.controller.disable();
        let state = self.inner.get();
        if state == 0 {
            self.inner.set(-1);
            #[cfg(feature = "debug")]
            self.last_location.set(Some(Location::caller()));

            atomic::compiler_fence(Acquire);
            Ok(TokenMut {
                state: self,
                token: Token(PhantomData),
            })
        } else {
            Err(BorrowMutError {
                #[cfg(feature = "debug")]
                location: self.last_location.get().unwrap(),
            })
        }
    }

    /// Immutably borrows the non-reentrant token of the current execution unit.
    ///
    /// The borrow lasts until the returned `TokenRef` exits scope. Multiple
    /// immutable borrows can be taken out at the same time.
    ///
    /// This method shares the same semantics as [the one in
    /// `RefCell`](core::cell::RefCell::borrow).
    ///
    /// # Panics
    ///
    /// Panics if the value is currently mutably borrowed. For a non-panicking
    /// variant, use [`try_borrow`](Self::try_borrow).
    #[track_caller]
    pub fn borrow(&self) -> TokenRef<'_, T> {
        self.try_borrow()
            .unwrap_or_else(|err| panic!("already mutably borrowed: {err:?}"))
    }

    /// Mutably borrows the non-reentrant token of the current execution unit.
    ///
    /// The borrow lasts until the returned `TokenMut` exits scope. Only one
    /// mutable borrow can be taken out at the same time.
    ///
    /// This method shares the same semantics as [the one in
    /// `RefCell`](core::cell::RefCell::borrow_mut).
    ///
    /// # Panics
    ///
    /// Panics if the value is currently borrowed. For a non-panicking variant,
    /// use [`try_borrow_mut`](Self::try_borrow_mut).
    #[track_caller]
    pub fn borrow_mut(&self) -> TokenMut<'_, T> {
        self.try_borrow_mut()
            .unwrap_or_else(|err| panic!("already borrowed: {err:?}"))
    }
}

/// An error returned by [`try_borrow`](State::try_borrow).
#[non_exhaustive]
pub struct BorrowError {
    #[cfg(feature = "debug")]
    location: &'static Location<'static>,
}

impl fmt::Debug for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("BorrowError");
        #[cfg(feature = "debug")]
        d.field("location", &self.location);
        d.finish()
    }
}

impl fmt::Display for BorrowError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("already mutably borrowed")
    }
}

/// An error returned by [`try_borrow_mut`](State::try_borrow_mut).
#[non_exhaustive]
pub struct BorrowMutError {
    #[cfg(feature = "debug")]
    location: &'static Location<'static>,
}

impl fmt::Debug for BorrowMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut d = f.debug_struct("BorrowMutError");
        #[cfg(feature = "debug")]
        d.field("location", &self.location);
        d.finish()
    }
}

impl fmt::Display for BorrowMutError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("already borrowed")
    }
}

impl<T: Reentrancy + ?Sized> State<T> {
    /// Returns the inner reentracy controller of this structure.
    pub fn controller(&self) -> &T {
        &self.controller
    }

    /// Checks if the current execution unit is reentrant.
    pub fn is_reentrant(&self) -> bool {
        self.controller.is_reentrant()
    }

    /// Returns the current borrow state of the non-reentrant token.
    pub fn borrow_state(&self) -> BorrowState {
        match self.inner.get() {
            0 => BorrowState::NotBorrowed,
            -1 => {
                assert!(!self.controller.is_reentrant());
                BorrowState::BorrowedMut
            }
            x if x > 0 => {
                assert!(!self.controller.is_reentrant());
                BorrowState::BorrowedRef {
                    num_borrows: x as usize,
                }
            }
            _ => unreachable!(),
        }
    }
}

/// A guard to a immutable reference of the current non-reentrant token.
///
/// See [`borrow`](State::borrow) for more information.
pub struct TokenRef<'a, T: Reentrancy + ?Sized = Global> {
    state: &'a State<T>,
}

/// A guard to a mutable reference of the current non-reentrant token.
///
/// See [`borrow_mut`](State::borrow_mut) for more information.
pub struct TokenMut<'a, T: Reentrancy + ?Sized = Global> {
    state: &'a State<T>,
    token: Token,
}

impl<T: Reentrancy> Deref for TokenRef<'_, T> {
    type Target = Token;

    fn deref(&self) -> &Self::Target {
        &Token(PhantomData)
    }
}

impl<T: Reentrancy> Deref for TokenMut<'_, T> {
    type Target = Token;

    fn deref(&self) -> &Self::Target {
        &Token(PhantomData)
    }
}

impl<T: Reentrancy> DerefMut for TokenMut<'_, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.token
    }
}

impl<T: Reentrancy + ?Sized> Drop for TokenRef<'_, T> {
    fn drop(&mut self) {
        atomic::compiler_fence(Release);

        let state = self.state.inner.get() - 1;
        self.state.inner.set(state);
        if state == 0 {
            // SAFETY: There is no other borrowing of the non-reentrant token.
            unsafe { self.state.controller.enable() }
        }
    }
}

impl<T: Reentrancy + ?Sized> Drop for TokenMut<'_, T> {
    fn drop(&mut self) {
        atomic::compiler_fence(Release);

        let state = self.state.inner.get() + 1;
        assert!(state == 0);
        self.state.inner.set(0);
        // SAFETY: There is no other borrowing of the non-reentrant token.
        unsafe { self.state.controller.enable() }
    }
}
