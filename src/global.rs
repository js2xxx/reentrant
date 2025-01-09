/// The global reentrancy controller.
///
/// This structure is the default reentrancy controller interface type used by
/// the library, which forwards to the actual reentrancy implementation via a
/// series of dedicated ABI calls, just like how global allocators works.
pub struct Global;

#[cfg(feature = "global")]
unsafe extern "Rust" {
    unsafe fn __rust_disable_reentrancy();

    unsafe fn __rust_enable_reentrancy();

    unsafe fn __rust_is_reentrant() -> bool;

    unsafe fn __rust_reentrant_handler();
}

#[cfg(feature = "global")]
unsafe impl Reentrancy for Global {
    unsafe fn enable(&self) {
        unsafe { __rust_enable_reentrancy() };
    }

    fn disable(&self) {
        unsafe { __rust_disable_reentrancy() };
    }

    fn is_reentrant(&self) -> bool {
        unsafe { __rust_is_reentrant() }
    }
}

#[cfg(feature = "global")]
fn default_reentrant_handler() {
    unsafe { __rust_reentrant_handler() }
}

/// Set up the global reentrancy controller.
///
/// Marking a type/static as `reentrancy_impl` will forward its implementation
/// to [the default interface](Global) used by this library.
///
/// See [the crate-level documentation](crate) for more information.
#[cfg(feature = "global")]
#[macro_export]
#[allow_internal_unsafe]
macro_rules! reentrancy_impl {
    ($e:expr) => {
        #[unsafe(no_mangle)]
        extern "Rust" fn __rust_disable_reentrancy() {
            $crate::Reentrancy::disable(&$e);
        }

        #[unsafe(no_mangle)]
        unsafe extern "Rust" fn __rust_enable_reentrancy() {
            unsafe { $crate::Reentrancy::enable(&$e) };
        }

        #[unsafe(no_mangle)]
        extern "Rust" fn __rust_is_reentrant() -> bool {
            $crate::Reentrancy::is_reentrant(&$e)
        }
    };
}

/// Set up the global reentrant handler.
///
/// This handler will be called when the global reentrancy is enabled.
#[cfg(feature = "global")]
#[macro_export]
#[allow_internal_unsafe]
macro_rules! reentrant_handler {
    ($e:expr) => {
        #[unsafe(no_mangle)]
        extern "Rust" fn __rust_reentrant_handler() {
            $e();
        }
    };
}

#[cfg(feature = "tls")]
mod tls {
    use super::default_reentrant_handler;
    use crate::{
        Global, State, Token,
        state::{BorrowError, BorrowMutError},
    };

    #[thread_local]
    static REENTRANCY_STATE: State<Global> =
        unsafe { State::new(Global, default_reentrant_handler) };

    /// Tries to obtain a immutable reference to the non-reentrant token of the
    /// current execution unit, and use it within the function if successfully
    /// obtained.
    ///
    /// The passed function will be called in a non-reentrant context.
    ///
    /// See [`State::try_borrow`] for more information.
    #[track_caller]
    pub fn try_with<T>(f: impl FnOnce(&Token) -> T) -> Result<T, BorrowError> {
        REENTRANCY_STATE.try_borrow().map(|token| f(&token))
    }

    /// Obtains a immutable reference to the non-reentrant token of the current
    /// execution unit, and use it within the function.
    ///
    /// The passed function will be called in a non-reentrant context.
    ///
    /// See [`State::borrow`] for more information.
    #[track_caller]
    pub fn with<T>(f: impl FnOnce(&Token) -> T) -> T {
        f(&REENTRANCY_STATE.borrow())
    }

    /// Tries to obtain the mutable reference to the non-reentrant token of the
    /// current execution unit, and use it within the function if successfully
    /// obtained.
    ///
    /// The passed function will be called in a non-reentrant context.
    ///
    /// See [`State::try_borrow_mut`] for more information.
    #[track_caller]
    pub fn try_with_mut<T>(f: impl FnOnce(&mut Token) -> T) -> Result<T, BorrowMutError> {
        REENTRANCY_STATE
            .try_borrow_mut()
            .map(|mut token| f(&mut token))
    }

    /// Obtains the mutable reference to the non-reentrant token of the current
    /// execution unit, and use it within the function.
    ///
    /// The passed function will be called in a non-reentrant context.
    ///
    /// See [`State::borrow_mut`] for more information.
    #[track_caller]
    pub fn with_mut<T>(f: impl FnOnce(&mut Token) -> T) -> T {
        f(&mut REENTRANCY_STATE.borrow_mut())
    }
}
#[cfg(feature = "tls")]
pub use self::tls::{try_with, try_with_mut, with, with_mut};
use crate::Reentrancy;

#[cfg(feature = "default")]
mod default {
    use crate::Reentrancy;
    struct Noop;
    reentrancy_impl!(Noop);

    unsafe impl Reentrancy for Noop {
        unsafe fn enable(&self) {}

        fn disable(&self) {}

        fn is_reentrant(&self) -> bool {
            false
        }
    }

    reentrant_handler!(|| {});
}
