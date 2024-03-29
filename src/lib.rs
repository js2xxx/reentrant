//! A model for protecting non-reentrant/TLS data structures using a static
//! version of [`ghost cells`](https://docs.rs/ghost-cell).
//!
//! # Usage
//!
//! For the simplest use cases, wrapping thread-local variables with
//! [`LocalCell`]s, and accessing them via [`with`] and [`with_mut`] will
//! suffice:
//!
//! ```rust
//! #![feature(lazy_cell)]
//! #![feature(thread_local)]
//!
//! use std::cell::LazyCell;
//! use reentrant::LocalCell;
//!
//! #[thread_local]
//! static MY_DATA: LazyCell<LocalCell<String>>
//!     = LazyCell::new(|| LocalCell::new(String::from("A")));
//! #[thread_local]
//! static ANOTHER_DATA: LocalCell<Vec<u8>> = LocalCell::new(Vec::new());
//!
//! reentrant::with_mut(|token| {
//!     // Multiple mutable borrows can be taken out at the same time.
//!     MY_DATA.borrow_mut(token).push_str("Hello, world!");
//!     ANOTHER_DATA.borrow_mut(token).extend([1, 2, 3, 4, 5]);
//!
//!     // The references of those thread-locals can't be assigned to
//!     // other thread locals because of the non-`'static` lifetime
//!     // of `token`, so they can be safely exposed here.
//!     println!("{} {:?}", MY_DATA.borrow(token), ANOTHER_DATA.borrow(token));
//!
//!     // And the token can be passed into nested scopes, such as
//!     // a deep chain of function calls.
//!     use_with_token(token);
//! });
//!
//! fn use_with_token(token: &mut reentrant::Token) {
//!     // Rust std's thread_local can also be used with non-reentrant tokens.
//!     std::thread_local! {
//!         static IN_SCOPE: LocalCell<String> = LocalCell::new(String::new());
//!     }
//!     IN_SCOPE.with(|data| data.borrow_mut(token).push_str("Hello, world!"));
//! }
//! ```
//!
//! # Customize the reentrancy controller
//!
//! The example above is not very connected to the concept of reentrancy, but
//! here we add another [trait](Reentrancy) to actually tackle this problem.
//!
//! The `Reentrancy` trait controls the low-level reentrancy state of the
//! current execution unit, such as disabling/enabling interrupts in a CPU core,
//! or (un)masking signals in a unix signal-some code context. The default
//! feature uses a noop reentrancy controller, but users can to implement their
//! own with the default feature disabled:
//!
//! ```rust,ignore
//! use reentrant::{Reentrancy, reentrancy_impl, reentrant_handler};
//! use x86_64::instructions::interrupts;
//!
//! struct X86Interrupts;
//! reentrancy_impl!(X86Interrupts);
//!
//! unsafe impl Reentrancy for X86Interrupts {
//!     unsafe fn enable(&self) {
//!         interrupts::enable();
//!     }
//!
//!     fn disable(&self) {
//!         interrupts::disable();
//!     }
//!
//!     fn is_reentrant(&self) -> bool {
//!         interrupts::are_enabled()
//!     }
//! }
//!
//! /// This function will be called right after
//! /// the current execution unit becomes reentrant.
//! fn handler() {
//!     // preempt_schedule();
//! }
//! reentrant_handler!(handler);
//! ```
//!
//! Besides, for spin locks that require non-reentrancy (in the Linux kernel for
//! example to disable preemption), simply wrap the lock guard in
//! [`reentrant::with`](with), or add a `Token` reference argument to the
//! locking function in order to bound the lifetime of the lock guard to the
//! token.
#![no_std]
#![deny(future_incompatible)]
#![deny(rust_2018_idioms)]
#![deny(rust_2024_compatibility)]
#![warn(missing_docs)]
#![allow(internal_features)]
#![feature(allow_internal_unsafe)]
#![feature(array_windows)]
#![feature(strict_provenance)]
#![feature(thread_local)]

pub mod cell;
mod global;
pub mod state;

#[cfg(test)]
extern crate std;

pub use self::{
    cell::LocalCell,
    global::{try_with, try_with_mut, with, with_mut, Global},
    state::{Reentrancy, State, Token},
};
