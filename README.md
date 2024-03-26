# A Reentrancy Model in Rust

A model for protecting non-reentrant/TLS data structures using a static version of [ghost cells](https://docs.rs/ghost-cell).

The term "reentrancy" here refers to revisiting data or recursing functions single-threadedly where multiple slices of control flows are executed in sequence.

# Problem

## TLS variables v.s. The borrow checker

Non-reentrant/TLS data structures are common in Rust, but they are pretty tricky to handle by the aliasing XOR mutability borrow rules because of their static lifetime and visibility to unscoped code contexts. For example:

```compile_fail
thread_local! {
    // We want to mutate the this variable using the `mut` keyword,
    // but the macro prevents us to do that because `static mut`s are evil.
    static mut MY_DATA: String = String::new();
}
```

To make the above code compile, the TLS variable usually ends up being wrapped in a `Cell` or a `RefCell`, which either requires the wrapped data to implement `Copy` or adds runtime cost for borrow checking (per variable), which seems not ideal.

## Lack of a unified reentrancy model

The current Rust lacks support for a unified reentrancy model in its built-in type system, for its borrow rules are based on the call stack, which lacks the instrumentation of the global data in the program.

To get rid of this problem, current users have to delay the checking of such data until runtime, which includes not only the `Cell`/`RefCell` example above but also the per-CPU hardware/software states (e.g. interrupts, signals, kernel preemption count, etc.).

# Adoption

## Ghost cells

Ghost cells separate the borrow rules from the data storage itself while preserving the zero-runtime-cost & safe borrow checks. An example from [its official documentation](https://docs.rs/ghost-cell) is shown below:

```rust
use ghost_cell::{GhostToken, GhostCell};

let n = 42;

let value = GhostToken::new(|mut token| {
    let cell = GhostCell::new(42);

    let vec: Vec<_> = (0..n).map(|_| &cell).collect();

    *vec[n / 2].borrow_mut(&mut token) = 33;

    *cell.borrow(&token)
});

assert_eq!(33, value);
```

In the example above, a ghost token creates a scope, where all the ghost cells bound to the scope can borrow their data arbitrarily by tagging the ghost token.

## Modification

Aside from its benefits of zero-runtime-cost & safe borrow checks, the creation of ghost tokens is again tricky to perform, because ghost tokens cannot be created with the `'static` lifetime.

Thus, the scoped creation is substituted with a `RefCell`-like approach which guarantees the uniqueness of tokens per execution unit. Although the runtime cost of borrow checking cannot be avoided, it can be significantly reduced by adapting to a larger scope:

```rust
#![feature(lazy_cell)]
#![feature(thread_local)]

use std::cell::LazyCell;
use reentrant::LocalCell;

#[thread_local]
static MY_DATA: LazyCell<LocalCell<String>>
    = LazyCell::new(|| LocalCell::new(String::from("A")));
#[thread_local]
static ANOTHER_DATA: LocalCell<Vec<u8>> = LocalCell::new(Vec::new());

reentrant::with_mut(|token| {
    // Multiple mutable borrows can be taken out at the same time.
    MY_DATA.borrow_mut(token).push_str("Hello, world!");
    ANOTHER_DATA.borrow_mut(token).extend([1, 2, 3, 4, 5]);

    // The references of those thread-locals can't be assigned to
    // other thread locals because of the non-`'static` lifetime
    // of `token`, so they can be safely exposed here.
    println!("{} {:?}", MY_DATA.borrow(token), ANOTHER_DATA.borrow(token));

    // And the token can be passed into nested scopes, such as
    // a deep chain of function calls.
    use_with_token(token);
});

fn use_with_token(token: &mut reentrant::Token) {
    // Rust std's thread_local can also be used with non-reentrant tokens.
    std::thread_local! {
        static IN_SCOPE: LocalCell<String> = LocalCell::new(String::new());
    }
    IN_SCOPE.with(|data| data.borrow_mut(token).push_str("Hello, world!"));
}
```

## Reentrancy, Again

The example above is not very connected to the concept of reentrancy, but here we add another trait to tackle this problem.

The `Reentrancy` trait controls the low-level reentrancy state of the current execution unit, such as disabling/enabling interrupts in a CPU core, or (un)masking signals in a unix signal-some code context. The default feature uses a noop reentrancy controller, but users can implement their own with the default feature disabled:

```rust
use reentrant::{Reentrancy, reentrancy_impl};
use x86_64::instructions::interrupts;

struct X86Interrupts;
reentrancy_impl!(X86Interrupts);

unsafe impl Reentrancy for X86Interrupts {
    unsafe fn enable(&self) {
        interrupts::enable();
    }

    fn disable(&self) {
        interrupts::disable();
    }

    fn is_reentrant(&self) -> bool {
        interrupts::are_enabled()
    }
}
```

Besides, for spin locks that require non-reentrancy (in the Linux kernel for example to disable preemption), simply wrap the lock guard in `reentrant::with`, or add a `Token` reference argument to the locking function to bind the lifetime of the lock guard to the token.

# Caveats

The non-reentrant token is unique per execution unit, which means that
`with_mut` cannot be nested, while adding `token: &(mut)
reentrant::Token` to the argument list of functions may decrease the readability of codes.

# References

- [ghost-cell](https://docs.rs/ghost-cell)
- [A post](https://users.rust-lang.org/t/a-better-term-than-thread-safe/73199/4) in the Rust forum about the relationship between reentrancy, thread safety, and borrowing rules

# License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.