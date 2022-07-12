//! # Better reference counted strings
//!
//! This crate defines [`RcStr`], a type similar to `Rc<str>`, but with a
//! number of new features and functionality. Theres a list of
//! [benefits][benefits] in the `RcStr` documentation comment which covers some
//! of the reasons you might want to use it over other alternatives.
//!
//! Additionally, if the `substr` feature is enabled (and it is by default) we
//! provide a [`Substr`] type which is essentially a `(RcStr, Range<usize>)`
//! with better ergonomics and more functionality, which represents a shared
//! slice of a "parent" `RcStr`. (Note that in reality, `u32` is used for the
//! index type, but this is not exposed in the API, and can be transparently
//! changed via a cargo feature).
//!
//! [benefits]: struct.RcStr.html#benefits-of-rcstr-over-rcstr
//!
//! ## Feature overview
//!
//! A quick tour of the distinguishing features:
//!
//! ```
//! use rcstr::RcStr;
//!
//! // Works in const:
//! const MY_ARCSTR: RcStr = rcstr::literal!("amazing constant");
//! assert_eq!(MY_ARCSTR, "amazing constant");
//!
//! // `rcstr::literal!` input can come from `include_str!` too:
//! # // We have to fake it here, but this has test coverage and such.
//! # const _: &str = stringify!{
//! const MY_ARCSTR: RcStr = rcstr::literal!(include_str!("my-best-files.txt"));
//! # };
//! ```
//!
//! Or, you can define the literals in normal expressions. Note that these
//! literals are essentially ["Zero Cost"][zero-cost]. Specifically, below we
//! not only don't allocate any heap memory to instantiate `wow` or any of the
//! clones, we also don't have to perform any atomic reads or writes.
//!
//! [zero-cost]: struct.RcStr.html#what-does-zero-cost-literals-mean
//!
//! ```
//! use rcstr::RcStr;
//!
//! let wow: RcStr = rcstr::literal!("Wow!");
//! assert_eq!("Wow!", wow);
//! // This line is probably not something you want to do regularly,
//! // but causes no extra allocations, nor performs any atomic reads
//! // nor writes.
//! let wowzers = wow.clone().clone().clone().clone();
//!
//! // At some point in the future, we can get a `&'static str` out of one
//! // of the literal `RcStr`s too. Note that this returns `None` for
//! // dynamically allocated `RcStr`:
//! let static_str: Option<&'static str> = RcStr::as_static(&wowzers);
//! assert_eq!(static_str, Some("Wow!"));
//! ```
//!
//! Of course, this is in addition to the typical functionality you might find a
//! non-borrowed string type (with the caveat that no way to mutate `RcStr` is
//! provided intentionally).
//!
//! It's an open TODO to update this "feature tour" to include `Substr`.
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(missing_docs)]
#![allow(unknown_lints)]

#[doc(hidden)]
pub extern crate alloc;

#[doc(hidden)]
pub use core;

#[macro_use]
mod mac;
#[cfg(feature = "serde")]
mod impl_serde;
mod rc_str;
pub use rc_str::RcStr;

#[cfg(feature = "substr")]
mod substr;
#[cfg(feature = "substr")]
pub use substr::Substr;

// Not public API, exists for macros
#[doc(hidden)]
pub mod _private {
    // Not part of public API. transmutes a `*const u8` to a `&[u8; N]`.
    //
    // As of writing this, it's unstable to directly deref a raw pointer in
    // const code, we can get around this by transmuting (using the
    // const-transmute union trick) to tranmute from `*const u8` to `&[u8; N]`,
    // and the dereferencing that.
    //
    // ... I'm a little surprised that this is allowed, but in general I do
    // remember a motivation behind stabilizing transmute in `const fn` was that
    // the union trick existed as a workaround.
    //
    // Anyway, this trick is courtesy of rodrimati1992 (that means you have to
    // blame them if it blows up :p).
    #[repr(C)]
    pub union ConstPtrDeref<Arr: Copy + 'static> {
        pub p: *const u8,
        pub a: &'static Arr,
    }
    pub use crate::rc_str::StaticArcStrInner;
    pub use core::primitive::{str, u8};
}
