//! `gapbuf` provides the type [`GapBuffer`].
//! `GapBuffer` has methods similar to `Vec`.
//!
//! # Examples
//!
//! ```
//! #[macro_use]
//! extern crate gapbuf;
//!
//! fn main() {
//!     let mut b = gap_buffer![1, 2, 3];
//!
//!     b.insert(1, 10);
//!     assert_eq!(b, [1, 10, 2, 3]);
//!
//!     b.remove(2);
//!     assert_eq!(b, [1, 10, 3]);
//! }
//!
//! ```

#[macro_use]
mod finally;

#[macro_use]
mod gap_buffer;

pub use gap_buffer::*;
