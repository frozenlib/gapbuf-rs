//! `gap_buf` provides the type [`GapBuffer`].
//! `GapBuffer` has methods similar to [`Vec`](std::vec::Vec).
//!
//! # Examples
//!
//! ```
//! use gap_buf::gap_buffer;
//!
//! let mut b = gap_buffer![1, 2, 3];
//!
//! b.insert(1, 10);
//! assert_eq!(b, [1, 10, 2, 3]);
//!
//! b.remove(2);
//! assert_eq!(b, [1, 10, 3]);
//! ```
//!
#![doc(html_root_url = "https://docs.rs/gap_buf/0.1.2")]

#[macro_use]
mod finally;

#[macro_use]
mod gap_buffer;

pub use crate::gap_buffer::*;
