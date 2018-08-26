#![feature(alloc)]
#![feature(generators, generator_trait)]
#![feature(test)]
#![feature(raw_vec_internals)]

extern crate alloc;

#[macro_use]
mod finally;

#[macro_use]
mod gap_buffer;
mod tests;

pub use gap_buffer::GapBuffer;
