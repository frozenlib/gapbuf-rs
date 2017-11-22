#![feature(alloc)]
#![feature(pointer_methods)]
#![feature(conservative_impl_trait)]
#![feature(generators, generator_trait)]
#![feature(test)]


extern crate alloc;

#[macro_use]
mod finally;

#[macro_use]
mod gap_buffer;
mod tests;

pub use gap_buffer::GapBuffer;
