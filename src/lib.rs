#![feature(generators, generator_trait)]
#![feature(crate_in_paths)]

#[macro_use]
mod finally;

#[macro_use]
mod gap_buffer;

pub use gap_buffer::GapBuffer;
