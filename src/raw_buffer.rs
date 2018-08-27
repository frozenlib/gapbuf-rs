use std::alloc::*;
use std::mem::*;
use std::ptr::*;

pub struct RawBuffer<T> {
    ptr: NonNull<T>,
    cap: usize,
}

impl<T> RawBuffer<T> {
    #[inline]
    pub fn new() -> Self {
        RawBuffer {
            ptr: NonNull::dangling(),
            cap: 0,
        }
    }
    pub fn realloc(&mut self, new_cap: usize) {
        if self.cap == new_cap {
            return;
        }
        unsafe {
            let p = if new_cap == 0 {
                let p = self.as_ptr() as *mut u8;
                dealloc(p, Self::get_layout(self.cap));
                NonNull::dangling()
            } else {
                let value_size = size_of::<T>();
                if usize::max_value() / value_size < new_cap {
                    panic!("memory size overflow");
                }
                let p = if self.cap == 0 {
                    alloc(Self::get_layout(new_cap))
                } else {
                    let p = self.as_ptr() as *mut u8;
                    let new_size = value_size * new_cap;
                    realloc(p, Self::get_layout(self.cap), new_size)
                };
                if let Some(p) = NonNull::new(p as *mut T) {
                    p
                } else {
                    handle_alloc_error(Self::get_layout(new_cap))
                }
            };
            self.ptr = p;
            self.cap = new_cap;
        }
    }
    fn get_layout(cap: usize) -> Layout {
        Layout::from_size_align(size_of::<T>() * cap, align_of::<T>()).unwrap()
    }

    #[inline]
    pub fn as_ptr(&self) -> *mut T {
        self.ptr.as_ptr()
    }

    #[inline]
    pub fn cap(&self) -> usize {
        self.cap
    }
}
impl<T> Drop for RawBuffer<T> {
    fn drop(&mut self) {
        self.realloc(0);
    }
}
