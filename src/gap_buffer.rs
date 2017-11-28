use alloc::raw_vec::RawVec;
use std::ptr;
use std::slice;
use std::ops::{Index, IndexMut};
use std::fmt::{Debug, Error, Formatter};
use std::iter::FromIterator;
use std::marker::PhantomData;

/// Creates a [`GapBuffer`] containing the arguments.
///
/// `gap_buffer!` allows [`GapBuffer`] to be defined with the same syntax as `vec!`.
/// There are two forms of this macro:
///
/// - Create a [`GapBuffer`] containing a given list of elements:
///
/// ```
/// # #[macro_use] extern crate gapbuf;
/// # fn main() {
///   let b = gap_buffer![1, 2, 3];
///   assert_eq!(b.len(), 3);
///   assert_eq!(b[0], 1);
///   assert_eq!(b[1], 2);
///   assert_eq!(b[2], 3);
/// # }
/// ```
///
/// - Create a [`GapBuffer`] from a given element and size:
///
/// ```
/// # #[macro_use] extern crate gapbuf;
/// # fn main() {
///   let b = gap_buffer!["abc"; 2];
///   assert_eq!(b.len(), 2);
///   assert_eq!(b[0], "abc");
///   assert_eq!(b[1], "abc");
/// # }
/// ```
///
/// [`GapBuffer`]: ../gapbuf/struct.GapBuffer.html
#[macro_export]
macro_rules! gap_buffer {
    ($elem:expr; $n:expr) => (
        {
            let mut buf = $crate::GapBuffer::with_capacity($n);
            buf.resize($n, $elem);
            buf
        }
    );
    ($($x:expr),*) => (
        {
            let mut buf = $crate::GapBuffer::new();
            $(
                buf.push_back($x);
            )*
            buf
        }
    );
    ($($x:expr,)*) => (gap_buffer![$($x),*])
}

pub struct GapBuffer<T> {
    buf: RawVec<T>,
    len: usize,
    gap: usize,
}

/// Dynamic array that allows efficient insertion and deletion operations clustered near the same location.
/// 
/// `GapBuffer` has a member similer to `Vec`.
impl<T> GapBuffer<T> {
    /// Constructs a new, empty `GapBuffer<T>`.
    ///
    /// The gap buffer will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    /// ```
    /// let mut buf = gapbuf::GapBuffer::<i32>::new();
    ///
    /// assert_eq!(buf.is_empty(), true);
    /// assert_eq!(buf.len(), 0);
    /// assert_eq!(buf.capacity(), 0);
    /// ```
    ///
    /// ```
    /// let mut buf = gapbuf::GapBuffer::new();
    /// buf.push_back(5);
    /// ```
    pub fn new() -> GapBuffer<T> {
        GapBuffer {
            buf: RawVec::<T>::new(),
            len: 0,
            gap: 0,
        }
    }

    /// Constructs a new, empty `GapBuffer<T>` with the specified capacity.
    ///
    /// # Examples
    /// ```
    /// let buf = gapbuf::GapBuffer::<i32>::with_capacity(5);
    ///
    /// assert_eq!(buf.is_empty(), true);
    /// assert_eq!(buf.len(), 0);
    /// assert_eq!(buf.capacity(), 5);
    /// ```
    pub fn with_capacity(capacity: usize) -> GapBuffer<T> {
        GapBuffer {
            buf: RawVec::<T>::with_capacity(capacity),
            len: 0,
            gap: 0,
        }
    }

    /// Create a `GapBuffer` directly from the raw components of another `GapBuffer`.
    pub unsafe fn from_raw_parts(
        ptr: *mut T,
        length: usize,
        gap: usize,
        capacity: usize,
    ) -> GapBuffer<T> {
        GapBuffer {
            buf: RawVec::from_raw_parts(ptr, capacity),
            len: length,
            gap: gap,
        }
    }

    /// Returns the number of elements the `GapBuffer` can hold without reallocating.
    /// 
    /// # Examples
    /// ```
    /// # use gapbuf::GapBuffer;
    /// let buf: GapBuffer<i32> = GapBuffer::with_capacity(10);
    /// assert_eq!(buf.capacity(), 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.buf.cap()
    }

    /// Returns the number of elements in the `GapBuffer`.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the `GapBuffer` contains no elements.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given `GapBuffer<T>`.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling reserve, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    pub fn reserve(&mut self, additional: usize) {
        let cap_old = self.buf.cap();
        self.buf.reserve(self.len, additional);
        self.on_capacity_changed(cap_old);
    }
    pub fn reserve_exact(&mut self, additional: usize) {
        let cap_old = self.buf.cap();
        self.buf.reserve_exact(self.len, additional);
        self.on_capacity_changed(cap_old);
    }
    pub fn shrink_to_fit(&mut self) {
        let len = self.len;
        self.set_gap(len);
        self.buf.shrink_to_fit(self.len);
    }
    fn on_capacity_changed(&mut self, cap_old: usize) {
        let cap_new = self.buf.cap();
        if cap_old == cap_new {
            return;
        }
        let count = self.len - self.gap;
        let p = self.buf.ptr();
        unsafe {
            ptr::copy(p.add(cap_old - count), p.add(cap_new - count), count);
        }
    }

    pub fn set_gap(&mut self, gap: usize) {
        let len = self.len;
        assert!(gap <= len);

        let gap_old = self.gap;
        if gap == gap_old {
            return;
        }

        let src;
        let dest;
        let count;
        if gap < gap_old {
            src = gap;
            dest = gap + self.gap_len();
            count = gap_old - gap;
        } else {
            src = gap_old + self.gap_len();
            dest = gap_old;
            count = gap - gap_old;
        };
        let p = self.buf.ptr();
        unsafe {
            ptr::copy(p.add(src), p.add(dest), count);
        }
        self.gap = gap;
    }
    pub fn gap(&self) -> usize {
        self.gap
    }

    pub fn set_gap_with_reserve(&mut self, gap: usize, additional: usize) {
        self.reserve(additional);
        self.set_gap(gap);
    }

    pub fn insert(&mut self, index: usize, element: T) {
        self.set_gap_with_reserve(index, 1);
        unsafe {
            ptr::write(self.buf.ptr().add(index), element);
        }
        self.gap += 1;
        self.len += 1;
    }

    /// Appends an element to the back of a collection.
    ///
    /// # Panics
    /// Panics if the number of elements in the gap buffer overflows a usize.
    pub fn push_back(&mut self, value: T) {
        let len = self.len;
        self.insert(len, value);
    }
    pub fn push_front(&mut self, value: T) {
        self.insert(0, value);
    }
    pub fn swap(&mut self, a: usize, b: usize) {
        let p = self.buf.ptr();
        let oa = self.get_offset(a);
        let ob = self.get_offset(b);
        unsafe { ptr::swap(p.add(oa), p.add(ob)) }
    }
    pub fn swap_remove(&mut self, index: usize) -> T {
        assert!(index < self.len);

        unsafe {
            let p = self.buf.ptr();
            let value;
            if index < self.gap {
                let pt = p.add(index);
                value = pt.read();
                self.gap -= 1;
                ptr::copy(p.add(self.gap), pt, 1);
                self.len -= 1;
            } else {
                let gap_len = self.gap_len();
                let pt = p.add(index + gap_len);
                value = pt.read();
                ptr::copy(p.add(self.gap + gap_len), pt, 1);
                self.len -= 1;
            }
            value
        }
    }
    pub fn remove(&mut self, index: usize) -> T {
        let offset;
        if self.gap <= index {
            self.set_gap(index);
            offset = self.buf.cap() - self.len + index;
        } else {
            self.set_gap(index + 1);
            self.gap = index;
            offset = index;
        }
        self.len -= 1;
        if self.len == 0 {
            self.gap = 0
        }
        unsafe { ptr::read(self.buf.ptr().add(offset)) }
    }
    pub fn clear(&mut self) {
        self.truncate(0);
    }
    pub fn truncate(&mut self, len: usize) {
        while len < self.len {
            let index = self.len - 1;
            self.remove(index);
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[macro_use] extern crate gapbuf; fn main() {
    /// #
    /// let mut buf = gap_buffer![1, 2, 3, 4];
    /// buf.retain(|&x| x%2 == 0);
    /// assert_eq!(buf, [2, 4]);
    /// #
    /// # }
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        let mut n = 0;
        while n < self.len {
            if f(&self[n]) {
                n += 1;
            } else {
                self.remove(n);
            }
        }
    }
    pub fn pop_front(&mut self) -> Option<T> {
        let len = self.len;
        match len {
            0 => None,
            _ => Some(self.remove(0)),
        }
    }
    pub fn pop_back(&mut self) -> Option<T> {
        let len = self.len;
        match len {
            0 => None,
            _ => Some(self.remove(len - 1)),
        }
    }

    pub fn as_slices(&self) -> (&[T], &[T]) {
        unsafe {
            let p0 = self.buf.ptr();
            let c1 = self.len - self.gap;
            let p1 = p0.add(self.buf.cap() - c1);
            (
                slice::from_raw_parts(p0, self.gap),
                slice::from_raw_parts(p1, c1),
            )
        }
    }
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        unsafe {
            let p0 = self.buf.ptr();
            let c1 = self.len - self.gap;
            let p1 = p0.add(self.buf.cap() - c1);
            (
                slice::from_raw_parts_mut(p0, self.gap),
                slice::from_raw_parts_mut(p1, c1),
            )
        }
    }

    pub fn as_slice(&self) -> GapBufferSlice<T> {
        GapBufferSlice {
            ptr: self.buf.ptr(),
            s: self.get_slice_state(),
            phantom: PhantomData,
        }
    }
    pub fn as_mut_slice(&self) -> GapBufferSliceMut<T> {
        GapBufferSliceMut {
            ptr: self.buf.ptr(),
            s: self.get_slice_state(),
            phantom: PhantomData,
        }
    }

    pub fn iter(&self) -> Iter<T> {
        Iter { buf: self, idx: 0 }
    }
    pub fn iter_mut(&mut self) -> IterMut<T> {
        IterMut { buf: self, idx: 0 }
    }

    fn get_offset(&self, index: usize) -> usize {
        assert!(index < self.len);
        index + if index < self.gap { 0 } else { self.gap_len() }
    }
    fn gap_len(&self) -> usize {
        self.buf.cap() - self.len
    }
    fn get_slice_state(&self) -> GapBufferSliceState {
        GapBufferSliceState {
            cap: self.buf.cap(),
            len: self.len,
            gap: self.gap,
        }
    }
}
impl<T> GapBuffer<T>
where
    T: Clone,
{
    /// Resize the `GapBuffer<T>` in-place so that 'len' is equal to 'new_len'.
    pub fn resize(&mut self, new_len: usize, value: T) {
        self.truncate(new_len);
        while self.len < new_len {
            self.push_back(value.clone());
        }
    }
}

impl<T> Drop for GapBuffer<T> {
    fn drop(&mut self) {
        unsafe {
            let (s0, s1) = self.as_mut_slices();
            try_finally!{
                {
                    ptr::drop_in_place(s0);
                },
                {
                    ptr::drop_in_place(s1);
                }
            }
        }
    }
}

impl<T> Index<usize> for GapBuffer<T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        let p = self.buf.ptr();
        let o = self.get_offset(index);
        unsafe { &*p.add(o) }
    }
}

impl<T> IndexMut<usize> for GapBuffer<T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        let p = self.buf.ptr();
        let o = self.get_offset(index);
        unsafe { &mut *p.add(o) }
    }
}

pub struct Iter<'a, T: 'a> {
    buf: &'a GapBuffer<T>,
    idx: usize,
}
impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        if self.idx == self.buf.len {
            None
        } else {
            let i = self.idx;
            self.idx += 1;
            Some(&self.buf[i])
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.buf.len - self.idx;
        (len, Some(len))
    }
}
impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {}

pub struct IterMut<'a, T: 'a> {
    buf: &'a mut GapBuffer<T>,
    idx: usize,
}
impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        if self.idx == self.buf.len {
            None
        } else {
            let p = self.buf.buf.ptr();
            let o = self.buf.get_offset(self.idx);
            self.idx += 1;
            unsafe { Some(&mut *p.add(o)) }
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.buf.len - self.idx;
        (len, Some(len))
    }
}
impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {}

pub struct IntoIter<T> {
    buf: GapBuffer<T>,
}
impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.buf.pop_front()
    }
}

impl<T> IntoIterator for GapBuffer<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { buf: self }
    }
}

impl<'a, T> IntoIterator for &'a GapBuffer<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut GapBuffer<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;
    fn into_iter(self) -> IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T, S> PartialEq<S> for GapBuffer<T>
where
    T: PartialEq<T>,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn eq(&self, other: &S) -> bool {
        self.iter().eq(other.into_iter())
    }
}



impl<T> Debug for GapBuffer<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.debug_list().entries(self).finish()
    }
}

impl<T> FromIterator<T> for GapBuffer<T> {
    fn from_iter<S: IntoIterator<Item = T>>(s: S) -> GapBuffer<T> {
        let iter = s.into_iter();
        let mut buf = GapBuffer::with_capacity(iter.size_hint().0);
        for item in iter {
            buf.push_back(item);
        }
        buf
    }
}


pub struct GapBufferSlice<'a, T: 'a> {
    ptr: *const T,
    s: GapBufferSliceState,
    phantom: PhantomData<&'a T>,
}
pub struct GapBufferSliceMut<'a, T: 'a> {
    ptr: *mut T,
    s: GapBufferSliceState,
    phantom: PhantomData<&'a T>,
}
struct GapBufferSliceState {
    cap: usize,
    len: usize,
    gap: usize,
}
impl GapBufferSliceState {
    fn gap_len(&self) -> usize {
        self.cap - self.len
    }
    fn offset_of(&self, index: usize) -> usize {
        assert!(index < self.len);
        index + if index < self.gap { 0 } else { self.gap_len() }
    }
}

impl<'a, T: 'a> Index<usize> for GapBufferSlice<'a, T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        unsafe { &*self.ptr.add(self.s.offset_of(index)) }
    }
}

impl<'a, T: 'a> Index<usize> for GapBufferSliceMut<'a, T> {
    type Output = T;
    fn index(&self, index: usize) -> &T {
        unsafe { &*self.ptr.add(self.s.offset_of(index)) }
    }
}
impl<'a, T: 'a> IndexMut<usize> for GapBufferSliceMut<'a, T> {
    fn index_mut(&mut self, index: usize) -> &mut T {
        unsafe { &mut *self.ptr.add(self.s.offset_of(index)) }
    }
}
