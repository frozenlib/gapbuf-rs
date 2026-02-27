use std::alloc::{Layout, alloc, dealloc, handle_alloc_error, realloc};
use std::cmp::{Ordering, max};
use std::fmt::{Debug, Error, Formatter};
use std::hash::{Hash, Hasher};
use std::iter::{Chain, Fuse, FusedIterator};
use std::marker::PhantomData;
use std::mem::{self, align_of, needs_drop, size_of};
use std::ops::{Deref, DerefMut, Drop, FnMut, Index, IndexMut, RangeBounds};
use std::ptr::{self, NonNull, copy, drop_in_place, write};
use std::slice;

/// Creates a [`GapBuffer`] containing the arguments.
///
/// `gap_buffer!` allows [`GapBuffer`] to be defined with the same syntax as [`vec!`](std::vec!).
/// There are two forms of this macro:
///
/// - Create a [`GapBuffer`] containing a given list of elements:
///
/// ```
/// use gap_buf::gap_buffer;
/// let b = gap_buffer![1, 2, 3];
/// assert_eq!(b.len(), 3);
/// assert_eq!(b[0], 1);
/// assert_eq!(b[1], 2);
/// assert_eq!(b[2], 3);
/// ```
///
/// - Create a [`GapBuffer`] from a given element and size:
///
/// ```
/// use gap_buf::gap_buffer;
/// let b = gap_buffer!["abc"; 2];
/// assert_eq!(b.len(), 2);
/// assert_eq!(b[0], "abc");
/// assert_eq!(b[1], "abc");
/// ```
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

/// Dynamic array that allows efficient insertion and deletion operations clustered near the same location.
///
/// `GapBuffer<T>` has methods similar to [`Vec`](std::vec::Vec).
#[derive(Hash)]
#[cfg_attr(feature = "bincode", derive(bincode::Decode, bincode::Encode))]
pub struct GapBuffer<T>(RawGapBuffer<T>);

impl<T> GapBuffer<T> {
    /// Constructs a new, empty `GapBuffer<T>`.
    ///
    /// The gap buffer will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    /// ```
    /// # use gap_buf::GapBuffer;
    /// let mut buf = GapBuffer::<i32>::new();
    ///
    /// assert_eq!(buf.is_empty(), true);
    /// assert_eq!(buf.len(), 0);
    /// assert_eq!(buf.capacity(), 0);
    /// ```
    ///
    /// ```
    /// use gap_buf::GapBuffer;
    ///
    /// let mut buf = GapBuffer::new();
    /// buf.push_back(5);
    /// ```
    #[inline]
    pub const fn new() -> Self {
        GapBuffer(RawGapBuffer::new())
    }

    /// Constructs a new, empty `GapBuffer<T>` with the specified capacity.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::GapBuffer;
    ///
    /// let buf: GapBuffer<i32> = GapBuffer::with_capacity(5);
    /// assert_eq!(buf.is_empty(), true);
    /// assert_eq!(buf.len(), 0);
    /// assert_eq!(buf.capacity(), 5);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        let mut buf = GapBuffer::new();
        buf.reserve_exact(capacity);
        buf
    }

    /// Returns the number of elements the `GapBuffer<T>` can hold without reallocating.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::GapBuffer;
    ///
    /// let buf: GapBuffer<i32> = GapBuffer::with_capacity(10);
    /// assert_eq!(buf.capacity(), 10);
    /// ```
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.0.0.cap
    }

    /// Reserves capacity for at least additional more elements to be inserted in the given `GapBuffer<T>`.
    /// The collection may reserve more space to avoid frequent reallocations.
    /// After calling reserve, capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    /// Panics if the new capacity overflows usize.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::GapBuffer;
    ///
    /// let mut buf = GapBuffer::new();
    /// buf.push_back(1);
    /// buf.reserve(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.reserve_as(additional, false);
    }

    /// Reserves the minimum capacity for exactly additional more elements to be inserted in the given `GapBuffer<T>`.
    /// After calling reserve_exact, capacity will be greater than or equal to self.len() + additional.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it requests.
    /// Therefore capacity can not be relied upon to be precisely minimal.
    /// Prefer [`reserve`] if future insertions are expected.
    ///
    /// # Panics
    /// Panics if the new capacity overflows usize.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::GapBuffer;
    ///
    /// let mut buf = GapBuffer::new();
    /// buf.push_back(1);
    /// buf.reserve_exact(10);
    /// assert!(buf.capacity() >= 11);
    /// ```
    ///
    /// [`reserve`]: #method.reserve
    pub fn reserve_exact(&mut self, additional: usize) {
        self.reserve_as(additional, true);
    }
    fn reserve_as(&mut self, additional: usize, exact: bool) {
        let len = self.len();
        let old_cap = self.cap;
        let new_cap = len.checked_add(additional).expect("capacity overflow");
        if new_cap <= old_cap {
            return;
        }
        let new_cap = if exact {
            new_cap
        } else {
            max(old_cap.saturating_mul(2), new_cap)
        };
        self.0.realloc(new_cap);

        unsafe {
            let p = self.as_mut_ptr();
            let count = len - self.gap();
            copy(p.add(old_cap - count), p.add(new_cap - count), count);
        }
    }

    /// Shrinks the capacity of the `GapBuffer<T>` as much as possible.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::GapBuffer;
    ///
    /// let mut buf = GapBuffer::new();
    /// buf.push_back(1);
    ///
    /// buf.reserve(10);
    /// assert!(buf.capacity() >= 11);
    ///
    /// buf.shrink_to_fit();
    /// assert_eq!(buf.capacity(), 1);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        let len = self.len();
        self.set_gap(len);
        self.0.realloc(len);
    }

    /// Set gap offset of the `GapBuffer<T>`.
    ///
    /// # Panics
    /// Panics if `index > len`.
    ///
    /// # Computational amount
    /// `O(n)` , `n = |self.gap() - gap|`
    #[inline]
    #[track_caller]
    pub fn set_gap(&mut self, gap: usize) {
        assert!(gap <= self.len());
        if gap != self.gap() {
            self.move_values(gap);
            self.gap = gap;
        }
    }

    /// Return gap offset of the `GapBuffer<T>`.
    #[inline]
    pub const fn gap(&self) -> usize {
        self.0.0.gap
    }

    #[inline]
    fn set_gap_with_reserve(&mut self, gap: usize, additional: usize) {
        self.reserve(additional);
        self.set_gap(gap);
    }

    /// Inserts an element at position index within the `GapBuffer<T>`.
    ///
    /// # Panics
    /// Panics if `index > len`.
    ///
    /// Panics if the number of elements in the gap buffer overflows a usize.
    ///
    /// # Computational amount
    /// `O(n)` , `n = |index - self.gap()|`
    #[inline]
    #[track_caller]
    pub fn insert(&mut self, index: usize, element: T) {
        assert!(index <= self.len());
        if self.gap() != index || self.len == self.capacity() {
            self.set_gap_with_reserve(index, 1);
        }
        unsafe {
            write(self.as_mut_ptr().add(index), element);
        }
        self.gap += 1;
        self.len += 1;
    }

    #[deprecated(note = "insert_iter renamed to insert_many.")]
    pub fn insert_iter(&mut self, index: usize, iter: impl IntoIterator<Item = T>) {
        self.insert_many(index, iter);
    }

    /// Inserts multiple elements at position index within the `GapBuffer<T>`.
    ///
    /// # Panics
    /// Panics if `index > len`.
    ///
    /// Panics if the number of elements in the gap buffer overflows a usize.
    #[track_caller]
    pub fn insert_many(&mut self, mut index: usize, iter: impl IntoIterator<Item = T>) {
        assert!(index <= self.len());
        let mut iter = iter.into_iter();
        let min_len = iter.size_hint().0;
        if let Some(value) = iter.next() {
            self.set_gap_with_reserve(index, max(min_len, 1));
            let p = self.as_mut_ptr();
            unsafe {
                write(p.add(index), value);
                self.gap += 1;
                self.len += 1;
                index += 1;
                for _ in 1..min_len {
                    if let Some(value) = iter.next() {
                        write(p.add(index), value);
                        self.gap += 1;
                        self.len += 1;
                        index += 1;
                    } else {
                        return;
                    }
                }
            }
            for value in iter {
                self.insert(index, value);
                index += 1;
            }
        }
    }

    /// Appends an element to the back of a GapBuffer.
    ///
    /// # Panics
    /// Panics if the number of elements in the gap buffer overflows a usize.
    #[inline]
    pub fn push_back(&mut self, value: T) {
        let len = self.len;
        self.insert(len, value);
    }

    /// Prepends an element to the GapBuffer.
    ///
    /// # Panics
    /// Panics if the number of elements in the gap buffer overflows a usize.
    #[inline]
    pub fn push_front(&mut self, value: T) {
        let len = self.len();
        if self.gap() != 0 || len == self.capacity() {
            self.set_gap_with_reserve(0, 1);
        }
        unsafe {
            write(self.as_mut_ptr().add(self.cap - self.len - 1), value);
        }
        self.len += 1;
    }

    /// Removes an element from the GapBuffer and returns it.
    ///
    /// The removed element is replaced by the near the gap.
    ///
    /// # Panics
    /// Panics if `index >= self.len()`.
    ///
    /// # Computational amount
    /// `O(1)`
    ///
    /// # Examples
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4, 5];
    /// buf.set_gap(5);
    /// let value = buf.swap_remove(0);
    /// assert_eq!(value, 1);
    /// assert_eq!(buf, [5, 2, 3, 4]);
    /// ```
    #[track_caller]
    pub fn swap_remove(&mut self, index: usize) -> T {
        assert!(index < self.len());

        unsafe {
            let p = self.as_mut_ptr();
            let value;
            if index < self.gap() {
                let pt = p.add(index);
                value = pt.read();
                self.gap -= 1;
                copy(p.add(self.gap), pt, 1);
            } else {
                let gap_len = self.gap_len();
                let pt = p.add(index + gap_len);
                value = pt.read();
                copy(p.add(self.gap + gap_len), pt, 1);
            }
            self.len -= 1;
            value
        }
    }

    /// Removes an element from the GapBuffer and returns it.
    ///
    /// # Panics
    /// Panics if `index >= self.len()`.
    ///
    /// # Computational amount
    /// `O(n)`, `n = |index - self.gap()|`
    ///
    /// # Examples
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4, 5];
    /// let value = buf.remove(0);
    /// assert_eq!(value, 1);
    /// assert_eq!(buf, [2, 3, 4, 5]);
    /// ```
    #[track_caller]
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index <= self.len());
        let offset;
        if self.gap() <= index {
            self.set_gap(index);
            offset = self.cap - self.len() + index;
        } else {
            self.set_gap(index + 1);
            self.gap = index;
            offset = index;
        }
        self.len -= 1;
        if self.len == 0 {
            self.gap = 0
        }
        unsafe { ptr::read(self.as_ptr().add(offset)) }
    }

    /// Clears the GapBuffer, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity of the GapBuffer.
    pub fn clear(&mut self) {
        self.truncate(0);
    }

    /// Shortens the GapBuffer, keeping the first len elements and dropping the rest.
    ///
    /// If len is greater than the GapBuffer's current length, this has no effect.
    ///
    /// Note that this method has no effect on the allocated capacity of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4];
    /// buf.truncate(2);
    /// assert_eq!(buf, [1, 2]);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if needs_drop::<T>() {
            while len < self.len {
                let index = self.len - 1;
                self.remove(index);
            }
        } else {
            if self.gap < len {
                self.set_gap(len);
            } else {
                self.gap = len;
            }
            self.len = len;
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4];
    /// buf.retain(|&x| x%2 == 0);
    /// assert_eq!(buf, [2, 4]);
    /// ```
    pub fn retain(&mut self, mut f: impl FnMut(&T) -> bool) {
        let mut n = 0;
        while n < self.len {
            if f(&self[n]) {
                n += 1;
            } else {
                self.remove(n);
            }
        }
    }

    /// Removes the first element and returns it, or None if the GapBuffer is empty.
    pub fn pop_front(&mut self) -> Option<T> {
        let len = self.len;
        match len {
            0 => None,
            _ => Some(self.remove(0)),
        }
    }

    /// Removes the last element and returns it, or None if the GapBuffer is empty.
    pub fn pop_back(&mut self) -> Option<T> {
        let len = self.len;
        match len {
            0 => None,
            _ => Some(self.remove(len - 1)),
        }
    }

    /// Creates a draining iterator that removes the specified range in the GapBuffer and yields the removed items.
    ///
    /// - Note 1: The element range is removed even if the iterator is only partially consumed or not consumed at all.
    /// - Note 2: It is unspecified how many elements are removed from the GapBuffer if the Drain value is leaked.
    ///
    /// # Panics
    /// Panics if the `range` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4];
    ///
    /// let d : Vec<_> = buf.drain(1..3).collect();
    /// assert_eq!(buf, [1, 4]);
    /// assert_eq!(d, [2, 3]);
    ///
    /// buf.drain(..);
    /// assert_eq!(buf.is_empty(), true);
    /// ```
    pub fn drain(&mut self, range: impl RangeBounds<usize>) -> Drain<'_, T> {
        let (idx, len) = self.to_idx_len(range);
        Drain {
            buf: self,
            idx,
            len,
        }
    }

    /// Creates an extracting iterator that removes elements from the specified range in the GapBuffer based on a predicate
    ///
    /// Note that this iterator will only remove elements that are consumed. If dropped, it will retain the remaining elements.
    ///
    /// # Panics
    ///
    /// Panics if the `range` is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4];
    ///
    /// let d : Vec<_> = buf.extract_if(.., |num| *num % 2 == 1).collect();
    /// assert_eq!(buf, [2, 4]);
    /// assert_eq!(d, [1, 3]);
    ///
    /// buf.extract_if(.., |_| true);
    /// assert_eq!(buf.is_empty(), false);
    /// ```
    pub fn extract_if<F>(
        &mut self,
        range: impl RangeBounds<usize>,
        filter: F,
    ) -> ExtractIf<'_, T, F>
    where
        F: FnMut(&mut T) -> bool,
    {
        let (idx, end) = self.to_idx_len(range);
        ExtractIf {
            buf: self,
            idx,
            end,
            pred: filter,
        }
    }

    /// Creates a splicing iterator
    /// that replaces the specified range in the GapBuffer with the given replace_with iterator and
    /// yields the removed items.
    /// replace_with does not need to be the same length as range.
    ///
    /// The element range is removed even if the iterator is not consumed until the end.
    ///
    /// This is optimal if the length of `range` is equal to the length of `replace_with`.
    /// Otherwise, call [`GapBuffer::set_gap`] internally.
    ///
    /// # Examples
    ///
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut b = gap_buffer![1, 2, 3, 4];
    /// let r : Vec<_> = b.splice(1..3, vec![7, 8, 9]).collect();
    ///
    /// assert_eq!(b, [1, 7, 8, 9, 4]);
    /// assert_eq!(r, [2, 3]);
    /// ```
    pub fn splice<I: IntoIterator<Item = T>>(
        &mut self,
        range: impl RangeBounds<usize>,
        replace_with: I,
    ) -> Splice<'_, T, I::IntoIter> {
        let (idx, len) = self.to_idx_len(range);
        Splice {
            buf: self,
            idx,
            end: idx + len,
            iter: replace_with.into_iter().fuse(),
        }
    }
}

/// A splicing iterator for [`GapBuffer`].
///
/// This struct is created by [`GapBuffer::splice`].
pub struct Splice<'gb, T: 'gb, I: Iterator<Item = T>> {
    buf: &'gb mut GapBuffer<T>,
    idx: usize,
    end: usize,
    iter: Fuse<I>,
}
impl<'gb, T: 'gb, I: Iterator<Item = T>> Iterator for Splice<'gb, T, I> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.idx < self.end {
            if let Some(value) = self.iter.next() {
                let value = mem::replace(&mut self.buf[self.idx], value);
                self.idx += 1;
                Some(value)
            } else {
                let value = self.buf.remove(self.idx);
                self.end -= 1;
                Some(value)
            }
        } else {
            None
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.end - self.idx;
        (size, Some(size))
    }
}
impl<'gb, T: 'gb, I: Iterator<Item = T>> Drop for Splice<'gb, T, I> {
    fn drop(&mut self) {
        while self.next().is_some() {}
        self.buf.insert_many(self.idx, &mut self.iter);
    }
}
impl<'gb, T: 'gb, I: Iterator<Item = T>> ExactSizeIterator for Splice<'gb, T, I> {}
impl<'gb, T: 'gb, I: Iterator<Item = T>> FusedIterator for Splice<'gb, T, I> {}
impl<'gb, T: 'gb, I: DoubleEndedIterator<Item = T>> DoubleEndedIterator for Splice<'gb, T, I> {
    fn next_back(&mut self) -> Option<T> {
        if self.idx < self.end {
            let i = self.end - 1;
            let value = if let Some(value) = self.iter.next_back() {
                mem::replace(&mut self.buf[i], value)
            } else {
                self.buf.remove(i)
            };
            self.end -= 1;
            Some(value)
        } else {
            None
        }
    }
}

impl<T> GapBuffer<T>
where
    T: Clone,
{
    /// Resize the `GapBuffer<T>` in-place so that `len` is equal to `new_len`.
    pub fn resize(&mut self, new_len: usize, value: T) {
        let old_len = self.len();
        if new_len < old_len {
            self.truncate(new_len);
        }
        if new_len > old_len {
            self.reserve(new_len - old_len);
            while self.len < new_len {
                self.push_back(value.clone());
            }
        }
    }
}

impl<T> Drop for GapBuffer<T> {
    fn drop(&mut self) {
        unsafe {
            let (s0, s1) = self.as_mut_slices();
            try_finally!(drop_in_place(s0), drop_in_place(s1));
        }
    }
}

impl<T> Deref for GapBuffer<T> {
    type Target = Slice<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &(self.0).0
    }
}
impl<T> DerefMut for GapBuffer<T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut (self.0).0
    }
}

impl<T> From<Vec<T>> for GapBuffer<T> {
    /// An `O(1)` conversion from a [`Vec<T>`].
    fn from(value: Vec<T>) -> Self {
        Self(RawGapBuffer::from_vec(value))
    }
}

impl<T> FromIterator<T> for GapBuffer<T> {
    fn from_iter<S: IntoIterator<Item = T>>(s: S) -> GapBuffer<T> {
        let mut buf = GapBuffer::new();
        buf.extend(s);
        buf
    }
}

impl<T: Clone> Clone for GapBuffer<T> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T> Extend<T> for GapBuffer<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let len = self.len;
        self.insert_many(len, iter);
    }
}

impl<'gb, T: 'gb + Copy> Extend<&'gb T> for GapBuffer<T> {
    fn extend<I: IntoIterator<Item = &'gb T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }
}

#[derive(Hash)]
#[cfg_attr(feature = "bincode", derive(bincode::Decode, bincode::Encode))]
struct RawGapBuffer<T>(Slice<T>);

impl<T> RawGapBuffer<T> {
    const fn new() -> Self {
        RawGapBuffer(Slice::empty())
    }

    const fn from_vec(vec: Vec<T>) -> Self {
        Self(Slice::from_vec(vec))
    }

    fn realloc(&mut self, new_cap: usize) {
        let old_cap = self.0.cap;
        if old_cap == new_cap {
            return;
        }
        if size_of::<T>() != 0 {
            unsafe {
                let old_layout = Self::get_layout(old_cap);
                let new_layout = Self::get_layout(new_cap);
                let p = self.0.ptr.as_ptr() as *mut u8;
                self.0.ptr = if new_cap == 0 {
                    dealloc(p, old_layout);
                    NonNull::dangling()
                } else {
                    NonNull::new(if old_cap == 0 {
                        alloc(new_layout)
                    } else {
                        realloc(p, old_layout, new_layout.size())
                    } as *mut T)
                    .unwrap_or_else(|| handle_alloc_error(new_layout))
                };
            }
        }
        self.0.cap = new_cap;
    }

    fn get_layout(cap: usize) -> Layout {
        let new_size = size_of::<T>()
            .checked_mul(cap)
            .expect("memory size overflow");
        Layout::from_size_align(new_size, align_of::<T>()).unwrap()
    }
}
impl<T> Drop for RawGapBuffer<T> {
    fn drop(&mut self) {
        self.realloc(0)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Range, RangeMut
////////////////////////////////////////////////////////////////////////////////

/// Immutable sub-range of [`GapBuffer`]
///
/// This struct is created by [`Slice::range`].
#[derive(Hash)]
pub struct Range<'gb, T: 'gb> {
    s: Slice<T>,
    _phantom: PhantomData<&'gb [T]>,
}

/// Mutable sub-range of [`GapBuffer`].
///
/// This struct is created by [`Slice::range_mut`].
#[derive(Hash)]
pub struct RangeMut<'gb, T: 'gb> {
    s: Slice<T>,
    _phantom: PhantomData<&'gb mut [T]>,
}
impl<'gb, T: 'gb> Range<'gb, T> {
    #[inline]
    const unsafe fn new(s: Slice<T>) -> Self {
        Range {
            s,
            _phantom: PhantomData,
        }
    }

    /// Construct a new, empty `Range`.
    #[inline]
    pub const fn empty() -> Self {
        unsafe { Range::new(Slice::empty()) }
    }

    /// Returns a reference to an element at index or None if out of bounds.
    ///
    /// Unlike [`Slice::get`], return value not borrow `self`.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&'gb T> {
        unsafe { self.s.get_with_lifetime(index) }
    }

    /// Return a immutable sub-range of this Slice.
    ///
    /// Unlike [`Slice::range`], return value not borrow `self`.
    pub fn range(&self, range: impl RangeBounds<usize>) -> Range<'gb, T> {
        unsafe { self.range_with_lifetime(range) }
    }

    /// Returns a pair of slices.
    /// First slice is before gap. Second slice is after gap.
    ///
    /// Unlike [`Slice::as_slices`], return value not borrow `self`.
    pub fn as_slices(&self) -> (&'gb [T], &'gb [T]) {
        unsafe { self.as_slices_with_lifetime() }
    }
}
impl<'gb, T: 'gb> RangeMut<'gb, T> {
    #[inline]
    const unsafe fn new(s: Slice<T>) -> Self {
        RangeMut {
            s,
            _phantom: PhantomData,
        }
    }

    /// Construct a new, empty `RangeMut`.
    #[inline]
    pub const fn empty() -> Self {
        unsafe { RangeMut::new(Slice::empty()) }
    }
}

impl<T> Deref for Range<'_, T> {
    type Target = Slice<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.s
    }
}
impl<T> Deref for RangeMut<'_, T> {
    type Target = Slice<T>;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.s
    }
}

impl<T> DerefMut for RangeMut<'_, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.s
    }
}

impl<T> Clone for Range<'_, T> {
    fn clone(&self) -> Self {
        unsafe {
            Range::new(Slice {
                ptr: self.ptr,
                cap: self.cap,
                gap: self.gap,
                len: self.len,
            })
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Slice
////////////////////////////////////////////////////////////////////////////////

/// Sub-range of [`GapBuffer`].
/// `Slice` define common method for [`GapBuffer`], [`Range`], [`RangeMut`].
pub struct Slice<T> {
    ptr: NonNull<T>,
    cap: usize,
    gap: usize,
    len: usize,
}
impl<T> Slice<T> {
    /// Construct a new, empty `Slice`.
    pub const fn empty() -> Self {
        Slice {
            ptr: NonNull::dangling(),
            cap: 0,
            gap: 0,
            len: 0,
        }
    }

    /// Constructs a `Slice` from a [`Vec<T>`] at `O(1)`.
    const fn from_vec(mut vec: Vec<T>) -> Self {
        let slice = Slice {
            ptr: match NonNull::new(vec.as_mut_ptr()) {
                Some(non_null) => non_null,
                None => NonNull::dangling(),
            },
            cap: vec.capacity(),
            gap: vec.len(),
            len: vec.len(),
        };

        let _dont_drop = std::mem::ManuallyDrop::new(vec);

        slice
    }

    /// Returns the number of elements in the GapBuffer.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the GapBuffer contains no elements.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to an element at index or None if out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        unsafe { self.get_with_lifetime(index) }
    }
    #[inline]
    unsafe fn get_with_lifetime<'gb>(&self, index: usize) -> Option<&'gb T> {
        self.get_offset(index)
            .map(|o| unsafe { &*self.as_ptr().add(o) })
    }

    /// Returns a mutable reference to an element at index or None if out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.get_offset(index)
            .map(|o| unsafe { &mut *self.as_mut_ptr().add(o) })
    }

    #[inline]
    fn move_values(&mut self, gap: usize) {
        let gap_old = self.gap;
        let gap_len = self.gap_len();
        let (src, dest, count) = if gap < gap_old {
            (gap, gap + gap_len, gap_old - gap)
        } else {
            (gap_old + gap_len, gap_old, gap - gap_old)
        };
        let p = self.as_mut_ptr();
        unsafe {
            copy(p.add(src), p.add(dest), count);
        }
    }

    /// Swaps two elements in the GapBuffer.
    ///
    /// # Arguments
    ///
    /// * a - The index of the first element
    /// * b - The index of the second element
    ///
    /// # Panics
    /// Panics if `a >= self.len()` or `b >= self.len()`.
    #[inline]
    pub const fn swap(&mut self, a: usize, b: usize) {
        let oa = self.get_offset(a).expect("a is out of bounds.");
        let ob = self.get_offset(b).expect("b is out of bounds.");
        let p = self.as_mut_ptr();
        unsafe { ptr::swap(p.add(oa), p.add(ob)) }
    }

    /// Return a immutable sub-range of this Slice.
    ///
    /// # Panics
    /// Panics if `range` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let buf = gap_buffer![1, 2, 3, 4, 5];
    ///
    /// let r1 = buf.range(1..);
    /// assert_eq!(r1, [2, 3, 4, 5]);
    ///
    /// let r2 = r1.range(1..3);
    /// assert_eq!(r2, [3, 4]);
    /// ```
    pub fn range(&self, range: impl RangeBounds<usize>) -> Range<'_, T> {
        unsafe { self.range_with_lifetime(range) }
    }
    unsafe fn range_with_lifetime<'gb>(&self, range: impl RangeBounds<usize>) -> Range<'gb, T> {
        unsafe { Range::new(self.range_slice(range)) }
    }

    /// Return a mutable sub-range of this Slice.
    ///
    /// # Panics
    /// Panics if `range` is out of bounds.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4, 5];
    /// {
    ///     let mut r = buf.range_mut(1..);
    ///     assert_eq!(r, [2, 3, 4, 5]);
    ///     r[0] = 0;
    /// }
    /// assert_eq!(buf, [1, 0, 3, 4, 5]);
    /// ```
    pub fn range_mut(&mut self, range: impl RangeBounds<usize>) -> RangeMut<'_, T> {
        unsafe { RangeMut::new(self.range_slice(range)) }
    }
    unsafe fn range_slice(&self, range: impl RangeBounds<usize>) -> Slice<T> {
        let (idx, len) = self.to_idx_len(range);
        if len == 0 {
            return Slice::empty();
        }

        let gap_is_before = self.gap <= idx;
        let gap_is_after = idx + len <= self.gap;

        let gap = if gap_is_before {
            0
        } else if !gap_is_after {
            self.gap - idx
        } else {
            len
        };
        let begin = if gap_is_before { self.gap_len() } else { 0 } + idx;
        let end = if !gap_is_after { self.gap_len() } else { 0 } + idx + len;

        Slice {
            ptr: NonNull::new(unsafe { self.ptr.as_ptr().add(begin) }).unwrap(),
            cap: end - begin,
            gap,
            len,
        }
    }
    fn to_idx_len(&self, range: impl RangeBounds<usize>) -> (usize, usize) {
        use std::ops::Bound::*;
        const MAX: usize = usize::MAX;
        let len = self.len;
        let idx = match range.start_bound() {
            Included(&idx) => idx,
            Excluded(&MAX) => panic!("attempted to index slice up to maximum usize"),
            Excluded(&idx) => idx + 1,
            Unbounded => 0,
        };
        if idx > len {
            panic!("index {idx} out of range for slice of length {len}");
        }

        let end = match range.end_bound() {
            Included(&MAX) => panic!("attempted to index slice up to maximum usize"),
            Included(&idx) => idx + 1,
            Excluded(&idx) => idx,
            Unbounded => len,
        };
        if end > len {
            panic!("index {end} out of range for slice of length {len}");
        }

        if end < idx {
            panic!("slice index starts at {idx} but ends at {len}");
        }
        (idx, end - idx)
    }

    /// Returns a pair of slices.
    /// First slice is before gap. Second slice is after gap.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4, 5];
    /// buf.set_gap(2);
    /// let (s1, s2) = buf.as_slices();
    /// assert_eq!(s1, [1, 2]);
    /// assert_eq!(s2, [3, 4, 5]);
    /// ```
    pub fn as_slices(&self) -> (&[T], &[T]) {
        unsafe { self.as_slices_with_lifetime() }
    }
    const unsafe fn as_slices_with_lifetime<'gb>(&self) -> (&'gb [T], &'gb [T]) {
        let p0 = self.as_ptr();
        let c1 = self.len - self.gap;
        let p1 = unsafe { p0.add(self.cap - c1) };
        (unsafe { slice::from_raw_parts(p0, self.gap) }, unsafe {
            slice::from_raw_parts(p1, c1)
        })
    }

    /// Returns a pair of slices.
    /// First slice is before gap. Second slice is after gap.
    ///
    /// # Examples
    /// ```
    /// use gap_buf::gap_buffer;
    ///
    /// let mut buf = gap_buffer![1, 2, 3, 4, 5];
    /// buf.set_gap(2);
    /// {
    ///     let (mut s1, mut s2) = buf.as_mut_slices();
    ///     s1[0] = 10;
    ///     s2[0] = 11;
    /// }
    /// assert_eq!(buf, [10, 2, 11, 4, 5]);
    /// ```
    pub const fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        unsafe {
            let p0 = self.as_mut_ptr();
            let c1 = self.len - self.gap;
            let p1 = p0.add(self.cap - c1);
            (
                slice::from_raw_parts_mut(p0, self.gap),
                slice::from_raw_parts_mut(p1, c1),
            )
        }
    }

    /// Returns an iterator over the Slice.
    pub fn iter(&self) -> Iter<'_, T> {
        let (s0, s1) = self.as_slices();
        s0.iter().chain(s1.iter())
    }

    /// Returns an iterator that allows modifying each value.
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        let (s0, s1) = self.as_mut_slices();
        s0.iter_mut().chain(s1.iter_mut())
    }

    #[inline]
    const fn get_offset(&self, index: usize) -> Option<usize> {
        if index < self.gap {
            Some(index)
        } else if index < self.len {
            Some(index + self.gap_len())
        } else {
            None
        }
    }

    #[inline]
    const fn gap_len(&self) -> usize {
        self.cap - self.len
    }

    #[inline]
    const fn as_ptr(&self) -> *const T {
        self.ptr.as_ptr()
    }

    #[inline]
    const fn as_mut_ptr(&mut self) -> *mut T {
        self.ptr.as_ptr()
    }
}

impl<T: Clone> Clone for Slice<T> {
    fn clone(&self) -> Self {
        let vec = self.iter().cloned().collect();
        Self::from_vec(vec)
    }
}

unsafe impl<T: Sync> Sync for Slice<T> {}
unsafe impl<T: Send> Send for Slice<T> {}

#[cfg(feature = "bincode")]
impl<T: bincode::Decode<Context>, Context> bincode::Decode<Context> for Slice<T> {
    fn decode<D: bincode::de::Decoder<Context = Context>>(
        decoder: &mut D,
    ) -> Result<Self, bincode::error::DecodeError> {
        let vec: Vec<T> = bincode::Decode::decode(decoder)?;
        Ok(Self::from_vec(vec))
    }
}

#[cfg(feature = "bincode")]
impl<'de, T, Context> bincode::BorrowDecode<'de, Context> for Slice<T>
where
    T: bincode::BorrowDecode<'de, Context>,
{
    fn borrow_decode<D: bincode::de::BorrowDecoder<'de, Context = Context>>(
        decoder: &mut D,
    ) -> Result<Self, bincode::error::DecodeError> {
        let vec: Vec<T> = bincode::BorrowDecode::borrow_decode(decoder)?;
        Ok(Self::from_vec(vec))
    }
}

#[cfg(feature = "bincode")]
impl<T: bincode::Encode> bincode::Encode for Slice<T> {
    fn encode<E: bincode::enc::Encoder>(
        &self,
        encoder: &mut E,
    ) -> Result<(), bincode::error::EncodeError> {
        use bincode::enc::write::Writer;
        let (s0, s1) = self.as_slices();

        bincode::Encode::encode(&(self.len as u64), encoder)?;

        if unty::type_equal::<T, u8>() {
            // Safety: T = u8
            let s0: &[u8] = unsafe { core::mem::transmute(s0) };
            encoder.writer().write(s0)?;
            let s1: &[u8] = unsafe { core::mem::transmute(s1) };
            encoder.writer().write(s1)?;
        } else {
            for item in self {
                item.encode(encoder)?;
            }
        }

        Ok(())
    }
}

impl<T> From<Slice<T>> for Vec<T> {
    fn from(mut value: Slice<T>) -> Self {
        if value.gap != value.len {
            value.move_values(value.len);
        }
        let vec = unsafe { Self::from_raw_parts(value.ptr.as_ptr(), value.len, value.cap) };

        let _dont_drop = std::mem::ManuallyDrop::new(value);

        vec
    }
}

////////////////////////////////////////////////////////////////////////////////
// Default
////////////////////////////////////////////////////////////////////////////////

impl<T> Default for GapBuffer<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}
impl<T> Default for Range<'_, T> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}
impl<T> Default for RangeMut<'_, T> {
    #[inline]
    fn default() -> Self {
        Self::empty()
    }
}

////////////////////////////////////////////////////////////////////////////////
// Index, IndexMut
////////////////////////////////////////////////////////////////////////////////

impl<T> Index<usize> for GapBuffer<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.deref().index(index)
    }
}
impl<T> IndexMut<usize> for GapBuffer<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.deref_mut().index_mut(index)
    }
}

impl<T> Index<usize> for Range<'_, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.deref().index(index)
    }
}
impl<T> Index<usize> for RangeMut<'_, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.deref().index(index)
    }
}
impl<T> IndexMut<usize> for RangeMut<'_, T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.deref_mut().index_mut(index)
    }
}

impl<T> Index<usize> for Slice<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        self.get(index).expect("index out of bounds")
    }
}
impl<T> IndexMut<usize> for Slice<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        self.get_mut(index).expect("index out of bounds")
    }
}

////////////////////////////////////////////////////////////////////////////////
// Debug
////////////////////////////////////////////////////////////////////////////////

impl<T> Debug for GapBuffer<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.deref().fmt(f)
    }
}
impl<T> Debug for Range<'_, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.deref().fmt(f)
    }
}
impl<T> Debug for RangeMut<'_, T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        self.deref().fmt(f)
    }
}

impl<T> Debug for Slice<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        f.debug_list().entries(self).finish()
    }
}

impl<T: Hash> Hash for Slice<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for value in self {
            value.hash(state);
        }
    }
}

////////////////////////////////////////////////////////////////////////////////
// Eq, PartialEq
////////////////////////////////////////////////////////////////////////////////

impl<T, S> PartialEq<S> for GapBuffer<T>
where
    T: PartialEq,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn eq(&self, other: &S) -> bool {
        self.deref().eq(other)
    }
}
impl<T: Eq> Eq for GapBuffer<T> {}

impl<T, S> PartialEq<S> for Range<'_, T>
where
    T: PartialEq,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn eq(&self, other: &S) -> bool {
        self.deref().eq(other)
    }
}
impl<T: Eq> Eq for Range<'_, T> {}

impl<T, S> PartialEq<S> for RangeMut<'_, T>
where
    T: PartialEq,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn eq(&self, other: &S) -> bool {
        self.deref().eq(other)
    }
}
impl<T: Eq> Eq for RangeMut<'_, T> {}

impl<T, S> PartialEq<S> for Slice<T>
where
    T: PartialEq,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn eq(&self, other: &S) -> bool {
        self.iter().eq(other)
    }
}
impl<T: Eq> Eq for Slice<T> {}

////////////////////////////////////////////////////////////////////////////////
// Ord, PartialOrd
////////////////////////////////////////////////////////////////////////////////

impl<T, S> PartialOrd<S> for GapBuffer<T>
where
    T: PartialOrd,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn partial_cmp(&self, other: &S) -> Option<Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: Ord> Ord for GapBuffer<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other)
    }
}

impl<T, S> PartialOrd<S> for Range<'_, T>
where
    T: PartialOrd,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn partial_cmp(&self, other: &S) -> Option<Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: Ord> Ord for Range<'_, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other)
    }
}

impl<T, S> PartialOrd<S> for RangeMut<'_, T>
where
    T: PartialOrd,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn partial_cmp(&self, other: &S) -> Option<Ordering> {
        self.deref().partial_cmp(other)
    }
}

impl<T: Ord> Ord for RangeMut<'_, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.deref().cmp(other)
    }
}

impl<T, S> PartialOrd<S> for Slice<T>
where
    T: PartialOrd,
    S: ?Sized,
    for<'b> &'b S: IntoIterator<Item = &'b T>,
{
    fn partial_cmp(&self, other: &S) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for Slice<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

////////////////////////////////////////////////////////////////////////////////
// iterator
////////////////////////////////////////////////////////////////////////////////

/// Immutable GapBuffer iterator.
pub type Iter<'gb, T> = Chain<slice::Iter<'gb, T>, slice::Iter<'gb, T>>;

/// Mutable GapBuffer iterator.
pub type IterMut<'gb, T> = Chain<slice::IterMut<'gb, T>, slice::IterMut<'gb, T>>;

/// An iterator that moves out of a [`GapBuffer`].
pub struct IntoIter<T> {
    buf: GapBuffer<T>,
}
impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.buf.pop_front()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.buf.len();
        (len, Some(len))
    }
}
impl<T> ExactSizeIterator for IntoIter<T> {}
impl<T> FusedIterator for IntoIter<T> {}
impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.buf.pop_back()
    }
}

impl<T> IntoIterator for GapBuffer<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        IntoIter { buf: self }
    }
}

impl<'gb, T> IntoIterator for &'gb GapBuffer<T> {
    type Item = &'gb T;
    type IntoIter = Iter<'gb, T>;
    fn into_iter(self) -> Iter<'gb, T> {
        self.iter()
    }
}
impl<'gb, T> IntoIterator for &'gb Range<'_, T> {
    type Item = &'gb T;
    type IntoIter = Iter<'gb, T>;
    fn into_iter(self) -> Iter<'gb, T> {
        self.iter()
    }
}
impl<'gb, T> IntoIterator for &'gb RangeMut<'_, T> {
    type Item = &'gb T;
    type IntoIter = Iter<'gb, T>;
    fn into_iter(self) -> Iter<'gb, T> {
        self.iter()
    }
}

impl<'gb, T> IntoIterator for &'gb Slice<T> {
    type Item = &'gb T;
    type IntoIter = Iter<'gb, T>;
    fn into_iter(self) -> Iter<'gb, T> {
        self.iter()
    }
}

impl<'gb, T> IntoIterator for &'gb mut GapBuffer<T> {
    type Item = &'gb mut T;
    type IntoIter = IterMut<'gb, T>;
    fn into_iter(self) -> IterMut<'gb, T> {
        self.iter_mut()
    }
}

impl<'gb, T> IntoIterator for &'gb mut RangeMut<'gb, T> {
    type Item = &'gb mut T;
    type IntoIter = IterMut<'gb, T>;
    fn into_iter(self) -> IterMut<'gb, T> {
        self.iter_mut()
    }
}

impl<'gb, T> IntoIterator for &'gb mut Slice<T> {
    type Item = &'gb mut T;
    type IntoIter = IterMut<'gb, T>;
    fn into_iter(self) -> IterMut<'gb, T> {
        self.iter_mut()
    }
}

/// A draining iterator for [`GapBuffer`].
///
/// This struct is created by [`GapBuffer::drain`].
pub struct Drain<'gb, T: 'gb> {
    buf: &'gb mut GapBuffer<T>,
    idx: usize,
    len: usize,
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            Some(self.buf.remove(self.idx))
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        let len = self.len;
        self.nth(len);
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {}
impl<T> FusedIterator for Drain<'_, T> {}

/// An iterator that conditionally extracts from a [`GapBuffer`].
///
/// this struct is created by [`GapBuffer::extract_if`].
#[must_use]
pub struct ExtractIf<'gb, T: 'gb, F> {
    buf: &'gb mut GapBuffer<T>,
    idx: usize,
    end: usize,
    pred: F,
}

impl<T, F> Iterator for ExtractIf<'_, T, F>
where
    F: FnMut(&mut T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        while self.idx < self.end {
            if (self.pred)(self.buf.get_mut(self.idx).unwrap()) {
                self.end -= 1;
                return Some(self.buf.remove(self.idx));
            } else {
                self.idx += 1;
            }
        }

        None
    }
}

impl<T, F> FusedIterator for ExtractIf<'_, T, F> where F: FnMut(&mut T) -> bool {}
