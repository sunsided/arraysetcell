use crate::error::CapacityError;
use default_option_arr::none_cell_arr;
use std::cell::Cell;
use std::fmt::{Debug, Formatter};
use std::mem::MaybeUninit;

/// `ArraySetCell` is a fixed-capacity, vector-like array with interior mutability
/// and no ordering guarantees.
pub struct ArraySetCell<T, const CAP: usize> {
    /// The underlying array.
    pub(crate) data: [Cell<Option<T>>; CAP],

    // TODO: Allow dynamic calculation of length.
    len: Cell<usize>,
}

impl<T, const CAP: usize> ArraySetCell<T, CAP> {
    /// The capacity of the `ArraySetCell`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// assert_eq!(ArraySetCell::<u8, 16>::CAPACITY, 16);
    /// ```
    pub const CAPACITY: usize = CAP;

    /// Create a new empty `ArraySetCell`.
    ///
    /// The maximum capacity is given by the generic parameter `CAP`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 16>::new();
    /// array.push(1);
    /// array.push(2);
    /// assert_eq!(array.capacity(), 16);
    /// assert_eq!(array.into_vec(), &[1, 2]);
    /// ```
    pub fn new() -> Self {
        Self {
            data: none_cell_arr![T; CAP],
            len: Cell::new(0),
        }
    }

    /// Return the number of elements in the `ArraySetCell`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::from([1, 2, 3]);
    /// array.pop();
    /// assert_eq!(array.len(), 2);
    /// ```
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len.get()
    }

    /// Returns whether the `ArraySetCell` is empty.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::from([1]);
    /// array.pop();
    /// assert_eq!(array.is_empty(), true);
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Return the capacity of the `ArraySetCell`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::from([1, 2, 3]);
    /// assert_eq!(array.capacity(), 3);
    /// ```
    #[inline(always)]
    pub const fn capacity(&self) -> usize {
        Self::CAPACITY
    }

    /// Return true if the `ArraySetCell` is completely filled to its capacity, false otherwise.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 1>::new();
    /// assert!(!array.is_full());
    /// array.push(1);
    /// assert!(array.is_full());
    /// ```
    pub fn is_full(&self) -> bool {
        self.len() == self.capacity()
    }

    /// Returns the capacity left in the `ArraySetCell`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::from([1, 2, 3]);
    /// array.pop();
    /// assert_eq!(array.remaining_capacity(), 1);
    /// ```
    pub fn remaining_capacity(&self) -> usize {
        self.capacity() - self.len()
    }

    /// Push `element` into the set.
    ///
    /// The order of insertions is not guaranteed, i.e. the last item pushed
    /// may not be the first item popped.
    ///
    /// ## Panics
    ///
    /// Panic if the vector is already full. If you need to avoid panics, use
    /// [`try_push`](ArraySetCell::try_push) instead.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 2>::new();
    ///
    /// array.push(1);
    /// array.push(2);
    ///
    /// assert_eq!(array.into_vec(), &[1, 2]);
    /// ```
    pub fn push(&mut self, element: T) {
        self.try_push(element).expect("Push failed")
    }

    /// Push `element` into the set.
    ///
    /// The order of insertions is not guaranteed, i.e. the last item pushed
    /// may not be the first item popped.
    ///
    /// Unlike [`ArraySetCell::push`], this method does not panic.
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 2>::new();
    /// let push1 = array.try_push(1);
    /// let push2 = array.try_push(2);
    /// let push3 = array.try_push(3); // overflow
    ///
    /// assert!(push1.is_ok());
    /// assert!(push2.is_ok());
    /// assert!(push3.is_err());
    ///
    /// assert_eq!(array.into_vec(), &[1, 2]);
    /// ```
    pub fn try_push(&mut self, element: T) -> Result<(), CapacityError<T>> {
        if self.len() < CAP {
            unsafe {
                self.push_unchecked(element);
            }
            Ok(())
        } else {
            Err(CapacityError::new(element))
        }
    }

    /// Remove all elements in the vector.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// assert_eq!(array.len(), 2);
    ///
    /// array.clear();
    /// assert!(array.is_empty());
    /// assert_eq!(array.len(), 0);
    ///
    /// let vec = array.into_vec();
    /// assert_eq!(vec, &[]);
    /// ```
    pub fn clear(&self) {
        for item in self.data.iter() {
            item.replace(None);
        }
        self.len.set(0);
    }

    /// Remove the last element in the vector and return it.
    ///
    /// Return `Some(` *element* `)` if the vector is non-empty, else `None`.
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 2>::new();
    ///
    /// array.push(1);
    ///
    /// assert_eq!(array.pop(), Some(1));
    /// assert_eq!(array.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        let len = self.len();
        if len == 0 {
            return None;
        }

        // TODO: Optimize
        for item in self.data.iter().rev() {
            if unsafe { &*item.as_ptr() }.is_none() {
                continue;
            }

            let item = item.replace(None);
            debug_assert!(item.is_some());
            self.len.set(len - 1);
            return item;
        }

        None
    }

    /// Converts the `ArraySetCell` into a `Vec<T>`.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// let vec = array.into_vec();
    ///
    /// assert_eq!(vec, &[1, 3]);
    /// assert_eq!(vec.capacity(), 2);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.into()
    }

    /// Filters elements in the list, returning either `Some(result)` or `None` to continue
    /// searching. The element may be mutated in place.
    ///
    /// ## Arguments
    ///
    /// * `f` - The filter function. May mutate the result; return `Some(result)` to terminate the search.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// let result = array.filter_mut(|x| if *x > 2 { Some(*x) } else { None });
    ///
    /// assert_eq!(result, Some(3));
    /// ```
    pub fn filter_mut<F, O>(&mut self, mut f: F) -> Option<O>
    where
        F: FnMut(&mut T) -> Option<O>,
    {
        let mut index = 0;
        let mut yielded = 0;
        while index < CAP && yielded < self.len.get() {
            let reference = self.data[index].get_mut().as_mut();
            match reference {
                None => {
                    index += 1;
                    continue;
                }
                Some(item) => {
                    index += 1;
                    yielded += 1;
                    match f(item) {
                        None => continue,
                        Some(result) => return Some(result),
                    }
                }
            }
        }

        None
    }

    /// Return a raw pointer to the set's buffer.
    pub fn as_ptr(&self) -> *const Option<T> {
        self.data.as_ptr() as _
    }

    /// Return a raw mutable pointer to the set's buffer.
    pub fn as_mut_ptr(&mut self) -> *mut Option<T> {
        self.data.as_mut_ptr() as _
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20]);
    /// array.retain(|x| *x & 1 != 0 );
    /// assert_eq!(array.into_vec(), &[1, 3, 11]);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T) -> bool,
    {
        // Check the implementation of
        // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.retain
        // for safety arguments (especially regarding panics in f and when
        // dropping elements). Implementation closely mirrored here.

        let original_len = self.len();
        self.len.set(0);

        struct BackshiftOnDrop<'a, T, const CAP: usize> {
            set: &'a mut ArraySetCell<T, CAP>,
            processed_len: usize,
            deleted_cnt: usize,
            original_len: usize,
        }

        impl<T, const CAP: usize> Drop for BackshiftOnDrop<'_, T, CAP> {
            fn drop(&mut self) {
                let missing = self.original_len - self.processed_len;
                if missing > 0 && self.deleted_cnt > 0 {
                    for i in (self.processed_len - self.deleted_cnt + 1)..self.original_len {
                        let right = self.set.data[i].take();
                        self.set.data[i - 1].set(right);
                    }
                }
                self.set.len.set(self.original_len - self.deleted_cnt);
            }
        }

        let mut g = BackshiftOnDrop {
            set: self,
            processed_len: 0,
            deleted_cnt: 0,
            original_len,
        };

        #[inline(always)]
        fn process_one<F: FnMut(&mut T) -> bool, T, const CAP: usize, const DELETED: bool>(
            f: &mut F,
            g: &mut BackshiftOnDrop<'_, T, CAP>,
        ) -> bool {
            let cur = unsafe { g.set.as_mut_ptr().add(g.processed_len) };
            match unsafe { &mut *cur } {
                None => {
                    // We use the same method to clean up holes in the set.
                    g.processed_len += 1;
                    g.deleted_cnt += 1;
                    return false;
                }
                Some(item) => {
                    if !f(item) {
                        g.processed_len += 1;
                        g.deleted_cnt += 1;
                        unsafe {
                            cur.replace(None);
                        };
                        return false;
                    }
                }
            }

            if DELETED {
                unsafe {
                    // Overwrite the previously dropped element with the current one.
                    let hole_slot = g.set.as_mut_ptr().add(g.processed_len - g.deleted_cnt);
                    let value = cur.replace(None);
                    hole_slot.replace(value);
                }
            }
            g.processed_len += 1;
            true
        }

        // Stage 1: Nothing was deleted. (Skip all leading retained elements.)
        while g.processed_len != original_len {
            if !process_one::<F, T, CAP, false>(&mut f, &mut g) {
                break;
            }
        }

        // Stage 2: Some elements were deleted.
        while g.processed_len != original_len {
            process_one::<F, T, CAP, true>(&mut f, &mut g);
        }

        drop(g);
    }

    unsafe fn push_unchecked(&mut self, element: T) {
        let len = self.len();
        debug_assert!(len < CAP);

        // The slot at "len" should be empty.
        if unsafe { &*self.data[len].as_ptr() }.is_none() {
            self.data[len].set(Some(element));
        } else {
            // Scan for the first free element.
            for i in 0..CAP {
                if unsafe { &*self.data[i].as_ptr() }.is_some() {
                    continue;
                }

                self.data[i].set(Some(element));
                break;
            }
        }

        self.len.set(len + 1);
    }
}

impl<T, const CAP: usize> From<[T; CAP]> for ArraySetCell<T, CAP> {
    /// Constructs an `ArraySetCell` from an array of `T`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::from([1, 2, 3]);
    /// assert_eq!(array.len(), 3);
    /// ```
    fn from(value: [T; CAP]) -> Self {
        let mut uninit_data: MaybeUninit<[Cell<Option<T>>; CAP]> = MaybeUninit::uninit();
        let mut ptr = uninit_data.as_mut_ptr() as *mut Cell<Option<T>>;
        for item in value.into_iter() {
            unsafe {
                ptr.write(Cell::new(Some(item)));
                ptr = ptr.add(1);
            }
        }
        let data = unsafe { uninit_data.assume_init() };

        Self {
            data,
            len: Cell::new(CAP),
        }
    }
}

impl<T, const CAP: usize> From<[Option<T>; CAP]> for ArraySetCell<T, CAP> {
    /// Constructs an `ArraySetCell` from an array of `Option<T>`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// assert_eq!(array.len(), 2);
    /// ```
    fn from(value: [Option<T>; CAP]) -> Self {
        let mut uninit_data: MaybeUninit<[Cell<Option<T>>; CAP]> = MaybeUninit::uninit();
        let mut ptr = uninit_data.as_mut_ptr() as *mut Cell<Option<T>>;
        let mut len = 0;

        // Fill non-None items to the beginning.
        for item in value.into_iter() {
            match item {
                None => {}
                Some(item) => {
                    len += 1;
                    unsafe {
                        ptr.write(Cell::new(Some(item)));
                        ptr = ptr.add(1);
                    }
                }
            }
        }

        // Fill remaining spots with None.
        for _ in len..CAP {
            unsafe {
                ptr.write(Cell::new(None));
                ptr = ptr.add(1);
            }
        }

        let data = unsafe { uninit_data.assume_init() };

        Self {
            data,
            len: Cell::new(len),
        }
    }
}

impl<T, const CAP: usize> From<[Cell<Option<T>>; CAP]> for ArraySetCell<T, CAP> {
    /// Constructs an `ArraySetCell` from an array of `Cell<Option<T>>`.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::<u32, 3>::from([
    ///     Cell::new(Some(1)),
    ///     Cell::new(None),
    ///     Cell::new(Some(3))
    /// ]);
    /// assert_eq!(array.len(), 2);
    /// ```
    fn from(value: [Cell<Option<T>>; CAP]) -> Self {
        let len = value
            .iter()
            .map(|item| {
                // SAFETY: Since the array is full, the pointer is not null and can be dereferenced.
                if unsafe { &*item.as_ptr() }.is_some() {
                    1
                } else {
                    0
                }
            })
            .sum();
        Self {
            data: value,
            len: Cell::new(len),
        }
    }
}

impl<T, const CAP: usize> From<ArraySetCell<T, CAP>> for [Option<T>; CAP] {
    /// Converts an `ArraySetCell` into an `[Option<T>; N]`.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::from([Some(1), None, Some(3)]);
    /// let into: [Option<u32>; 3] = array.into();
    ///
    /// assert_eq!(into, [Some(1), Some(3), None]);
    /// ```
    fn from(value: ArraySetCell<T, CAP>) -> Self {
        let mut uninit_data: MaybeUninit<[Option<T>; CAP]> = MaybeUninit::uninit();
        let mut ptr = uninit_data.as_mut_ptr() as *mut Option<T>;
        for item in value.data.into_iter() {
            unsafe {
                ptr.write(item.take());
                ptr = ptr.add(1);
            }
        }
        unsafe { uninit_data.assume_init() }
    }
}

impl<T, const CAP: usize> From<ArraySetCell<T, CAP>> for [Cell<Option<T>>; CAP] {
    /// Converts an `ArraySetCell` into an `[Cell<Option<T>>; N]`.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::from([Some(1), None, Some(3)]);
    /// let into: [Cell<Option<u32>>; 3] = array.into();
    ///
    /// assert_eq!(into, [Cell::new(Some(1)), Cell::new(Some(3)), Cell::new(None)]);
    /// ```
    fn from(value: ArraySetCell<T, CAP>) -> Self {
        value.data
    }
}

impl<T, const CAP: usize> From<ArraySetCell<T, CAP>> for Vec<Option<T>> {
    /// Converts an `ArraySetCell` into a `Vec<Option<T>>`.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// let vec: Vec<Option<u32>> = array.into();
    ///
    /// assert_eq!(vec, &[Some(1), Some(3), None]);
    /// assert_eq!(vec.capacity(), 3);
    /// ```
    fn from(value: ArraySetCell<T, CAP>) -> Self {
        let mut out = Vec::with_capacity(value.capacity());
        for item in value.data.into_iter() {
            out.push(item.replace(None));
        }
        out
    }
}

impl<T, const CAP: usize> From<ArraySetCell<T, CAP>> for Vec<T> {
    /// Converts an `ArraySetCell` into a `Vec<T>`.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// let vec: Vec<u32> = array.into();
    ///
    /// assert_eq!(vec, &[1, 3]);
    /// assert_eq!(vec.capacity(), 2);
    /// ```
    fn from(value: ArraySetCell<T, CAP>) -> Self {
        let mut out = Vec::with_capacity(value.len());
        let expected = value.len();
        for item in value.data.into_iter() {
            match item.replace(None) {
                None => continue,
                Some(item) => out.push(item),
            }
            if out.len() == expected {
                break;
            }
        }
        out
    }
}

impl<T, const CAP: usize> IntoIterator for ArraySetCell<T, CAP> {
    type Item = T;
    type IntoIter = ArraySetCellIntoIter<T, CAP>;

    /// Returns an iterator.
    ///
    /// ## Example
    ///
    /// ```
    /// use std::cell::Cell;
    /// use arraysetcell::ArraySetCell;
    ///
    /// let array = ArraySetCell::<u32, 3>::from([Some(1), None, Some(3)]);
    /// let mut iter = array.into_iter();
    ///
    /// assert_eq!(iter.size_hint(), (2, Some(2)));
    /// assert_eq!(iter.next(), Some(1));
    /// assert_eq!(iter.next(), Some(3));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        ArraySetCellIntoIter {
            set: self,
            index: 0,
            yielded: 0,
        }
    }
}

pub struct ArraySetCellIntoIter<T, const CAP: usize> {
    set: ArraySetCell<T, CAP>,
    index: usize,
    yielded: usize,
}

impl<T, const CAP: usize> Iterator for ArraySetCellIntoIter<T, CAP> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut index = self.index;
        while index < CAP && self.yielded < self.set.len() {
            match self.set.data[index].replace(None) {
                None => {
                    index += 1;
                }
                Some(item) => {
                    self.index = index + 1;
                    self.yielded += 1;
                    return Some(item);
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.set.len();
        (len, Some(len))
    }
}

impl<T, const CAP: usize> Default for ArraySetCell<T, CAP> {
    /// Create a new empty `ArraySetCell`.
    ///
    /// The maximum capacity is given by the generic parameter `CAP`.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 16>::default();
    /// array.push(1);
    /// array.push(2);
    /// assert_eq!(array.capacity(), 16);
    /// assert_eq!(array.into_vec(), &[1, 2]);
    /// ```
    fn default() -> Self {
        ArraySetCell::new()
    }
}

impl<T, const CAP: usize> Debug for ArraySetCell<T, CAP> {
    /// Creates a debug string representation of the array.
    ///
    /// ## Example
    ///
    /// ```
    /// use arraysetcell::ArraySetCell;
    ///
    /// let mut array = ArraySetCell::<_, 16>::default();
    /// array.push(1);
    /// array.push(2);
    /// assert_eq!(format!("{:?}", array), "len=2 cap=16");
    /// ```
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "len={} cap={}", self.len.get(), CAP)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new() {
        let array: ArraySetCell<u8, 16> = ArraySetCell::new();
        assert_eq!(array.len(), 0);
        assert!(array.is_empty());
        assert!(!array.is_full());
        assert_eq!(array.capacity(), 16);
        assert_eq!(array.remaining_capacity(), 16);
        assert_eq!(array.into_vec(), &[]);
    }

    #[test]
    fn test_push_pop() {
        let mut array: ArraySetCell<u8, 2> = ArraySetCell::new();
        assert_eq!(array.len(), 0);
        assert!(array.is_empty());
        assert!(!array.is_full());
        assert_eq!(array.capacity(), 2);
        assert_eq!(array.remaining_capacity(), 2);

        array.push(1);
        assert!(array.try_push(2).is_ok());
        assert!(array.try_push(3).is_err());

        assert_eq!(array.pop(), Some(2));
        array.push(3);

        assert_eq!(array.into_vec(), &[1, 3]);
    }

    #[test]
    fn clear() {
        let array = ArraySetCell::from([1, 2, 3, 4, 11, 20]);
        assert_eq!(array.len(), 6);
        assert!(!array.is_empty());
        assert!(array.is_full());

        array.clear();
        assert_eq!(array.len(), 0);
        assert!(array.is_empty());
        assert!(!array.is_full());
        assert_eq!(array.into_vec(), &[]);
    }

    #[test]
    fn retain_odd() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20]);
        assert_eq!(array.len(), 6);
        assert!(!array.is_empty());
        assert!(array.is_full());

        array.retain(|x| *x & 1 != 0);
        assert_eq!(array.len(), 3);
        assert!(!array.is_empty());
        assert!(!array.is_full());
        assert_eq!(array.into_vec(), &[1, 3, 11]);
    }

    #[test]
    fn retain_even() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20, 22]);
        array.retain(|x| *x & 1 == 0);
        assert_eq!(array.len(), 4);
        assert_eq!(array.into_vec(), &[2, 4, 20, 22]);
    }

    #[test]
    fn retain_all_but_first() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20, 22]);
        array.retain(|x| *x != 1);
        assert_eq!(array.len(), 6);
        assert_eq!(array.into_vec(), &[2, 3, 4, 11, 20, 22]);
    }

    #[test]
    fn retain_all_but_last() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20, 22]);
        array.retain(|x| *x != 22);
        assert_eq!(array.len(), 6);
        assert_eq!(array.into_vec(), &[1, 2, 3, 4, 11, 20]);
    }

    #[test]
    fn retain_all_but_second_to_last() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20, 22]);
        array.retain(|x| *x != 20);
        assert_eq!(array.len(), 6);
        assert_eq!(array.into_vec(), &[1, 2, 3, 4, 11, 22]);
    }

    #[test]
    fn retain_all() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20, 22]);
        array.retain(|_| true);
        assert_eq!(array.len(), 7);
        assert_eq!(array.into_vec(), &[1, 2, 3, 4, 11, 20, 22]);
    }

    #[test]
    fn retain_none() {
        let mut array = ArraySetCell::from([1, 2, 3, 4, 11, 20, 22]);
        array.retain(|_| false);
        assert_eq!(array.len(), 0);
        assert_eq!(array.into_vec(), &[]);
    }

    #[test]
    #[allow(static_mut_refs)]
    fn retain_does_not_drop_multiple_times() {
        static mut ORIGINAL_DISPOSED: usize = 0;
        static mut REFERENCE_DISPOSED: usize = 0;

        unsafe {
            ORIGINAL_DISPOSED = 0;
            REFERENCE_DISPOSED = 0;
        }

        #[derive(Debug, Clone)]
        struct Test(usize, bool);

        impl Drop for Test {
            fn drop(&mut self) {
                if self.1 {
                    unsafe {
                        ORIGINAL_DISPOSED += 1;
                    }
                } else {
                    unsafe {
                        REFERENCE_DISPOSED += 1;
                    }
                }
            }
        }

        impl Test {
            pub fn new(value: usize) -> Box<Self> {
                Box::new(Self(value, true))
            }

            pub fn new_cmp(value: usize) -> Box<Self> {
                Box::new(Self(value, false))
            }
        }

        impl PartialEq for Test {
            fn eq(&self, other: &Self) -> bool {
                self.0.eq(&other.0)
            }
        }

        let mut array = ArraySetCell::from([
            Test::new(1), // will be dropped
            Test::new(2),
            Test::new(3), // will be dropped
            Test::new(4),
            Test::new(11), // will be dropped
            Test::new(20),
            Test::new(22),
        ]);
        array.retain(|x| x.0 & 1 == 0);

        unsafe {
            assert_eq!(ORIGINAL_DISPOSED, 3);
            assert_eq!(REFERENCE_DISPOSED, 0);
        }

        assert_eq!(array.len(), 4);
        assert_eq!(
            array.into_vec(),
            &[
                Test::new_cmp(2),
                Test::new_cmp(4),
                Test::new_cmp(20),
                Test::new_cmp(22)
            ]
        );

        unsafe {
            assert_eq!(ORIGINAL_DISPOSED, 7);
            assert_eq!(REFERENCE_DISPOSED, 4);
        }
    }
}
