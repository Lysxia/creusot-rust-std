//! Indexing implementations for `[T]`.

use crate::panic::const_panic;
// use core::ub_checks::assert_unsafe_precondition;
// use core::{ops, range};
use crate::assert_unsafe_precondition;
use crate::intrinsics::{
    slice_get_unchecked_mut, slice_get_unchecked_raw, slice_get_unchecked_raw_mut,
    slice_get_unchecked_ref,
};
use crate::ops;
#[cfg(creusot)]
use core::ops::Bound;
#[cfg(creusot)]
use creusot_contracts::std::ptr::metadata_logic;
use creusot_contracts::{ghost::PtrOwn, std::ops::RangeBounds, *};

// #[stable(feature = "rust1", since = "1.0.0")]
impl<T, I> ops::Index<I> for [T]
where
    I: SliceIndex<[T]>,
{
    type Output = I::Output;

    #[inline(always)]
    #[requires(index.in_bounds(*self))]
    #[ensures(index.slice_index(*self, *result))]
    fn index(&self, index: I) -> &I::Output {
        index.index(self)
    }
}

// #[stable(feature = "rust1", since = "1.0.0")]
impl<T, I> ops::IndexMut<I> for [T]
where
    I: SliceIndex<[T]>,
{
    #[inline(always)]
    #[requires(index.in_bounds(*self))]
    #[ensures(index.slice_index(*self, *result))]
    #[ensures(index.slice_index(^self, ^result))]
    #[ensures(index.resolve_elsewhere(*self, ^self))]
    fn index_mut(&mut self, index: I) -> &mut I::Output {
        index.index_mut(self)
    }
}

// #[cfg_attr(not(feature = "panic_immediate_abort"), inline(never), cold)]
// #[cfg_attr(feature = "panic_immediate_abort", inline)]
#[track_caller]
#[check(ghost)]
#[erasure(private core::slice::index::slice_index_fail)]
#[requires(false)]
const fn slice_index_fail(start: usize, end: usize, len: usize) -> ! {
    if start > len {
        const_panic!(
            "slice start index is out of range for slice",
            "range start index {start} out of range for slice of length {len}",
            start: usize,
            len: usize,
        )
    }

    if end > len {
        const_panic!(
            "slice end index is out of range for slice",
            "range end index {end} out of range for slice of length {len}",
            end: usize,
            len: usize,
        )
    }

    if start > end {
        const_panic!(
            "slice index start is larger than end",
            "slice index starts at {start} but ends at {end}",
            start: usize,
            end: usize,
        )
    }

    // Only reachable if the range was a `RangeInclusive` or a
    // `RangeToInclusive`, with `end == len`.
    const_panic!(
        "slice end index is out of range for slice",
        "range end index {end} out of range for slice of length {len}",
        end: usize,
        len: usize,
    )
}

// The UbChecks are great for catching bugs in the unsafe methods, but including
// them in safe indexing is unnecessary and hurts inlining and debug runtime perf.
// Both the safe and unsafe public methods share these helpers,
// which use intrinsics directly to get *no* extra checks.

#[inline(always)]
#[erasure(private core::slice::index::get_offset_len_noubcheck)]
#[requires(own.ptr() == ptr)]
#[requires(offset@ + len@ <= own.len())]
#[ensures(result as *const T == (ptr as *const T).offset_logic(offset@))]
#[ensures(result.len_logic() == len@)]
unsafe fn get_offset_len_noubcheck<T>(
    ptr: *const [T],
    offset: usize,
    len: usize,
    own: Ghost<&PtrOwn<[T]>>,
) -> *const [T] {
    let ptr = ptr as *const T;
    // SAFETY: The caller already checked these preconditions
    let ptr = unsafe { crate::intrinsics::offset_own(ptr, offset, own) };
    aggregate_raw_ptr_slice(ptr, len)
}

#[inline(always)]
#[erasure(private core::slice::index::get_offset_len_mut_noubcheck)]
#[requires(own.ptr() == ptr as *const [T])]
#[requires(offset@ + len@ <= own.len())]
#[ensures(result as *const T == (ptr as *const T).offset_logic(offset@))]
#[ensures(result.len_logic() == len@)]
unsafe fn get_offset_len_mut_noubcheck<T>(
    ptr: *mut [T],
    offset: usize,
    len: usize,
    own: Ghost<&PtrOwn<[T]>>,
) -> *mut [T] {
    let ptr = ptr as *mut T;
    // SAFETY: The caller already checked these preconditions
    let ptr = unsafe { crate::intrinsics::offset_own_mut(ptr, offset, own) };
    aggregate_raw_ptr_mut_slice(ptr, len)
}

#[trusted]
#[erasure(core::intrinsics::aggregate_raw_ptr::<*const [T], *const T, usize>)]
#[ensures(result as *const T == ptr && metadata_logic(result) == len)]
fn aggregate_raw_ptr_slice<T>(ptr: *const T, len: usize) -> *const [T] {
    core::intrinsics::aggregate_raw_ptr(ptr, len)
}

#[trusted]
#[erasure(core::intrinsics::aggregate_raw_ptr::<*mut [T], *mut T, usize>)]
#[ensures(result as *mut T == ptr && metadata_logic(result) == len)]
fn aggregate_raw_ptr_mut_slice<T>(ptr: *mut T, len: usize) -> *mut [T] {
    core::intrinsics::aggregate_raw_ptr(ptr, len)
}

mod private_slice_index {
    use core::{ops, range};

    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    pub trait Sealed {}

    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for usize {}
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::Range<usize> {}
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeTo<usize> {}
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeFrom<usize> {}
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeFull {}
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeInclusive<usize> {}
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    impl Sealed for ops::RangeToInclusive<usize> {}
    // #[stable(feature = "slice_index_with_ops_bound_pair", since = "1.53.0")]
    impl Sealed for (ops::Bound<usize>, ops::Bound<usize>) {}

    // #[unstable(feature = "new_range_api", issue = "125687")]
    impl Sealed for range::Range<usize> {}
    // #[unstable(feature = "new_range_api", issue = "125687")]
    impl Sealed for range::RangeInclusive<usize> {}
    // #[unstable(feature = "new_range_api", issue = "125687")]
    impl Sealed for range::RangeFrom<usize> {}
    // impl Sealed for ops::IndexRange {}
}

/// A helper trait used for indexing operations.
///
/// Implementations of this trait have to promise that if the argument
/// to `get_unchecked(_mut)` is a safe reference, then so is the result.
// #[stable(feature = "slice_get_slice", since = "1.28.0")]
// #[rustc_diagnostic_item = "SliceIndex"]
// #[rustc_on_unimplemented(
//     on(T = "str", label = "string indices are ranges of `usize`",),
//     on(
//         all(any(T = "str", T = "&str", T = "alloc::string::String"), _Self = "{integer}"),
//         note = "you can use `.chars().nth()` or `.bytes().nth()`\n\
//                 for more information, see chapter 8 in The Book: \
//                 <https://doc.rust-lang.org/book/ch08-02-strings.html#indexing-into-strings>"
//     ),
//     message = "the type `{T}` cannot be indexed by `{Self}`",
//     label = "slice indices are of type `usize` or ranges of `usize`"
// )]
pub unsafe trait SliceIndex<T: ?Sized>: private_slice_index::Sealed {
    /// The output type returned by methods.
    // #[stable(feature = "slice_get_slice", since = "1.28.0")]
    type Output: ?Sized;

    #[logic]
    fn in_bounds(self, slice: T) -> bool;

    #[logic]
    fn slice_index(self, slice: T, output: Self::Output) -> bool;

    #[logic]
    fn resolve_elsewhere(self, old: T, fin: T) -> bool;

    /// Returns a shared reference to the output at this location, if in
    /// bounds.
    // #[unstable(feature = "slice_index_methods", issue = "none")]
    #[ensures(match result {
        None => !self.in_bounds(*slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result),
    })]
    fn get(self, slice: &T) -> Option<&Self::Output>;

    /// Returns a mutable reference to the output at this location, if in
    /// bounds.
    // #[unstable(feature = "slice_index_methods", issue = "none")]
    #[ensures(match result {
        None => !self.in_bounds(*slice) && resolve(slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result) && self.slice_index(^slice, ^result) && self.resolve_elsewhere(*slice, ^slice),
    })]
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;

    /// Returns a pointer to the output at this location, without
    /// performing any bounds checking.
    ///
    /// Calling this method with an out-of-bounds index or a dangling `slice` pointer
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    // #[unstable(feature = "slice_index_methods", issue = "none")]
    #[requires(own.ptr() == slice)]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    unsafe fn get_unchecked_own(
        self,
        slice: *const T,
        own: Ghost<&PtrOwn<T>>,
    ) -> (*const Self::Output, Ghost<&PtrOwn<Self::Output>>);

    /// Returns a mutable pointer to the output at this location, without
    /// performing any bounds checking.
    ///
    /// Calling this method with an out-of-bounds index or a dangling `slice` pointer
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    // #[unstable(feature = "slice_index_methods", issue = "none")]
    #[requires(own.ptr() == slice as *const T)]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 as *const Self::Output == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    #[ensures(self.slice_index(*(^own.inner_logic()).val(), *(^result.1.inner_logic()).val()))]
    #[ensures(self.resolve_elsewhere(*own.val(), *(^own.inner_logic()).val()))]
    unsafe fn get_unchecked_mut_own(
        self,
        slice: *mut T,
        own: Ghost<&mut PtrOwn<T>>,
    ) -> (*mut Self::Output, Ghost<&mut PtrOwn<Self::Output>>);

    /// Returns a shared reference to the output at this location, panicking
    /// if out of bounds.
    // #[unstable(feature = "slice_index_methods", issue = "none")]
    #[track_caller]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    fn index(self, slice: &T) -> &Self::Output;

    /// Returns a mutable reference to the output at this location, panicking
    /// if out of bounds.
    // #[unstable(feature = "slice_index_methods", issue = "none")]
    #[track_caller]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    #[ensures(self.slice_index(^slice, ^result))]
    #[ensures(self.resolve_elsewhere(*slice, ^slice))]
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
}

/// The methods `index` and `index_mut` panic if the index is out of bounds.
// #[stable(feature = "slice_get_slice_impls", since = "1.15.0")]
unsafe impl<T> SliceIndex<[T]> for usize {
    type Output = T;

    #[logic]
    fn in_bounds(self, slice: [T]) -> bool {
        pearlite! { self@ < slice@.len() }
    }

    #[logic]
    fn slice_index(self, slice: [T], res: T) -> bool {
        pearlite! { res == slice@[self@] }
    }

    #[logic]
    fn resolve_elsewhere(self, old: [T], fin: [T]) -> bool {
        pearlite! { forall<i: Int> i != self@ ==> old@.get(i) == fin@.get(i) }
    }

    #[inline]
    #[erasure(<usize as core::slice::SliceIndex<[T]>>::get)]
    #[ensures(match result {
        None => slice@.len() <= self@,
        Some(item) => self@ < slice@.len() && *item == slice@[self@],
    })]
    fn get(self, slice: &[T]) -> Option<&T> {
        // SAFETY: `self` is checked to be in bounds.
        if self < slice.len() {
            unsafe { Some(&*slice_get_unchecked_ref(slice, self)) }
        } else {
            None
        }
    }

    #[inline]
    #[erasure(<usize as core::slice::SliceIndex<[T]>>::get_mut)]
    #[ensures(match result {
        None => !self.in_bounds(*slice) && resolve(slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result) && self.slice_index(^slice, ^result) && self.resolve_elsewhere(*slice, ^slice),
    })]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut T> {
        if self < slice.len() {
            // SAFETY: `self` is checked to be in bounds.
            unsafe { Some(&mut *slice_get_unchecked_mut(slice, self)) }
        } else {
            None
        }
    }

    #[erasure(<usize as core::slice::SliceIndex<[T]>>::get_unchecked)]
    #[requires(own.ptr() == slice)]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    unsafe fn get_unchecked_own(
        self,
        slice: *const [T],
        own: Ghost<&PtrOwn<[T]>>,
    ) -> (*const T, Ghost<&PtrOwn<T>>) {
        assert_unsafe_precondition!(
            check_language_ub,
            "slice::get_unchecked requires that the index is within the slice",
            pearlite! { this < len },
            (this: usize = self, len: usize = slice.len()) => this < len
        );
        // SAFETY: the caller guarantees that `slice` is not dangling, so it
        // cannot be longer than `isize::MAX`. They also guarantee that
        // `self` is in bounds of `slice` so `self` cannot overflow an `isize`,
        // so the call to `add` is safe.
        unsafe {
            // Use intrinsics::assume instead of hint::assert_unchecked so that we don't check the
            // precondition of this function twice.
            core::intrinsics::assume(self < slice.len());
            let ptr = slice_get_unchecked_raw(slice, self, own);
            (
                ptr,
                ghost! { own.index_ptr_own_ref_ghost(*Int::new(self as i128)) },
            )
        }
    }

    #[erasure(<usize as core::slice::SliceIndex<[T]>>::get_unchecked_mut)]
    #[requires(own.ptr() == slice as *const [T])]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 as *const T == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    #[ensures(self.slice_index(*(^own.inner_logic()).val(), *(^result.1.inner_logic()).val()))]
    #[ensures(self.resolve_elsewhere(*own.val(), *(^own.inner_logic()).val()))]
    unsafe fn get_unchecked_mut_own(
        self,
        slice: *mut [T],
        own: Ghost<&mut PtrOwn<[T]>>,
    ) -> (*mut T, Ghost<&mut PtrOwn<T>>) {
        assert_unsafe_precondition!(
            check_library_ub,
            "slice::get_unchecked_mut requires that the index is within the slice",
            pearlite! { this < len },
            (this: usize = self, len: usize = slice.len()) => this < len
        );
        // SAFETY: see comments for `get_unchecked` above.
        unsafe {
            let ptr = slice_get_unchecked_raw_mut(slice, self, ghost! { &**own });
            (
                ptr,
                ghost! { own.into_inner().index_ptr_own_mut_ghost(*Int::new(self as i128)) },
            )
        }
    }

    //#[erasure(<usize as core::slice::SliceIndex<[T]>>::index)]
    #[inline]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    fn index(self, slice: &[T]) -> &T {
        // N.B., use intrinsic indexing
        &(*slice)[self]
    }

    //#[erasure(<usize as core::slice::SliceIndex<[T]>>::index_mut)]
    #[inline]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    #[ensures(self.slice_index(^slice, ^result))]
    #[ensures(self.resolve_elsewhere(*slice, ^slice))]
    fn index_mut(self, slice: &mut [T]) -> &mut T {
        // N.B., use intrinsic indexing
        &mut (*slice)[self]
    }
}

/*
/// Because `IndexRange` guarantees `start <= end`, fewer checks are needed here
/// than there are for a general `Range<usize>` (which might be `100..3`).
unsafe impl<T> SliceIndex<[T]> for ops::IndexRange {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if self.end() <= slice.len() {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe { Some(&*get_offset_len_noubcheck(slice, self.start(), self.len())) }
        } else {
            None
        }
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        if self.end() <= slice.len() {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe { Some(&mut *get_offset_len_mut_noubcheck(slice, self.start(), self.len())) }
        } else {
            None
        }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        assert_unsafe_precondition!(
            check_library_ub,
            "slice::get_unchecked requires that the index is within the slice",
            (end: usize = self.end(), len: usize = slice.len()) => end <= len
        );
        // SAFETY: the caller guarantees that `slice` is not dangling, so it
        // cannot be longer than `isize::MAX`. They also guarantee that
        // `self` is in bounds of `slice` so `self` cannot overflow an `isize`,
        // so the call to `add` is safe.
        unsafe { get_offset_len_noubcheck(slice, self.start(), self.len()) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        assert_unsafe_precondition!(
            check_library_ub,
            "slice::get_unchecked_mut requires that the index is within the slice",
            (end: usize = self.end(), len: usize = slice.len()) => end <= len
        );

        // SAFETY: see comments for `get_unchecked` above.
        unsafe { get_offset_len_mut_noubcheck(slice, self.start(), self.len()) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        if self.end() <= slice.len() {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe { &*get_offset_len_noubcheck(slice, self.start(), self.len()) }
        } else {
            slice_index_fail(self.start(), self.end(), slice.len())
        }
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        if self.end() <= slice.len() {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe { &mut *get_offset_len_mut_noubcheck(slice, self.start(), self.len()) }
        } else {
            slice_index_fail(self.start(), self.end(), slice.len())
        }
    }
} */

#[check(ghost)]
#[requires(start <= end && end@ <= own.len())]
#[ensures(result.ptr() as *const T == (own.ptr() as *const T).offset_logic(start@))]
#[ensures(result.val()@ == own.val()@.subsequence(start@, end@))]
fn ptr_own_slice<T>(own: Ghost<&PtrOwn<[T]>>, start: usize, end: usize) -> Ghost<&PtrOwn<[T]>> {
    ghost! {
        let (own, _) = own.into_inner().split_at_ghost(*Int::new(end as i128));
        let (_, own) = own.split_at_ghost(*Int::new(start as i128));
        own
    }
}

#[check(ghost)]
#[requires(start <= end && end@ <= own.len())]
#[ensures(result.ptr() as *const T == (own.ptr() as *const T).offset_logic(start@))]
#[ensures(result.val()@ == own.val()@.subsequence(start@, end@))]
#[ensures(own.ptr() == (^own).ptr())]
#[ensures((^result).val()@ == (^own).val()@.subsequence(start@, end@))]
#[ensures(forall<i: Int> i < start@ || end@ <= i ==> own.val()@.get(i) == (^own).val()@.get(i))]
fn ptr_own_slice_mut<T>(
    own: Ghost<&mut PtrOwn<[T]>>,
    start: usize,
    end: usize,
) -> Ghost<&mut PtrOwn<[T]>> {
    ghost! {
        let (own, _) = own.into_inner().split_at_mut_ghost(*Int::new(end as i128));
        let (_, own) = own.split_at_mut_ghost(*Int::new(start as i128));
        own
    }
}

/// The methods `index` and `index_mut` panic if:
/// - the start of the range is greater than the end of the range or
/// - the end of the range is out of bounds.
// #[stable(feature = "slice_get_slice_impls", since = "1.15.0")]
unsafe impl<T> SliceIndex<[T]> for ops::Range<usize> {
    type Output = [T];

    #[logic]
    fn in_bounds(self, slice: [T]) -> bool {
        pearlite! { self.start <= self.end && self.end@ <= slice@.len() }
    }

    #[logic]
    fn slice_index(self, slice: [T], res: [T]) -> bool {
        pearlite! { res@ == slice@.subsequence(self.start@, self.end@) }
    }

    #[logic]
    fn resolve_elsewhere(self, old: [T], fin: [T]) -> bool {
        pearlite! {
            old@.len() == fin@.len()
            && forall<i: Int> i < self.start@ || self.end@ <= i ==> old@.get(i) == fin@.get(i)
        }
    }

    #[inline]
    #[erasure(<ops::Range<usize> as core::slice::SliceIndex<[T]>>::get)]
    #[ensures(match result {
        None => !self.in_bounds(*slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result),
    })]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        // Using checked_sub is a safe way to get `SubUnchecked` in MIR
        if let Some(new_len) = usize::checked_sub(self.end, self.start)
            && self.end <= slice.len()
        {
            let (ptr, own) = PtrOwn::from_ref(slice);
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe {
                let ptr = get_offset_len_noubcheck(ptr, self.start, new_len, ghost! { *own });
                let own = ghost! { ptr_own_slice(own, self.start, self.end).into_inner() };
                Some(PtrOwn::as_ref(ptr, own))
            }
        } else {
            None
        }
    }

    #[inline]
    #[erasure(<ops::Range<usize> as core::slice::SliceIndex<[T]>>::get_mut)]
    #[ensures(match result {
        None => !self.in_bounds(*slice) && resolve(slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result) && self.slice_index(^slice, ^result) && self.resolve_elsewhere(*slice, ^slice),
    })]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        if let Some(new_len) = usize::checked_sub(self.end, self.start)
            && self.end <= slice.len()
        {
            let (ptr, own) = PtrOwn::from_mut(slice);
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe {
                let ptr = get_offset_len_mut_noubcheck(ptr, self.start, new_len, ghost! { *own });
                let own = ghost! { ptr_own_slice_mut(own, self.start, self.end).into_inner() };
                Some(PtrOwn::as_mut(ptr, own))
            }
        } else {
            None
        }
    }

    #[inline]
    #[erasure(<ops::Range<usize> as core::slice::SliceIndex<[T]>>::get_unchecked)]
    #[requires(own.ptr() == slice)]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    unsafe fn get_unchecked_own(
        self,
        slice: *const [T],
        own: Ghost<&PtrOwn<[T]>>,
    ) -> (*const [T], Ghost<&PtrOwn<[T]>>) {
        assert_unsafe_precondition!(
            check_library_ub,
            "slice::get_unchecked requires that the range is within the slice",
            pearlite! { end >= start && end <= len },
            (
                start: usize = self.start,
                end: usize = self.end,
                len: usize = slice.len()
            ) => end >= start && end <= len
        );

        // SAFETY: the caller guarantees that `slice` is not dangling, so it
        // cannot be longer than `isize::MAX`. They also guarantee that
        // `self` is in bounds of `slice` so `self` cannot overflow an `isize`,
        // so the call to `add` is safe and the length calculation cannot overflow.
        unsafe {
            // Using the intrinsic avoids a superfluous UB check,
            // since the one on this method already checked `end >= start`.
            let new_len = crate::intrinsics::unchecked_sub(self.end, self.start);
            let ptr = get_offset_len_noubcheck(slice, self.start, new_len, ghost! { *own });
            let own = ghost! { ptr_own_slice(own, self.start, self.end).into_inner() };
            (ptr, own)
        }
    }

    #[inline]
    #[erasure(<ops::Range<usize> as core::slice::SliceIndex<[T]>>::get_unchecked_mut)]
    #[requires(own.ptr() == slice as *const [T])]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 as *const Self::Output == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    #[ensures(self.slice_index(*(^own.inner_logic()).val(), *(^result.1.inner_logic()).val()))]
    #[ensures(self.resolve_elsewhere(*own.val(), *(^own.inner_logic()).val()))]
    unsafe fn get_unchecked_mut_own(
        self,
        slice: *mut [T],
        own: Ghost<&mut PtrOwn<[T]>>,
    ) -> (*mut [T], Ghost<&mut PtrOwn<[T]>>) {
        assert_unsafe_precondition!(
            check_library_ub,
            "slice::get_unchecked_mut requires that the range is within the slice",
            pearlite! { end >= start && end <= len },
            (
                start: usize = self.start,
                end: usize = self.end,
                len: usize = slice.len()
            ) => end >= start && end <= len
        );
        // SAFETY: see comments for `get_unchecked` above.
        unsafe {
            let new_len = crate::intrinsics::unchecked_sub(self.end, self.start);
            let ptr = get_offset_len_mut_noubcheck(slice, self.start, new_len, ghost! { *own });
            let own = ghost! { ptr_own_slice_mut(own, self.start, self.end).into_inner() };
            (ptr, own)
        }
    }

    #[inline(always)]
    #[erasure(<ops::Range<usize> as core::slice::SliceIndex<[T]>>::index)]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    fn index(self, slice: &[T]) -> &[T] {
        // Using checked_sub is a safe way to get `SubUnchecked` in MIR
        if let Some(new_len) = usize::checked_sub(self.end, self.start)
            && self.end <= slice.len()
        {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe {
                let (ptr, own) = PtrOwn::from_ref(slice);
                let ptr = get_offset_len_noubcheck(ptr, self.start, new_len, ghost! { *own });
                let own = ghost! { ptr_own_slice(own, self.start, self.end).into_inner() };
                PtrOwn::as_ref(ptr, own)
            }
        } else {
            slice_index_fail(self.start, self.end, slice.len())
        }
    }

    #[inline]
    #[erasure(<ops::Range<usize> as core::slice::SliceIndex<[T]>>::index_mut)]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    #[ensures(self.slice_index(^slice, ^result))]
    #[ensures(self.resolve_elsewhere(*slice, ^slice))]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        if let Some(new_len) = usize::checked_sub(self.end, self.start)
            && self.end <= slice.len()
        {
            // SAFETY: `self` is checked to be valid and in bounds above.
            unsafe {
                let (ptr, own) = PtrOwn::from_mut(slice);
                let ptr = get_offset_len_mut_noubcheck(ptr, self.start, new_len, ghost! { *own });
                let own = ghost! { ptr_own_slice_mut(own, self.start, self.end).into_inner() };
                PtrOwn::as_mut(ptr, own)
            }
        } else {
            slice_index_fail(self.start, self.end, slice.len())
        }
    }
}

// #[unstable(feature = "new_range_api", issue = "125687")]
unsafe impl<T> SliceIndex<[T]> for core::range::Range<usize> {
    type Output = [T];

    #[logic]
    fn in_bounds(self, slice: [T]) -> bool {
        pearlite! { self.start <= self.end && self.end@ <= slice@.len() }
    }

    #[logic]
    fn slice_index(self, slice: [T], res: [T]) -> bool {
        pearlite! { res@ == slice@.subsequence(self.start@, self.end@) }
    }

    #[logic]
    fn resolve_elsewhere(self, old: [T], fin: [T]) -> bool {
        pearlite! {
            old@.len() == fin@.len()
            && forall<i: Int> i < self.start@ || self.end@ <= i ==> old@.get(i) == fin@.get(i)
        }
    }

    #[inline]
    #[erasure(<core::range::Range<usize> as core::slice::SliceIndex<[T]>>::get)]
    #[ensures(match result {
        None => !self.in_bounds(*slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result),
    })]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        ops::Range::from(self).get(slice)
    }

    #[inline]
    #[erasure(<core::range::Range<usize> as core::slice::SliceIndex<[T]>>::get_mut)]
    #[ensures(match result {
        None => !self.in_bounds(*slice) && resolve(slice),
        Some(result) => self.in_bounds(*slice) && self.slice_index(*slice, *result) && self.slice_index(^slice, ^result) && self.resolve_elsewhere(*slice, ^slice),
    })]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        ops::Range::from(self).get_mut(slice)
    }

    #[inline]
    #[erasure(<core::range::Range<usize> as core::slice::SliceIndex<[T]>>::get_unchecked)]
    #[requires(own.ptr() == slice)]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    unsafe fn get_unchecked_own(
        self,
        slice: *const [T],
        own: Ghost<&PtrOwn<[T]>>,
    ) -> (*const [T], Ghost<&PtrOwn<[T]>>) {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { ops::Range::from(self).get_unchecked_own(slice, own) }
    }

    #[inline]
    #[erasure(<core::range::Range<usize> as core::slice::SliceIndex<[T]>>::get_unchecked_mut)]
    #[requires(own.ptr() == slice as *const [T])]
    #[requires(self.in_bounds(*own.val()))]
    #[ensures(result.0 as *const Self::Output == result.1.ptr())]
    #[ensures(self.slice_index(*own.val(), *result.1.val()))]
    #[ensures(self.slice_index(*(^own.inner_logic()).val(), *(^result.1.inner_logic()).val()))]
    #[ensures(self.resolve_elsewhere(*own.val(), *(^own.inner_logic()).val()))]
    unsafe fn get_unchecked_mut_own(
        self,
        slice: *mut [T],
        own: Ghost<&mut PtrOwn<[T]>>,
    ) -> (*mut [T], Ghost<&mut PtrOwn<[T]>>) {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { ops::Range::from(self).get_unchecked_mut_own(slice, own) }
    }

    #[inline(always)]
    #[erasure(<core::range::Range<usize> as core::slice::SliceIndex<[T]>>::index)]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    fn index(self, slice: &[T]) -> &[T] {
        ops::Range::from(self).index(slice)
    }

    #[inline]
    #[erasure(<core::range::Range<usize> as core::slice::SliceIndex<[T]>>::index_mut)]
    #[requires(self.in_bounds(*slice))]
    #[ensures(self.slice_index(*slice, *result))]
    #[ensures(self.slice_index(^slice, ^result))]
    #[ensures(self.resolve_elsewhere(*slice, ^slice))]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        ops::Range::from(self).index_mut(slice)
    }
}

/*
/// The methods `index` and `index_mut` panic if the end of the range is out of bounds.
// #[stable(feature = "slice_get_slice_impls", since = "1.15.0")]
unsafe impl<T> SliceIndex<[T]> for ops::RangeTo<usize> {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        (0..self.end).get(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        (0..self.end).get_mut(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { (0..self.end).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { (0..self.end).get_unchecked_mut(slice) }
    }

    #[inline(always)]
    fn index(self, slice: &[T]) -> &[T] {
        (0..self.end).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        (0..self.end).index_mut(slice)
    }
}

/// The methods `index` and `index_mut` panic if the start of the range is out of bounds.
// #[stable(feature = "slice_get_slice_impls", since = "1.15.0")]
unsafe impl<T> SliceIndex<[T]> for ops::RangeFrom<usize> {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        (self.start..slice.len()).get(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        (self.start..slice.len()).get_mut(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { (self.start..slice.len()).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { (self.start..slice.len()).get_unchecked_mut(slice) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        if self.start > slice.len() {
            slice_index_fail(self.start, slice.len(), slice.len())
        }
        // SAFETY: `self` is checked to be valid and in bounds above.
        unsafe { &*self.get_unchecked(slice) }
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        if self.start > slice.len() {
            slice_index_fail(self.start, slice.len(), slice.len())
        }
        // SAFETY: `self` is checked to be valid and in bounds above.
        unsafe { &mut *self.get_unchecked_mut(slice) }
    }
}

// #[unstable(feature = "new_range_api", issue = "125687")]
unsafe impl<T> SliceIndex<[T]> for range::RangeFrom<usize> {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        ops::RangeFrom::from(self).get(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        ops::RangeFrom::from(self).get_mut(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { ops::RangeFrom::from(self).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { ops::RangeFrom::from(self).get_unchecked_mut(slice) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        ops::RangeFrom::from(self).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        ops::RangeFrom::from(self).index_mut(slice)
    }
}

// #[stable(feature = "slice_get_slice_impls", since = "1.15.0")]
unsafe impl<T> SliceIndex<[T]> for ops::RangeFull {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        Some(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        Some(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        slice
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        slice
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        slice
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        slice
    }
}

/// The methods `index` and `index_mut` panic if:
/// - the end of the range is `usize::MAX` or
/// - the start of the range is greater than the end of the range or
/// - the end of the range is out of bounds.
// #[stable(feature = "inclusive_range", since = "1.26.0")]
unsafe impl<T> SliceIndex<[T]> for ops::RangeInclusive<usize> {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        if *self.end() == usize::MAX { None } else { self.into_slice_range().get(slice) }
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        if *self.end() == usize::MAX { None } else { self.into_slice_range().get_mut(slice) }
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { self.into_slice_range().get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { self.into_slice_range().get_unchecked_mut(slice) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        if *self.end() == usize::MAX {
            slice_end_index_overflow_fail();
        }
        self.into_slice_range().index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        if *self.end() == usize::MAX {
            slice_end_index_overflow_fail();
        }
        self.into_slice_range().index_mut(slice)
    }
}

// #[unstable(feature = "new_range_api", issue = "125687")]
unsafe impl<T> SliceIndex<[T]> for range::RangeInclusive<usize> {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        ops::RangeInclusive::from(self).get(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        ops::RangeInclusive::from(self).get_mut(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { ops::RangeInclusive::from(self).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { ops::RangeInclusive::from(self).get_unchecked_mut(slice) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        ops::RangeInclusive::from(self).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        ops::RangeInclusive::from(self).index_mut(slice)
    }
}

/// The methods `index` and `index_mut` panic if the end of the range is out of bounds.
// #[stable(feature = "inclusive_range", since = "1.26.0")]
unsafe impl<T> SliceIndex<[T]> for ops::RangeToInclusive<usize> {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&[T]> {
        (0..=self.end).get(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut [T]> {
        (0..=self.end).get_mut(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { (0..=self.end).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut [T] {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { (0..=self.end).get_unchecked_mut(slice) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &[T] {
        (0..=self.end).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut [T] {
        (0..=self.end).index_mut(slice)
    }
}

/// Performs bounds checking of a range.
///
/// This method is similar to [`Index::index`] for slices, but it returns a
/// [`Range`] equivalent to `range`. You can use this method to turn any range
/// into `start` and `end` values.
///
/// `bounds` is the range of the slice to use for bounds checking. It should
/// be a [`RangeTo`] range that ends at the length of the slice.
///
/// The returned [`Range`] is safe to pass to [`slice::get_unchecked`] and
/// [`slice::get_unchecked_mut`] for slices with the given range.
///
/// [`Range`]: ops::Range
/// [`RangeTo`]: ops::RangeTo
/// [`slice::get_unchecked`]: slice::get_unchecked
/// [`slice::get_unchecked_mut`]: slice::get_unchecked_mut
///
/// # Panics
///
/// Panics if `range` would be out of bounds.
///
/// # Examples
///
/// ```
/// #![feature(slice_range)]
///
/// use std::slice;
///
/// let v = [10, 40, 30];
/// assert_eq!(1..2, slice::range(1..2, ..v.len()));
/// assert_eq!(0..2, slice::range(..2, ..v.len()));
/// assert_eq!(1..3, slice::range(1.., ..v.len()));
/// ```
///
/// Panics when [`Index::index`] would panic:
///
/// ```should_panic
/// #![feature(slice_range)]
///
/// use std::slice;
///
/// let _ = slice::range(2..1, ..3);
/// ```
///
/// ```should_panic
/// #![feature(slice_range)]
///
/// use std::slice;
///
/// let _ = slice::range(1..4, ..3);
/// ```
///
/// ```should_panic
/// #![feature(slice_range)]
///
/// use std::slice;
///
/// let _ = slice::range(1..=usize::MAX, ..3);
/// ```
///
/// [`Index::index`]: ops::Index::index
#[track_caller]
// #[unstable(feature = "slice_range", issue = "76393")]
*/
#[must_use]
#[erasure(private core::slice::index::range)]
#[requires(int_lower_bound(range.start_bound_logic()) <= int_upper_bound(range.end_bound_logic(), bounds.end) && int_upper_bound(range.end_bound_logic(), bounds.end) <= bounds.end@)]
#[ensures(result.start@ == int_lower_bound(range.start_bound_logic()))]
#[ensures(result.end@ == int_upper_bound(range.end_bound_logic(), bounds.end))]
pub fn range<R>(range: R, bounds: ops::RangeTo<usize>) -> ops::Range<usize>
where
    R: RangeBounds<usize>,
{
    let len = bounds.end;

    let end = match range.end_bound() {
        ops::Bound::Included(&end) if end >= len => slice_index_fail(0, end, len),
        // Cannot overflow because `end < len` implies `end < usize::MAX`.
        ops::Bound::Included(&end) => end + 1,

        ops::Bound::Excluded(&end) if end > len => slice_index_fail(0, end, len),
        ops::Bound::Excluded(&end) => end,
        ops::Bound::Unbounded => len,
    };

    let start = match range.start_bound() {
        ops::Bound::Excluded(&start) if start >= end => slice_index_fail(start, end, len),
        // Cannot overflow because `start < end` implies `start < usize::MAX`.
        ops::Bound::Excluded(&start) => start + 1,

        ops::Bound::Included(&start) if start > end => slice_index_fail(start, end, len),
        ops::Bound::Included(&start) => start,

        ops::Bound::Unbounded => 0,
    };

    ops::Range { start, end }
}

/// Convert a lower bound to an inclusive lower bound, with a minimum of `0`.
#[logic(open)]
pub fn int_lower_bound(lo: Bound<&usize>) -> Int {
    pearlite! {
        match lo {
            Bound::Included(lo) => lo@,
            Bound::Excluded(lo) => lo@ + 1,
            Bound::Unbounded => 0,
        }
    }
}

/// Convert an upper bound to an exclusive upper bound, with a maximum of `len`.
#[logic(open)]
pub fn int_upper_bound(hi: Bound<&usize>, len: usize) -> Int {
    pearlite! {
        match hi {
            Bound::Included(hi) => hi@ + 1,
            Bound::Excluded(hi) => hi@,
            Bound::Unbounded => len@,
        }
    }
}

/*
/// Performs bounds checking of a range without panicking.
///
/// This is a version of [`range()`] that returns [`None`] instead of panicking.
///
/// # Examples
///
/// ```
/// #![feature(slice_range)]
///
/// use std::slice;
///
/// let v = [10, 40, 30];
/// assert_eq!(Some(1..2), slice::try_range(1..2, ..v.len()));
/// assert_eq!(Some(0..2), slice::try_range(..2, ..v.len()));
/// assert_eq!(Some(1..3), slice::try_range(1.., ..v.len()));
/// ```
///
/// Returns [`None`] when [`Index::index`] would panic:
///
/// ```
/// #![feature(slice_range)]
///
/// use std::slice;
///
/// assert_eq!(None, slice::try_range(2..1, ..3));
/// assert_eq!(None, slice::try_range(1..4, ..3));
/// assert_eq!(None, slice::try_range(1..=usize::MAX, ..3));
/// ```
///
/// [`Index::index`]: ops::Index::index
// #[unstable(feature = "slice_range", issue = "76393")]
#[must_use]
pub fn try_range<R>(range: R, bounds: ops::RangeTo<usize>) -> Option<ops::Range<usize>>
where
    R: ops::RangeBounds<usize>,
{
    let len = bounds.end;

    let start = match range.start_bound() {
        ops::Bound::Included(&start) => start,
        ops::Bound::Excluded(start) => start.checked_add(1)?,
        ops::Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        ops::Bound::Included(end) => end.checked_add(1)?,
        ops::Bound::Excluded(&end) => end,
        ops::Bound::Unbounded => len,
    };

    if start > end || end > len { None } else { Some(ops::Range { start, end }) }
}

/// Converts a pair of `ops::Bound`s into `ops::Range` without performing any
/// bounds checking or (in debug) overflow checking.
pub(crate) fn into_range_unchecked(
    len: usize,
    (start, end): (ops::Bound<usize>, ops::Bound<usize>),
) -> ops::Range<usize> {
    use ops::Bound;
    let start = match start {
        Bound::Included(i) => i,
        Bound::Excluded(i) => i + 1,
        Bound::Unbounded => 0,
    };
    let end = match end {
        Bound::Included(i) => i + 1,
        Bound::Excluded(i) => i,
        Bound::Unbounded => len,
    };
    start..end
}

/// Converts pair of `ops::Bound`s into `ops::Range`.
/// Returns `None` on overflowing indices.
pub(crate) fn into_range(
    len: usize,
    (start, end): (ops::Bound<usize>, ops::Bound<usize>),
) -> Option<ops::Range<usize>> {
    use ops::Bound;
    let start = match start {
        Bound::Included(start) => start,
        Bound::Excluded(start) => start.checked_add(1)?,
        Bound::Unbounded => 0,
    };

    let end = match end {
        Bound::Included(end) => end.checked_add(1)?,
        Bound::Excluded(end) => end,
        Bound::Unbounded => len,
    };

    // Don't bother with checking `start < end` and `end <= len`
    // since these checks are handled by `Range` impls

    Some(start..end)
}

/// Converts pair of `ops::Bound`s into `ops::Range`.
/// Panics on overflowing indices.
pub(crate) fn into_slice_range(
    len: usize,
    (start, end): (ops::Bound<usize>, ops::Bound<usize>),
) -> ops::Range<usize> {
    let end = match end {
        ops::Bound::Included(end) if end >= len => slice_index_fail(0, end, len),
        // Cannot overflow because `end < len` implies `end < usize::MAX`.
        ops::Bound::Included(end) => end + 1,

        ops::Bound::Excluded(end) if end > len => slice_index_fail(0, end, len),
        ops::Bound::Excluded(end) => end,

        ops::Bound::Unbounded => len,
    };

    let start = match start {
        ops::Bound::Excluded(start) if start >= end => slice_index_fail(start, end, len),
        // Cannot overflow because `start < end` implies `start < usize::MAX`.
        ops::Bound::Excluded(start) => start + 1,

        ops::Bound::Included(start) if start > end => slice_index_fail(start, end, len),
        ops::Bound::Included(start) => start,

        ops::Bound::Unbounded => 0,
    };

    start..end
}

// #[stable(feature = "slice_index_with_ops_bound_pair", since = "1.53.0")]
unsafe impl<T> SliceIndex<[T]> for (ops::Bound<usize>, ops::Bound<usize>) {
    type Output = [T];

    #[inline]
    fn get(self, slice: &[T]) -> Option<&Self::Output> {
        into_range(slice.len(), self)?.get(slice)
    }

    #[inline]
    fn get_mut(self, slice: &mut [T]) -> Option<&mut Self::Output> {
        into_range(slice.len(), self)?.get_mut(slice)
    }

    #[inline]
    unsafe fn get_unchecked(self, slice: *const [T]) -> *const Self::Output {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked`.
        unsafe { into_range_unchecked(slice.len(), self).get_unchecked(slice) }
    }

    #[inline]
    unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut Self::Output {
        // SAFETY: the caller has to uphold the safety contract for `get_unchecked_mut`.
        unsafe { into_range_unchecked(slice.len(), self).get_unchecked_mut(slice) }
    }

    #[inline]
    fn index(self, slice: &[T]) -> &Self::Output {
        into_slice_range(slice.len(), self).index(slice)
    }

    #[inline]
    fn index_mut(self, slice: &mut [T]) -> &mut Self::Output {
        into_slice_range(slice.len(), self).index_mut(slice)
    }
}
 */
