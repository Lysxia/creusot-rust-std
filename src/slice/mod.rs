//! Slice management and manipulation.
//!
//! For more details see [`std::slice`].
//!
//! [`std::slice`]: ../../std/slice/index.html

// #![stable(feature = "rust1", since = "1.0.0")]

use creusot_contracts::ptr_own::PtrOwn;
use creusot_contracts::{Clone, PartialEq, *};

use crate::intrinsics::{exact_div, unchecked_sub};
use core::cmp::Ordering::{self, Equal, Greater, Less};
use core::mem::{self, MaybeUninit, SizedTypeProperties};
// use core::num::NonZero;
use core::ops::{/* OneSidedRange, OneSidedRangeBound, */ Range, RangeBounds, RangeInclusive};
// use core::panic::const_panic;
use core::simd::{self, Simd};
use core::{hint /* range, */, ptr};
use crate::ptr as vptr;

/*
#[unstable(
    feature = "slice_internals",
    issue = "none",
    reason = "exposed from core to be reused in std; use the memchr crate"
)]
/// Pure Rust memchr implementation, taken from rust-memchr
pub mod memchr;

#[unstable(
    feature = "slice_internals",
    issue = "none",
    reason = "exposed from core to be reused in std;"
)]
#[doc(hidden)]
pub mod sort;

mod ascii;
mod cmp;
*/
pub(crate) mod index;
mod raw;
mod rotate;
/*
mod iter;
mod rotate;
mod specialize;

#[stable(feature = "inherent_ascii_escape", since = "1.60.0")]
pub use ascii::EscapeAscii;
#[unstable(feature = "str_internals", issue = "none")]
#[doc(hidden)]
pub use ascii::is_ascii_simple;
*/
//#[stable(feature = "slice_get_slice", since = "1.28.0")]
use index::{SliceIndex, range};

use raw::{from_raw_parts, from_raw_parts_mut};

// cannot define inherent `impl` for primitive types
pub trait SliceExt<T> {
    unsafe fn get_unchecked<I>(&self, index: I) -> &I::Output
    where
        I: SliceIndex<Self>;

    unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
    where
        I: SliceIndex<Self>;

    unsafe fn swap_unchecked(&mut self, a: usize, b: usize);

    unsafe fn as_chunks_unchecked<const N: usize>(&self) -> &[[T; N]];

    unsafe fn as_chunks_unchecked_mut<const N: usize>(&mut self) -> &mut [[T; N]];

    unsafe fn split_at_unchecked(&self, mid: usize) -> (&[T], &[T]);

    unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut [T], &mut [T]);

    fn align_to_offsets<U>(&self) -> (usize, usize);

    unsafe fn align_to<U>(&self) -> (&[T], &[U], &[T]);

    unsafe fn align_to_mut<U>(&mut self) -> (&mut [T], &mut [U], &mut [T]);

    fn first_chunk<const N: usize>(&self) -> Option<&[T; N]>;
    fn first_chunk_mut<const N: usize>(&mut self) -> Option<&mut [T; N]>;
    fn split_first_chunk<const N: usize>(&self) -> Option<(&[T; N], &[T])>;
    fn split_first_chunk_mut<const N: usize>(&mut self) -> Option<(&mut [T; N], &mut [T])>;
    fn split_last_chunk<const N: usize>(&self) -> Option<(&[T], &[T; N])>;
    fn split_last_chunk_mut<const N: usize>(&mut self) -> Option<(&mut [T], &mut [T; N])>;
    fn last_chunk<const N: usize>(&self) -> Option<&[T; N]>;
    fn last_chunk_mut<const N: usize>(&mut self) -> Option<&mut [T; N]>;
    fn reverse(&mut self);
    fn as_chunks<const N: usize>(&self) -> (&[[T; N]], &[T]);
    fn as_rchunks<const N: usize>(&self) -> (&[T], &[[T; N]]);
    fn as_chunks_mut<const N: usize>(&mut self) -> (&mut [[T; N]], &mut [T]);
    fn split_at_checked(&self, mid: usize) -> Option<(&[T], &[T])>;
    fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])>;
    fn binary_search_by<'a, F>(&'a self, f: F) -> Result<usize, usize>
    where
        T: 'a,
        F: FnMut(&'a T) -> Ordering;
    fn partition_dedup_by<F>(&mut self, same_bucket: F) -> (&mut [T], &mut [T])
    where
        F: FnMut(&mut T, &mut T) -> bool;
    fn rotate_left(&mut self, mid: usize);
    fn rotate_right(&mut self, mid: usize);
    fn copy_from_slice(&mut self, src: &[T])
    where
        T: Copy;
    fn copy_within<R: RangeBounds<usize>>(&mut self, src: R, dest: usize)
    where
        T: Copy;
    fn swap_with_slice(&mut self, other: &mut [T]);
    fn as_simd<const LANES: usize>(&self) -> (&[T], &[Simd<T, LANES>], &[T])
    where
        Simd<T, LANES>: AsRef<[T; LANES]>,
        T: simd::SimdElement,
        simd::LaneCount<LANES>: simd::SupportedLaneCount;

    fn as_simd_mut<const LANES: usize>(&mut self) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
    where
        Simd<T, LANES>: AsMut<[T; LANES]>,
        T: simd::SimdElement,
        simd::LaneCount<LANES>: simd::SupportedLaneCount;

    fn get_disjoint_mut<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> Result<[&mut I::Output; N], GetDisjointMutError>
    where
        I: GetDisjointMutIndex + SliceIndex<Self>;

    unsafe fn get_disjoint_unchecked_mut<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> [&mut I::Output; N]
    where
        I: GetDisjointMutIndex + SliceIndex<Self>;
}

#[pure]
#[requires(0 <= i && i < s.len() && 0 <= j && j < s.len() && i != j)]
#[ensures(result.0.ptr() == s.ptr().as_ptr_logic().offset_logic(i))]
#[ensures(result.1.ptr() == s.ptr().as_ptr_logic().offset_logic(j))]
#[ensures(*result.0.val() == s.val()@[i])]
#[ensures(*result.1.val() == s.val()@[j])]
#[ensures(*(^result.inner_logic().0).val() == (^s.inner_logic()).val()@[i])]
#[ensures(*(^result.inner_logic().1).val() == (^s.inner_logic()).val()@[j])]
#[ensures((^s.inner_logic()).ptr() == s.ptr())]
#[ensures((^s.inner_logic()).len() == s.len())]
#[ensures(forall<k: Int> k != i && k != j ==> (^s.inner_logic()).val()@.get(k) == s.val()@.get(k))]
pub fn block_get_2_ghost<T>(s: Ghost<&mut PtrOwn<[T]>>, i: Int, j: Int) -> Ghost<(&mut PtrOwn<T>, &mut PtrOwn<T>)> {
    proof_assert!(forall<s: Seq<T>, i: Int, j: Int, k: Int> 0 <= i && i <= j && j <= s.len() && 0 <= k && k < j - i ==>
      s.subsequence(i, j)[k] == s[i + k]);
    ghost!{
        let (s0, si) = s.into_inner().split_at_mut_ghost(i);
        if i < j {
            let (si, sj) = si.split_at_mut_ghost(j - i);
            (si.as_ptr_own_mut_ghost(), sj.as_ptr_own_mut_ghost())
        } else {
            let (_, sj) = s0.split_at_mut_ghost(j);
            (si.as_ptr_own_mut_ghost(), sj.as_ptr_own_mut_ghost())
        }
    }
}

impl<T> SliceExt<T> for [T] {
    // For the following unsafe functions (in library/core/src/slice/mod.rs):
    //
    //     Write contracts specifying the safety precondition(s) that the caller must uphold, then
    //     Verify that if the caller respects those preconditions, the function does not cause undefined behavior.

    #[trusted]
    #[requires(false)]
    unsafe fn get_unchecked<I>(&self, index: I) -> &I::Output
    where
        I: SliceIndex<Self>,
    {
        // SAFETY: the caller must uphold most of the safety requirements for `get_unchecked`;
        // the slice is dereferenceable because `self` is a safe reference.
        // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
        unsafe { &*index.get_unchecked(self) }
    }

    #[trusted]
    #[requires(false)]
    unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
    where
        I: SliceIndex<Self>,
    {
        // SAFETY: the caller must uphold the safety requirements for `get_unchecked_mut`;
        // the slice is dereferenceable because `self` is a safe reference.
        // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
        unsafe { &mut *index.get_unchecked_mut(self) }
    }

    // `s.exchange(t, i, j)` says precisely that `s: Seq<T>` is the result of exchanging
    // elements at indices `i` and `j` in `t`.
    #[requires(a@ < self@.len() && b@ < self@.len())]
    #[ensures((^self)@.exchange(self@, a@, b@))]
    /* pub const */
    unsafe fn swap_unchecked(&mut self, a: usize, b: usize) {
        // assert_unsafe_precondition!(
        //     check_library_ub,
        //     "slice::swap_unchecked requires that the indices are within the slice",
        //     (
        //         len: usize = self.len(),
        //         a: usize = a,
        //         b: usize = b,
        //     ) => a < len && b < len,
        // );

        let (ptr, mut owns) = self.as_mut_ptr_own();
        let own = ghost! {
            if a == b {
              let a_ = Int::new(a as i128).into_inner();
              vptr::DisjointOrEqual::Equal(owns.index_ptr_own_mut_ghost(a_))
            } else {
              let a_ = Int::new(a as i128).into_inner();
              let b_ = Int::new(b as i128).into_inner();
              let (own_a, own_b) = block_get_2_ghost(owns, a_, b_).into_inner();
              vptr::DisjointOrEqual::Disjoint(own_a, own_b)
            }
        };

        // SAFETY: caller has to guarantee that `a < self.len()` and `b < self.len()`
        unsafe {
            vptr::swap_disjoint(ptr.add_own(a, ghost!(own.left_ghost().as_slice_own_ref_ghost())), ptr.add_own(b, ghost!(own.right_ghost().as_slice_own_ref_ghost())), own);
        }
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    unsafe fn as_chunks_unchecked<const N: usize>(&self) -> &[[T; N]] {
        // assert_unsafe_precondition!(
        //     check_language_ub,
        //     "slice::as_chunks_unchecked requires `N != 0` and the slice to split exactly into `N`-element chunks",
        //     (n: usize = N, len: usize = self.len()) => n != 0 && len % n == 0,
        // );
        // SAFETY: Caller must guarantee that `N` is nonzero and exactly divides the slice length
        let new_len = unsafe { exact_div(self.len(), N) };
        // SAFETY: We cast a slice of `new_len * N` elements into
        // a slice of `new_len` many `N` elements chunks.
        unsafe { from_raw_parts(self.as_ptr().cast(), new_len) }
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    unsafe fn as_chunks_unchecked_mut<const N: usize>(&mut self) -> &mut [[T; N]] {
        // assert_unsafe_precondition!(
        //     check_language_ub,
        //     "slice::as_chunks_unchecked requires `N != 0` and the slice to split exactly into `N`-element chunks",
        //     (n: usize = N, len: usize = self.len()) => n != 0 && len % n == 0
        // );
        // SAFETY: Caller must guarantee that `N` is nonzero and exactly divides the slice length
        let new_len = unsafe { exact_div(self.len(), N) };
        // SAFETY: We cast a slice of `new_len * N` elements into
        // a slice of `new_len` many `N` elements chunks.
        unsafe { from_raw_parts_mut(self.as_mut_ptr().cast(), new_len) }
    }

    /* pub const */
    unsafe fn split_at_unchecked(&self, mid: usize) -> (&[T], &[T]) {
        // FIXME(const-hack): the const function `from_raw_parts` is used to make this
        // function const; previously the implementation used
        // `(self.get_unchecked(..mid), self.get_unchecked(mid..))`

        let len = self.len();
        let ptr = self.as_ptr();

        // assert_unsafe_precondition!(
        //     check_library_ub,
        //     "slice::split_at_unchecked requires the index to be within the slice",
        //     (mid: usize = mid, len: usize = len) => mid <= len,
        // );

        // SAFETY: Caller has to check that `0 <= mid <= self.len()`
        unsafe {
            (
                from_raw_parts(ptr, mid),
                from_raw_parts(ptr.add(mid), unchecked_sub(len, mid)),
            )
        }
    }

    /* pub const */
    unsafe fn split_at_mut_unchecked(&mut self, mid: usize) -> (&mut [T], &mut [T]) {
        let len = self.len();
        let ptr = self.as_mut_ptr();

        // assert_unsafe_precondition!(
        //     check_library_ub,
        //     "slice::split_at_mut_unchecked requires the index to be within the slice",
        //     (mid: usize = mid, len: usize = len) => mid <= len,
        // );

        // SAFETY: Caller has to check that `0 <= mid <= self.len()`.
        //
        // `[ptr; mid]` and `[mid; len]` are not overlapping, so returning a mutable reference
        // is fine.
        unsafe {
            (
                from_raw_parts_mut(ptr, mid),
                from_raw_parts_mut(ptr.add(mid), unchecked_sub(len, mid)),
            )
        }
    }

    /// Function to calculate lengths of the middle and trailing slice for `align_to{,_mut}`.
    fn align_to_offsets<U>(&self) -> (usize, usize) {
        // What we gonna do about `rest` is figure out what multiple of `U`s we can put in a
        // lowest number of `T`s. And how many `T`s we need for each such "multiple".
        //
        // Consider for example T=u8 U=u16. Then we can put 1 U in 2 Ts. Simple. Now, consider
        // for example a case where size_of::<T> = 16, size_of::<U> = 24. We can put 2 Us in
        // place of every 3 Ts in the `rest` slice. A bit more complicated.
        //
        // Formula to calculate this is:
        //
        // Us = lcm(size_of::<T>, size_of::<U>) / size_of::<U>
        // Ts = lcm(size_of::<T>, size_of::<U>) / size_of::<T>
        //
        // Expanded and simplified:
        //
        // Us = size_of::<T> / gcd(size_of::<T>, size_of::<U>)
        // Ts = size_of::<U> / gcd(size_of::<T>, size_of::<U>)
        //
        // Luckily since all this is constant-evaluated... performance here matters not!
        const fn gcd(a: usize, b: usize) -> usize {
            if b == 0 { a } else { gcd(b, a % b) }
        }

        // Explicitly wrap the function call in a const block so it gets
        // constant-evaluated even in debug mode.
        // let gcd: usize = const { gcd(size_of::<T>(), size_of::<U>()) };
        let gcd: usize = gcd(size_of::<T>(), size_of::<U>());
        let ts: usize = size_of::<U>() / gcd;
        let us: usize = size_of::<T>() / gcd;

        // Armed with this knowledge, we can find how many `U`s we can fit!
        let us_len = self.len() / ts * us;
        // And how many `T`s will be in the trailing slice!
        let ts_len = self.len() % ts;
        (us_len, ts_len)
    }

    unsafe fn align_to<U>(&self) -> (&[T], &[U], &[T]) {
        // Note that most of this function will be constant-evaluated,
        // if U::IS_ZST || T::IS_ZST
        if is_zst::<U>() || is_zst::<T>() {
            // handle ZSTs specially, which is – don't handle them at all.
            return (self, &[], &[]);
        }

        // First, find at what point do we split between the first and 2nd slice. Easy with
        // ptr.align_offset.
        let ptr = self.as_ptr();
        // SAFETY: See the `align_to_mut` method for the detailed safety comment.
        let offset = unsafe { crate::ptr::align_offset(ptr, align_of::<U>()) };
        if offset > self.len() {
            (self, &[], &[])
        } else {
            let (left, rest) = self.split_at(offset);
            let (us_len, ts_len) = rest.align_to_offsets::<U>();
            // Inform Miri that we want to consider the "middle" pointer to be suitably aligned.
            #[cfg(miri)]
            crate::intrinsics::miri_promise_symbolic_alignment(
                rest.as_ptr().cast(),
                align_of::<U>(),
            );
            // SAFETY: now `rest` is definitely aligned, so `from_raw_parts` below is okay,
            // since the caller guarantees that we can transmute `T` to `U` safely.
            unsafe {
                (
                    left,
                    from_raw_parts(rest.as_ptr() as *const U, us_len),
                    from_raw_parts(rest.as_ptr().add(rest.len() - ts_len), ts_len),
                )
            }
        }
    }

    unsafe fn align_to_mut<U>(&mut self) -> (&mut [T], &mut [U], &mut [T]) {
        // Note that most of this function will be constant-evaluated,
        // if U::IS_ZST || T::IS_ZST
        if is_zst::<U>() || is_zst::<T>() {
            // handle ZSTs specially, which is – don't handle them at all.
            return (self, &mut [], &mut []);
        }

        // First, find at what point do we split between the first and 2nd slice. Easy with
        // ptr.align_offset.
        let ptr = self.as_ptr();
        // SAFETY: Here we are ensuring we will use aligned pointers for U for the
        // rest of the method. This is done by passing a pointer to &[T] with an
        // alignment targeted for U.
        // `crate::ptr::align_offset` is called with a correctly aligned and
        // valid pointer `ptr` (it comes from a reference to `self`) and with
        // a size that is a power of two (since it comes from the alignment for U),
        // satisfying its safety constraints.
        let offset = unsafe { crate::ptr::align_offset(ptr, align_of::<U>()) };
        if offset > self.len() {
            (self, &mut [], &mut [])
        } else {
            let (left, rest) = self.split_at_mut(offset);
            let (us_len, ts_len) = rest.align_to_offsets::<U>();
            let rest_len = rest.len();
            let mut_ptr = rest.as_mut_ptr();
            // Inform Miri that we want to consider the "middle" pointer to be suitably aligned.
            #[cfg(miri)]
            crate::intrinsics::miri_promise_symbolic_alignment(
                mut_ptr.cast() as *const (),
                align_of::<U>(),
            );
            // We can't use `rest` again after this, that would invalidate its alias `mut_ptr`!
            // SAFETY: see comments for `align_to`.
            unsafe {
                (
                    left,
                    from_raw_parts_mut(mut_ptr as *mut U, us_len),
                    from_raw_parts_mut(mut_ptr.add(rest_len - ts_len), ts_len),
                )
            }
        }
    }

    // Prove that the following safe abstractions (in library/core/src/slice/mod.rs) do not cause undefined behavior:

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn first_chunk<const N: usize>(&self) -> Option<&[T; N]> {
        if self.len() < N {
            None
        } else {
            // SAFETY: We explicitly check for the correct number of elements,
            //   and do not let the reference outlive the slice.
            Some(unsafe { &*(self.as_ptr().cast::<[T; N]>()) })
        }
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn first_chunk_mut<const N: usize>(&mut self) -> Option<&mut [T; N]> {
        if self.len() < N {
            None
        } else {
            // SAFETY: We explicitly check for the correct number of elements,
            //   do not let the reference outlive the slice,
            //   and require exclusive access to the entire slice to mutate the chunk.
            Some(unsafe { &mut *(self.as_mut_ptr().cast::<[T; N]>()) })
        }
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn split_first_chunk<const N: usize>(&self) -> Option<(&[T; N], &[T])> {
        let Some((first, tail)) = self.split_at_checked(N) else {
            return None;
        };

        // SAFETY: We explicitly check for the correct number of elements,
        //   and do not let the references outlive the slice.
        Some((unsafe { &*(first.as_ptr().cast::<[T; N]>()) }, tail))
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn split_first_chunk_mut<const N: usize>(&mut self) -> Option<(&mut [T; N], &mut [T])> {
        let Some((first, tail)) = self.split_at_mut_checked(N) else {
            return None;
        };

        // SAFETY: We explicitly check for the correct number of elements,
        //   do not let the reference outlive the slice,
        //   and enforce exclusive mutability of the chunk by the split.
        Some((unsafe { &mut *(first.as_mut_ptr().cast::<[T; N]>()) }, tail))
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn split_last_chunk<const N: usize>(&self) -> Option<(&[T], &[T; N])> {
        let Some(index) = self.len().checked_sub(N) else {
            return None;
        };
        let (init, last) = self.split_at(index);

        // SAFETY: We explicitly check for the correct number of elements,
        //   and do not let the references outlive the slice.
        Some((init, unsafe { &*(last.as_ptr().cast::<[T; N]>()) }))
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn split_last_chunk_mut<const N: usize>(&mut self) -> Option<(&mut [T], &mut [T; N])> {
        let Some(index) = self.len().checked_sub(N) else {
            return None;
        };
        let (init, last) = self.split_at_mut(index);

        // SAFETY: We explicitly check for the correct number of elements,
        //   do not let the reference outlive the slice,
        //   and enforce exclusive mutability of the chunk by the split.
        Some((init, unsafe { &mut *(last.as_mut_ptr().cast::<[T; N]>()) }))
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn last_chunk<const N: usize>(&self) -> Option<&[T; N]> {
        // FIXME(const-hack): Without const traits, we need this instead of `get`.
        let Some(index) = self.len().checked_sub(N) else {
            return None;
        };
        let (_, last) = self.split_at(index);

        // SAFETY: We explicitly check for the correct number of elements,
        //   and do not let the references outlive the slice.
        Some(unsafe { &*(last.as_ptr().cast::<[T; N]>()) })
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn last_chunk_mut<const N: usize>(&mut self) -> Option<&mut [T; N]> {
        // FIXME(const-hack): Without const traits, we need this instead of `get`.
        let Some(index) = self.len().checked_sub(N) else {
            return None;
        };
        let (_, last) = self.split_at_mut(index);

        // SAFETY: We explicitly check for the correct number of elements,
        //   do not let the reference outlive the slice,
        //   and require exclusive access to the entire slice to mutate the chunk.
        Some(unsafe { &mut *(last.as_mut_ptr().cast::<[T; N]>()) })
    }

    /* pub const */
    fn reverse(&mut self) {
        let half_len = self.len() / 2;
        let Range { start, end } = self.as_mut_ptr_range();

        // These slices will skip the middle item for an odd length,
        // since that one doesn't need to move.
        let (front_half, back_half) =
            // SAFETY: Both are subparts of the original slice, so the memory
            // range is valid, and they don't overlap because they're each only
            // half (or less) of the original slice.
            unsafe {
                (
                    raw::from_raw_parts_mut(start, half_len),
                    raw::from_raw_parts_mut(end.sub(half_len), half_len),
                )
            };

        // Introducing a function boundary here means that the two halves
        // get `noalias` markers, allowing better optimization as LLVM
        // knows that they're disjoint, unlike in the original slice.
        revswap(front_half, back_half, half_len);

        #[inline]
        const fn revswap<T>(a: &mut [T], b: &mut [T], n: usize) {
            debug_assert!(a.len() == n);
            debug_assert!(b.len() == n);

            // Because this function is first compiled in isolation,
            // this check tells LLVM that the indexing below is
            // in-bounds. Then after inlining -- once the actual
            // lengths of the slices are known -- it's removed.
            let (a, _) = a.split_at_mut(n);
            let (b, _) = b.split_at_mut(n);

            let mut i = 0;
            while i < n {
                mem::swap(&mut a[i], &mut b[n - 1 - i]);
                i += 1;
            }
        }
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn as_chunks<const N: usize>(&self) -> (&[[T; N]], &[T]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len_rounded_down = self.len() / N * N;
        // SAFETY: The rounded-down value is always the same or smaller than the
        // original length, and thus must be in-bounds of the slice.
        let (multiple_of_n, remainder) = unsafe { self.split_at_unchecked(len_rounded_down) };
        // SAFETY: We already panicked for zero, and ensured by construction
        // that the length of the subslice is a multiple of N.
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked() };
        (array_slice, remainder)
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn as_rchunks<const N: usize>(&self) -> (&[T], &[[T; N]]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len = self.len() / N;
        let (remainder, multiple_of_n) = self.split_at(self.len() - len * N);
        // SAFETY: We already panicked for zero, and ensured by construction
        // that the length of the subslice is a multiple of N.
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked() };
        (remainder, array_slice)
    }

    #[trusted]
    #[requires(false)]
    /* pub const */
    fn as_chunks_mut<const N: usize>(&mut self) -> (&mut [[T; N]], &mut [T]) {
        assert!(N != 0, "chunk size must be non-zero");
        let len_rounded_down = self.len() / N * N;
        // SAFETY: The rounded-down value is always the same or smaller than the
        // original length, and thus must be in-bounds of the slice.
        let (multiple_of_n, remainder) = unsafe { self.split_at_mut_unchecked(len_rounded_down) };
        // SAFETY: We already panicked for zero, and ensured by construction
        // that the length of the subslice is a multiple of N.
        let array_slice = unsafe { multiple_of_n.as_chunks_unchecked_mut() };
        (array_slice, remainder)
    }

    /* pub const */
    fn split_at_checked(&self, mid: usize) -> Option<(&[T], &[T])> {
        if mid <= self.len() {
            // SAFETY: `[ptr; mid]` and `[mid; len]` are inside `self`, which
            // fulfills the requirements of `split_at_unchecked`.
            Some(unsafe { self.split_at_unchecked(mid) })
        } else {
            None
        }
    }

    /* pub const */
    fn split_at_mut_checked(&mut self, mid: usize) -> Option<(&mut [T], &mut [T])> {
        if mid <= self.len() {
            // SAFETY: `[ptr; mid]` and `[mid; len]` are inside `self`, which
            // fulfills the requirements of `split_at_unchecked`.
            Some(unsafe { self.split_at_mut_unchecked(mid) })
        } else {
            None
        }
    }

    fn binary_search_by<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&'a T) -> Ordering,
    {
        let mut size = self.len();
        if size == 0 {
            return Err(0);
        }
        let mut base = 0usize;

        // This loop intentionally doesn't have an early exit if the comparison
        // returns Equal. We want the number of loop iterations to depend *only*
        // on the size of the input slice so that the CPU can reliably predict
        // the loop count.
        while size > 1 {
            let half = size / 2;
            let mid = base + half;

            // SAFETY: the call is made safe by the following invariants:
            // - `mid >= 0`: by definition
            // - `mid < size`: `mid = size / 2 + size / 4 + size / 8 ...`
            let cmp = f(unsafe { self.get_unchecked(mid) });

            // Binary search interacts poorly with branch prediction, so force
            // the compiler to use conditional moves if supported by the target
            // architecture.
            base = select_unpredictable(cmp == Greater, base, mid);

            // This is imprecise in the case where `size` is odd and the
            // comparison returns Greater: the mid element still gets included
            // by `size` even though it's known to be larger than the element
            // being searched for.
            //
            // This is fine though: we gain more performance by keeping the
            // loop iteration count invariant (and thus predictable) than we
            // lose from considering one additional element.
            size -= half;
        }

        // SAFETY: base is always in [0, size) because base <= mid.
        let cmp = f(unsafe { self.get_unchecked(base) });
        if cmp == Equal {
            // SAFETY: same as the `get_unchecked` above.
            unsafe { hint::assert_unchecked(base < self.len()) };
            Ok(base)
        } else {
            let result = base + (cmp == Less) as usize;
            // SAFETY: same as the `get_unchecked` above.
            // Note that this is `<=`, unlike the assume in the `Ok` path.
            unsafe { hint::assert_unchecked(result <= self.len()) };
            Err(result)
        }
    }

    #[trusted]
    #[requires(false)]
    fn partition_dedup_by<F>(&mut self, mut same_bucket: F) -> (&mut [T], &mut [T])
    where
        F: FnMut(&mut T, &mut T) -> bool,
    {
        // Although we have a mutable reference to `self`, we cannot make
        // *arbitrary* changes. The `same_bucket` calls could panic, so we
        // must ensure that the slice is in a valid state at all times.
        //
        // The way that we handle this is by using swaps; we iterate
        // over all the elements, swapping as we go so that at the end
        // the elements we wish to keep are in the front, and those we
        // wish to reject are at the back. We can then split the slice.
        // This operation is still `O(n)`.
        //
        // Example: We start in this state, where `r` represents "next
        // read" and `w` represents "next_write".
        //
        //           r
        //     +---+---+---+---+---+---+
        //     | 0 | 1 | 1 | 2 | 3 | 3 |
        //     +---+---+---+---+---+---+
        //           w
        //
        // Comparing self[r] against self[w-1], this is not a duplicate, so
        // we swap self[r] and self[w] (no effect as r==w) and then increment both
        // r and w, leaving us with:
        //
        //               r
        //     +---+---+---+---+---+---+
        //     | 0 | 1 | 1 | 2 | 3 | 3 |
        //     +---+---+---+---+---+---+
        //               w
        //
        // Comparing self[r] against self[w-1], this value is a duplicate,
        // so we increment `r` but leave everything else unchanged:
        //
        //                   r
        //     +---+---+---+---+---+---+
        //     | 0 | 1 | 1 | 2 | 3 | 3 |
        //     +---+---+---+---+---+---+
        //               w
        //
        // Comparing self[r] against self[w-1], this is not a duplicate,
        // so swap self[r] and self[w] and advance r and w:
        //
        //                       r
        //     +---+---+---+---+---+---+
        //     | 0 | 1 | 2 | 1 | 3 | 3 |
        //     +---+---+---+---+---+---+
        //                   w
        //
        // Not a duplicate, repeat:
        //
        //                           r
        //     +---+---+---+---+---+---+
        //     | 0 | 1 | 2 | 3 | 1 | 3 |
        //     +---+---+---+---+---+---+
        //                       w
        //
        // Duplicate, advance r. End of slice. Split at w.

        let len = self.len();
        if len <= 1 {
            return (self, &mut []);
        }

        let ptr = self.as_mut_ptr();
        let mut next_read: usize = 1;
        let mut next_write: usize = 1;

        // SAFETY: the `while` condition guarantees `next_read` and `next_write`
        // are less than `len`, thus are inside `self`. `prev_ptr_write` points to
        // one element before `ptr_write`, but `next_write` starts at 1, so
        // `prev_ptr_write` is never less than 0 and is inside the slice.
        // This fulfils the requirements for dereferencing `ptr_read`, `prev_ptr_write`
        // and `ptr_write`, and for using `ptr.add(next_read)`, `ptr.add(next_write - 1)`
        // and `prev_ptr_write.offset(1)`.
        //
        // `next_write` is also incremented at most once per loop at most meaning
        // no element is skipped when it may need to be swapped.
        //
        // `ptr_read` and `prev_ptr_write` never point to the same element. This
        // is required for `&mut *ptr_read`, `&mut *prev_ptr_write` to be safe.
        // The explanation is simply that `next_read >= next_write` is always true,
        // thus `next_read > next_write - 1` is too.
        unsafe {
            // Avoid bounds checks by using raw pointers.
            while next_read < len {
                let ptr_read = ptr.add(next_read);
                let prev_ptr_write = ptr.add(next_write - 1);
                if !same_bucket(&mut *ptr_read, &mut *prev_ptr_write) {
                    if next_read != next_write {
                        let ptr_write = prev_ptr_write.add(1);
                        mem::swap(&mut *ptr_read, &mut *ptr_write);
                    }
                    next_write += 1;
                }
                next_read += 1;
            }
        }

        self.split_at_mut(next_write)
    }

    fn rotate_left(&mut self, mid: usize) {
        assert!(mid <= self.len());
        let k = self.len() - mid;
        let p = self.as_mut_ptr();

        // SAFETY: The range `[p.add(mid) - mid, p.add(mid) + k)` is trivially
        // valid for reading and writing, as required by `ptr_rotate`.
        unsafe {
            rotate::ptr_rotate(mid, p.add(mid), k);
        }
    }

    fn rotate_right(&mut self, k: usize) {
        assert!(k <= self.len());
        let mid = self.len() - k;
        let p = self.as_mut_ptr();

        // SAFETY: The range `[p.add(mid) - mid, p.add(mid) + k)` is trivially
        // valid for reading and writing, as required by `ptr_rotate`.
        unsafe {
            rotate::ptr_rotate(mid, p.add(mid), k);
        }
    }

    /* pub const */
    fn copy_from_slice(&mut self, src: &[T])
    where
        T: Copy,
    {
        // The panic code path was put into a cold function to not bloat the
        // call site.
        // #[cfg_attr(not(feature = "panic_immediate_abort"), inline(never), cold)]
        // #[cfg_attr(feature = "panic_immediate_abort", inline)]
        #[track_caller]
        #[allow(unused_variables)]
        const fn len_mismatch_fail(dst_len: usize, src_len: usize) -> ! {
            // const_panic!(
            //     "copy_from_slice: source slice length does not match destination slice length",
            //     "copy_from_slice: source slice length ({src_len}) does not match destination slice length ({dst_len})",
            //     src_len: usize,
            //     dst_len: usize,
            // )
            panic!()
        }

        if self.len() != src.len() {
            len_mismatch_fail(self.len(), src.len());
        }

        // SAFETY: `self` is valid for `self.len()` elements by definition, and `src` was
        // checked to have the same length. The slices cannot overlap because
        // mutable references are exclusive.
        unsafe {
            ptr::copy_nonoverlapping(src.as_ptr(), self.as_mut_ptr(), self.len());
        }
    }

    #[trusted]
    fn copy_within<R: RangeBounds<usize>>(&mut self, src: R, dest: usize)
    where
        T: Copy,
    {
        let Range {
            start: src_start,
            end: src_end,
        } = range(src, ..self.len());
        let count = src_end - src_start;
        assert!(dest <= self.len() - count, "dest is out of bounds");
        // SAFETY: the conditions for `ptr::copy` have all been checked above,
        // as have those for `ptr::add`.
        unsafe {
            // Derive both `src_ptr` and `dest_ptr` from the same loan
            let ptr = self.as_mut_ptr();
            let src_ptr = ptr.add(src_start);
            let dest_ptr = ptr.add(dest);
            ptr::copy(src_ptr, dest_ptr, count);
        }
    }

    fn swap_with_slice(&mut self, other: &mut [T]) {
        assert!(
            self.len() == other.len(),
            "destination and source slices have different lengths"
        );
        // SAFETY: `self` is valid for `self.len()` elements by definition, and `src` was
        // checked to have the same length. The slices cannot overlap because
        // mutable references are exclusive.
        unsafe {
            ptr::swap_nonoverlapping(self.as_mut_ptr(), other.as_mut_ptr(), self.len());
        }
    }

    fn as_simd<const LANES: usize>(&self) -> (&[T], &[Simd<T, LANES>], &[T])
    where
        Simd<T, LANES>: AsRef<[T; LANES]>,
        T: simd::SimdElement,
        simd::LaneCount<LANES>: simd::SupportedLaneCount,
    {
        // These are expected to always match, as vector types are laid out like
        // arrays per <https://llvm.org/docs/LangRef.html#vector-type>, but we
        // might as well double-check since it'll optimize away anyhow.
        assert_eq!(size_of::<Simd<T, LANES>>(), size_of::<[T; LANES]>());

        // SAFETY: The simd types have the same layout as arrays, just with
        // potentially-higher alignment, so the de-facto transmutes are sound.
        unsafe { self.align_to() }
    }

    fn as_simd_mut<const LANES: usize>(&mut self) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
    where
        Simd<T, LANES>: AsMut<[T; LANES]>,
        T: simd::SimdElement,
        simd::LaneCount<LANES>: simd::SupportedLaneCount,
    {
        // These are expected to always match, as vector types are laid out like
        // arrays per <https://llvm.org/docs/LangRef.html#vector-type>, but we
        // might as well double-check since it'll optimize away anyhow.
        assert_eq!(size_of::<Simd<T, LANES>>(), size_of::<[T; LANES]>());

        // SAFETY: The simd types have the same layout as arrays, just with
        // potentially-higher alignment, so the de-facto transmutes are sound.
        unsafe { self.align_to_mut() }
    }

    fn get_disjoint_mut<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> Result<[&mut I::Output; N], GetDisjointMutError>
    where
        I: GetDisjointMutIndex + SliceIndex<Self>,
    {
        get_disjoint_check_valid(&indices, self.len())?;
        // SAFETY: The `get_disjoint_check_valid()` call checked that all indices
        // are disjunct and in bounds.
        unsafe { Ok(self.get_disjoint_unchecked_mut(indices)) }
    }

    #[trusted]
    unsafe fn get_disjoint_unchecked_mut<I, const N: usize>(
        &mut self,
        indices: [I; N],
    ) -> [&mut I::Output; N]
    where
        I: GetDisjointMutIndex + SliceIndex<Self>,
    {
        // NB: This implementation is written as it is because any variation of
        // `indices.map(|i| self.get_unchecked_mut(i))` would make miri unhappy,
        // or generate worse code otherwise. This is also why we need to go
        // through a raw pointer here.
        let slice: *mut [T] = self;
        let mut arr: MaybeUninit<[&mut I::Output; N]> = MaybeUninit::uninit();
        let arr_ptr = arr.as_mut_ptr();

        // SAFETY: We expect `indices` to contain disjunct values that are
        // in bounds of `self`.
        unsafe {
            for i in 0..N {
                let idx = indices.get_unchecked(i).clone();
                arr_ptr.cast::<&mut I::Output>().add(i).write(
                    // &mut *slice.get_unchecked_mut(idx)
                    &mut *idx.get_unchecked_mut(slice),
                );
            }
            arr.assume_init()
        }
    }
}

pub trait ArraySliceExt<T, const N: usize> {
    fn as_flattened(&self) -> &[T];
    fn as_flattened_mut(&mut self) -> &mut [T];
}

impl<T, const N: usize> ArraySliceExt<T, N> for [[T; N]] {
    #[trusted]
    fn as_flattened(&self) -> &[T] {
        let len = // if T::IS_ZST {
        if is_zst::<T>() {
            self.len().checked_mul(N).expect("slice len overflow")
        } else {
            // SAFETY: `self.len() * N` cannot overflow because `self` is
            // already in the address space.
            unsafe { self.len().unchecked_mul(N) }
        };
        // SAFETY: `[T]` is layout-identical to `[T; N]`
        unsafe { from_raw_parts(self.as_ptr().cast(), len) }
    }

    #[trusted]
    fn as_flattened_mut(&mut self) -> &mut [T] {
        let len = if T::IS_ZST {
            self.len().checked_mul(N).expect("slice len overflow")
        } else {
            // SAFETY: `self.len() * N` cannot overflow because `self` is
            // already in the address space.
            unsafe { self.len().unchecked_mul(N) }
        };
        // SAFETY: `[T]` is layout-identical to `[T; N]`
        unsafe { from_raw_parts_mut(self.as_mut_ptr().cast(), len) }
    }
}

// from std::hint since 1.89
fn select_unpredictable<T>(b: bool, true_val: T, false_val: T) -> T {
    if b { true_val } else { false_val }
}

#[cfg_attr(not(creusot), derive(Debug))]
#[derive(DeepModel, Clone, PartialEq, Eq)]
pub enum GetDisjointMutError {
    /// An index provided was out-of-bounds for the slice.
    IndexOutOfBounds,
    /// Two indices provided were overlapping.
    OverlappingIndices,
}

pub unsafe trait GetDisjointMutIndex:
    Clone + private_get_disjoint_mut_index::Sealed
{
    /// Returns `true` if `self` is in bounds for `len` slice elements.
    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    fn is_in_bounds(&self, len: usize) -> bool;

    /// Returns `true` if `self` overlaps with `other`.
    ///
    /// Note that we don't consider zero-length ranges to overlap at the beginning or the end,
    /// but do consider them to overlap in the middle.
    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    fn is_overlapping(&self, other: &Self) -> bool;
}

mod private_get_disjoint_mut_index {
    use super::{Range, RangeInclusive, /* range */};

    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    pub trait Sealed {}

    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    impl Sealed for usize {}
    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    impl Sealed for Range<usize> {}
    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    impl Sealed for RangeInclusive<usize> {}
    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    // impl Sealed for range::Range<usize> {}
    // #[unstable(feature = "get_disjoint_mut_helpers", issue = "none")]
    // impl Sealed for range::RangeInclusive<usize> {}
}

/// This checks every index against each other, and against `len`.
///
/// This will do `binomial(N + 1, 2) = N * (N + 1) / 2 = 0, 1, 3, 6, 10, ..`
/// comparison operations.
#[inline]
fn get_disjoint_check_valid<I: GetDisjointMutIndex, const N: usize>(
    indices: &[I; N],
    len: usize,
) -> Result<(), GetDisjointMutError> {
    // NB: The optimizer should inline the loops into a sequence
    // of instructions without additional branching.
    for (i, idx) in indices.iter().enumerate() {
        if !idx.is_in_bounds(len) {
            return Err(GetDisjointMutError::IndexOutOfBounds);
        }
        for idx2 in &indices[..i] {
            if idx.is_overlapping(idx2) {
                return Err(GetDisjointMutError::OverlappingIndices);
            }
        }
    }
    Ok(())
}

// Placeholder for T::IS_ZST
#[trusted]
#[requires(false)]
fn is_zst<T>() -> bool {
    false
}

// The verification must be unbounded---it must hold for slices of arbitrary length.
//
// The verification must hold for generic type T (no monomorphization).
//
// All proofs must automatically ensure the absence of the following undefined behaviors ref:
//
//     Accessing (loading from or storing to) a place that is dangling or based on a misaligned pointer.
//     Reading from uninitialized memory except for padding or unions.
//     Mutating immutable bytes.
//     Producing an invalid value
