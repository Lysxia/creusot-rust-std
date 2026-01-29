//! Slice management and manipulation.
//!
//! For more details see [`std::slice`].
//!
//! [`std::slice`]: ../../std/slice/index.html

// #![stable(feature = "rust1", since = "1.0.0")]

use crate::intrinsics::{exact_div, unchecked_sub};
use crate::ptr::{
    cast_array_perm, cast_array_perm_mut, cast_from_chunks_perm, cast_from_chunks_perm_mut,
};
use core::cmp::Ordering::{self, Equal, Greater, Less};
use core::mem::{self, MaybeUninit, SizedTypeProperties};
use creusot_std::{
    ghost::perm::Perm,
    prelude::{Clone, PartialEq, *},
    std::ops::RangeBounds,
};
// use core::num::NonZero;
use core::ops::{/* OneSidedRange, OneSidedRangeBound, */ Range, RangeInclusive};
// use core::panic::const_panic;
use crate::{
    assert_unsafe_precondition,
    ptr::{self as vptr, PtrAddExt as _},
};
use core::simd::{self, Simd};
use core::{hint /* range, */, ptr};

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
use crate::slice::index::{SliceIndex, range};

use raw::{from_raw_parts, from_raw_parts_mut, from_raw_parts_mut_perm, from_raw_parts_perm};

#[check(ghost)]
#[requires(0 <= i && i < s.len() && 0 <= j && j < s.len() && i != j)]
#[ensures(*result.0.ward() == (*s.ward() as *const T).offset_logic(i))]
#[ensures(*result.1.ward() == (*s.ward() as *const T).offset_logic(j))]
#[ensures(*result.0.val() == s.val()@[i])]
#[ensures(*result.1.val() == s.val()@[j])]
#[ensures(*(^(*result).0).val() == (^*s).val()@[i])]
#[ensures(*(^(*result).1).val() == (^*s).val()@[j])]
#[ensures((^*s).ward() == s.ward())]
#[ensures(forall<k: Int> k != i && k != j ==> (^*s).val()@.get(k) == s.val()@.get(k))]
pub fn block_get_2<T>(
    s: Ghost<&mut Perm<*const [T]>>,
    i: Int,
    j: Int,
) -> Ghost<(&mut Perm<*const T>, &mut Perm<*const T>)> {
    ghost! {
        let _s = snapshot!(s);
        if i < j {
            let (s, sj) = s.into_inner().split_at_mut(j);
            proof_assert!{ forall<k> k < j ==> (^*_s).val()@.get(k) == (^s).val()@.get(k)};
            proof_assert!{ forall<k> k != i && k != j ==> k < i || k > i };
            (s.index_mut(i), sj.index_mut(0int))
        } else {
            let (s, si) = s.into_inner().split_at_mut(i);
            proof_assert!{ forall<k> i < k ==> (^*_s).val()@.get(k) == (^si).val()@.get(k-i)};
            (si.index_mut(0int), s.index_mut(j))
        }
    }
}

// For the following unsafe functions (in library/core/src/slice/mod.rs):
//
//     Write contracts specifying the safety precondition(s) that the caller must uphold, then
//     Verify that if the caller respects those preconditions, the function does not cause undefined behavior.

// #[erasure(<[T]>::get_unchecked::<I>)] TODO
#[requires(index.in_bounds(*self_))]
#[ensures(index.slice_index(*self_, *result))]
pub unsafe fn get_unchecked<T, I>(self_: &[T], index: I) -> &I::Output
where
    I: SliceIndex<[T]>,
{
    let (ptr, perm) = Perm::from_ref(self_);
    // SAFETY: the caller must uphold most of the safety requirements for `get_unchecked`;
    // the slice is dereferenceable because `self` is a safe reference.
    // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
    unsafe {
        let (ptr, perm) = index.get_unchecked_perm(ptr, perm);
        Perm::as_ref(ptr, perm)
    }
}

// #[erasure(<[T]>::get_unchecked_mut::<I>)] TODO
#[requires(index.in_bounds(*self_))]
#[ensures(index.slice_index(*self_, *result))]
#[ensures(index.slice_index(^self_, ^result))]
#[ensures(index.resolve_elsewhere(*self_, ^self_))]
pub unsafe fn get_unchecked_mut<T, I>(self_: &mut [T], index: I) -> &mut I::Output
where
    I: SliceIndex<[T]>,
{
    let (ptr, perm) = Perm::from_mut(self_);
    // SAFETY: the caller must uphold the safety requirements for `get_unchecked_mut`;
    // the slice is dereferenceable because `self` is a safe reference.
    // The returned pointer is safe because impls of `SliceIndex` have to guarantee that it is.
    unsafe {
        let (ptr, perm) = index.get_unchecked_mut_perm(ptr, perm);
        Perm::as_mut(ptr, perm)
    }
}

// `s.exchange(t, i, j)` says precisely that `s: Seq<T>` is the result of exchanging
// elements at indices `i` and `j` in `t`.
#[erasure(<[T]>::swap_unchecked)]
#[requires(a@ < self_@.len() && b@ < self_@.len())]
#[ensures((^self_)@.exchange(self_@, a@, b@))]
pub unsafe fn swap_unchecked<T>(self_: &mut [T], a: usize, b: usize) {
    assert_unsafe_precondition!(
        check_library_ub,
        "slice::swap_unchecked requires that the indices are within the slice",
        pearlite! { a < len && b < len },
        (
            len: usize = self_.len(),
            a: usize = a,
            b: usize = b,
        ) => a < len && b < len,
    );

    let (ptr, perm) = self_.as_mut_ptr_perm();
    let (mut perm, live) = ghost! { perm.into_inner().live_mut() }.split();
    let perm = ghost! {
        if a == b {
            let a_ = Int::new(a as i128).into_inner();
            vptr::DisjointOrEqual::Equal(perm.index_mut(a_))
        } else {
            let a_ = Int::new(a as i128).into_inner();
            let b_ = Int::new(b as i128).into_inner();
            let (perm_a, perm_b) = block_get_2(perm, a_, b_).into_inner();
            vptr::DisjointOrEqual::Disjoint(perm_a, perm_b)
        }
    };

    // SAFETY: caller has to guarantee that `a < self.len()` and `b < self.len()`
    unsafe {
        vptr::swap_disjoint(ptr.add_live(a, live), ptr.add_live(b, live), perm);
    }
}

#[erasure(<[T]>::as_chunks_unchecked::<N>)]
#[requires(N@ != 0 && self_@.len() % N@ == 0)]
#[ensures(result@.len() == self_@.len() / N@)]
#[ensures(forall<i: Int, j: Int>
    0 <= i && i < result@.len() && 0 <= j && j < N@
    ==> result@[i]@[j] == self_@[i * N@ + j]
)]
pub unsafe fn as_chunks_unchecked<T, const N: usize>(self_: &[T]) -> &[[T; N]] {
    assert_unsafe_precondition!(
        check_language_ub,
        "slice::as_chunks_unchecked requires `N != 0` and the slice to split exactly into `N`-element chunks",
        pearlite! { n@ != 0 && len@ % n@ == 0 },
        (n: usize = N, len: usize = self_.len()) => n != 0 && len.is_multiple_of(n),
    );
    // SAFETY: Caller must guarantee that `N` is nonzero and exactly divides the slice length
    let new_len = unsafe { exact_div(self_.len(), N) };
    let (ptr, perm) = self_.as_ptr_perm();
    let perm = ghost! { crate::ptr::cast_chunks_perm(perm.into_inner()) };
    // SAFETY: We cast a slice of `new_len * N` elements into
    // a slice of `new_len` many `N` elements chunks.
    unsafe { from_raw_parts_perm(ptr.cast(), new_len, perm) }
}

#[erasure(<[T]>::as_chunks_unchecked_mut::<N>)]
#[requires(N@ != 0 && self_@.len() % N@ == 0)]
#[ensures(result@.len() == self_@.len() / N@)]
#[ensures(forall<i: Int, j: Int>
    0 <= i && i < result@.len() && 0 <= j && j < N@
    ==> result@[i]@[j] == self_@[i * N@ + j]
)]
#[ensures(self_@.len() == (^self_)@.len())]
#[ensures(forall<i: Int, j: Int>
    0 <= i && i < result@.len() && 0 <= j && j < N@
    ==> (^result)@[i]@[j] == (^self_)@[i * N@ + j]
)]
pub unsafe fn as_chunks_unchecked_mut<T, const N: usize>(self_: &mut [T]) -> &mut [[T; N]] {
    assert_unsafe_precondition!(
        check_language_ub,
        "slice::as_chunks_unchecked requires `N != 0` and the slice to split exactly into `N`-element chunks",
        pearlite! { n@ != 0 && len@ % n@ == 0 },
        (n: usize = N, len: usize = self_.len()) => n != 0 && len.is_multiple_of(n)
    );
    // SAFETY: Caller must guarantee that `N` is nonzero and exactly divides the slice length
    let new_len = unsafe { exact_div(self_.len(), N) };
    let (ptr, perm) = self_.as_mut_ptr_perm();
    let perm = ghost! { crate::ptr::cast_chunks_perm_mut(perm.into_inner()) };
    // SAFETY: We cast a slice of `new_len * N` elements into
    // a slice of `new_len` many `N` elements chunks.
    unsafe { from_raw_parts_mut_perm((ptr as *mut T).cast(), new_len, perm) }
}

#[erasure(<[T]>::split_at)]
#[requires(mid@ <= self_@.len())]
#[ensures(self_@[0..mid@] == result.0@)]
#[ensures(self_@[mid@..self_@.len()] == result.1@)]
pub fn split_at<T>(self_: &[T], mid: usize) -> (&[T], &[T]) {
    match split_at_checked(self_, mid) {
        Some(pair) => pair,
        None => panic!("mid > len"),
    }
}

#[erasure(<[T]>::split_at_mut)]
#[requires(mid@ <= self_@.len())]
#[ensures(self_@[0..mid@] == result.0@)]
#[ensures(self_@[mid@..self_@.len()] == result.1@)]
#[ensures(self_@.len() == (^self_)@.len())]
#[ensures((^self_)@[0..mid@] == (^result.0)@)]
#[ensures((^self_)@[mid@..self_@.len()] == (^result.1)@)]
pub fn split_at_mut<T>(self_: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    match split_at_mut_checked(self_, mid) {
        Some(pair) => pair,
        None => panic!("mid > len"),
    }
}

#[erasure(<[T]>::split_at_unchecked)]
#[requires(mid@ <= self_@.len())]
#[ensures(self_@[0..mid@] == result.0@)]
#[ensures(self_@[mid@..self_@.len()] == result.1@)]
pub unsafe fn split_at_unchecked<T>(self_: &[T], mid: usize) -> (&[T], &[T]) {
    // FIXME(const-hack): the const function `from_raw_parts` is used to make this
    // function const; previously the implementation used
    // `(self.get_unchecked(..mid), self.get_unchecked(mid..))`

    let len = self_.len();
    let (ptr, perm) = self_.as_ptr_perm();
    let (perm0, perm1) = ghost! {
        perm.into_inner().split_at(*Int::new(mid as i128))
    }
    .split();
    assert_unsafe_precondition!(
        check_library_ub,
        "slice::split_at_unchecked requires the index to be within the slice",
        pearlite!{ mid <= len },
        (mid: usize = mid, len: usize = len) => mid <= len,
    );

    // SAFETY: Caller has to check that `0 <= mid <= self.len()`
    unsafe {
        (
            from_raw_parts_perm(ptr, mid, perm0),
            from_raw_parts_perm(
                ptr.add_live(mid, ghost! { perm0.live() }),
                unchecked_sub(len, mid),
                perm1,
            ),
        )
    }
}

/* pub const */
#[erasure(<[T]>::split_at_mut_unchecked)]
#[requires(mid@ <= self_@.len())]
#[ensures(self_@[0..mid@] == result.0@)]
#[ensures(self_@[mid@..self_@.len()] == result.1@)]
#[ensures(self_@.len() == (^self_)@.len())]
#[ensures((^self_)@[0..mid@] == (^result.0)@)]
#[ensures((^self_)@[mid@..self_@.len()] == (^result.1)@)]
unsafe fn split_at_mut_unchecked<T>(self_: &mut [T], mid: usize) -> (&mut [T], &mut [T]) {
    let len = self_.len();
    let (ptr, perm) = self_.as_mut_ptr_perm();
    let (perm, live) = ghost! { perm.into_inner().live_mut() }.split();
    let (perm0, perm1) = ghost! {
        perm.into_inner().split_at_mut(*Int::new(mid as i128))
    }
    .split();

    assert_unsafe_precondition!(
        check_library_ub,
        "slice::split_at_mut_unchecked requires the index to be within the slice",
        pearlite!{ mid <= len },
        (mid: usize = mid, len: usize = len) => mid <= len,
    );

    // SAFETY: Caller has to check that `0 <= mid <= self_.len()`.
    //
    // `[ptr; mid]` and `[mid; len]` are not overlapping, so returning a mutable reference
    // is fine.
    unsafe {
        (
            from_raw_parts_mut_perm(ptr, mid, perm0),
            from_raw_parts_mut_perm(ptr.add_live(mid, live), unchecked_sub(len, mid), perm1),
        )
    }
}

#[trusted] // TODO
/// Function to calculate lengths of the middle and trailing slice for `align_to{,_mut}`.
pub fn align_to_offsets<T, U>(self_: &[T]) -> (usize, usize) {
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
    let us_len = self_.len() / ts * us;
    // And how many `T`s will be in the trailing slice!
    let ts_len = self_.len() % ts;
    (us_len, ts_len)
}

#[trusted] // TODO
pub unsafe fn align_to<T, U>(self_: &[T]) -> (&[T], &[U], &[T]) {
    // Note that most of this function will be constant-evaluated,
    if U::IS_ZST || T::IS_ZST {
        // handle ZSTs specially, which is – don't handle them at all.
        return (self_, &[], &[]);
    }

    // First, find at what point do we split between the first and 2nd slice. Easy with
    // ptr.align_offset.
    let ptr = self_.as_ptr();
    // SAFETY: See the `align_to_mut` method for the detailed safety comment.
    let offset = unsafe { crate::ptr::align_offset(ptr, align_of::<U>()) };
    if offset > self_.len() {
        (self_, &[], &[])
    } else {
        let (left, rest) = self_.split_at(offset);
        let (us_len, ts_len) = align_to_offsets::<T, U>(rest);
        // Inform Miri that we want to consider the "middle" pointer to be suitably aligned.
        #[cfg(miri)]
        crate::intrinsics::miri_promise_symbolic_alignment(rest.as_ptr().cast(), align_of::<U>());
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

#[trusted] // TODO
pub unsafe fn align_to_mut<T, U>(self_: &mut [T]) -> (&mut [T], &mut [U], &mut [T]) {
    // Note that most of this function will be constant-evaluated,
    if U::IS_ZST || T::IS_ZST {
        // handle ZSTs specially, which is – don't handle them at all.
        return (self_, &mut [], &mut []);
    }

    // First, find at what point do we split between the first and 2nd slice. Easy with
    // ptr.align_offset.
    let ptr = self_.as_ptr();
    // SAFETY: Here we are ensuring we will use aligned pointers for U for the
    // rest of the method. This is done by passing a pointer to &[T] with an
    // alignment targeted for U.
    // `crate::ptr::align_offset` is called with a correctly aligned and
    // valid pointer `ptr` (it comes from a reference to `self_`) and with
    // a size that is a power of two (since it comes from the alignment for U),
    // satisfying its safety constraints.
    let offset = unsafe { crate::ptr::align_offset(ptr, align_of::<U>()) };
    if offset > self_.len() {
        (self_, &mut [], &mut [])
    } else {
        let (left, rest) = self_.split_at_mut(offset);
        let (us_len, ts_len) = align_to_offsets::<T, U>(rest);
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

#[allow(unused)] // TODO
#[trusted] // TODO: needs MaybeUninit
// #[erasure(<[T]>::get_disjoint_unchecked_mut::<I, N>)] // TODO: not the same traits
pub unsafe fn get_disjoint_unchecked_mut<T, I, const N: usize>(
    self_: &mut [T],
    indices: [I; N],
) -> [&mut I::Output; N]
where
    I: GetDisjointMutIndex + SliceIndex<[T]>,
{
    // NB: This implementation is written as it is because any variation of
    // `indices.map(|i| self.get_unchecked_mut(i))` would make miri unhappy,
    // or generate worse code otherwise. This is also why we need to go
    // through a raw pointer here.
    let slice: *mut [T] = self_;
    let mut arr: MaybeUninit<[&mut I::Output; N]> = MaybeUninit::uninit();
    let arr_ptr = arr.as_mut_ptr();

    // SAFETY: We expect `indices` to contain disjunct values that are
    // in bounds of `self`.
    unsafe {
        for i in 0..N {
            let idx = indices.get_unchecked(i).clone();
            arr_ptr.cast::<&mut I::Output>().add(i).write(
                // &mut *slice.get_unchecked_mut(idx)
                // &mut *idx.get_unchecked_mut_perm(slice, todo!()),
                todo!(),
            );
        }
        arr.assume_init()
    }
}

// Prove that the following safe abstractions (in library/core/src/slice/mod.rs) do not cause undefined behavior:

// TODO: upstream to creusot-std
extern_spec! {
    impl<T> *const T {
        #[ensures(result as *const T == self)]
        fn cast_array<const N: usize>(self) -> *const [T; N] {
            self.cast()
        }
    }

    impl<T> *mut T {
        #[ensures(result as *mut T == self)]
        fn cast_array<const N: usize>(self) -> *mut [T; N] {
            self.cast()
        }
    }
}

#[erasure(<[T]>::first_chunk::<N>)]
#[ensures(match result {
    None => self_@.len() < N@,
    Some(chunk) => N@ <= self_@.len() && chunk@ == self_@[..N@],
})]
/* pub const */
pub fn first_chunk<T, const N: usize>(self_: &[T]) -> Option<&[T; N]> {
    if self_.len() < N {
        None
    } else {
        let (ptr, perm) = self_.as_ptr_perm();
        let perm = ghost! {
            cast_array_perm(perm.into_inner().split_at(*Int::new(N as i128)).0)
        }; // SAFETY: We explicitly check for the correct number of elements,
        //   and do not let the reference outlive the slice.
        Some(unsafe { Perm::as_ref(ptr.cast_array(), perm) })
    }
}

#[erasure(<[T]>::first_chunk_mut::<N>)]
#[ensures(match result {
    None => self_@.len() < N@ && resolve(self_),
    Some(chunk) => N@ <= self_@.len() && chunk@ == self_@[..N@]
        && (^self_)@ == (^chunk)@.concat(self_@[N@..]),
})]
/* pub const */
pub fn first_chunk_mut<T, const N: usize>(self_: &mut [T]) -> Option<&mut [T; N]> {
    if self_.len() < N {
        None
    } else {
        let (ptr, perm) = self_.as_mut_ptr_perm();
        let perm = ghost! {
            cast_array_perm_mut(perm.into_inner().split_at_mut(*Int::new(N as i128)).0)
        };
        // SAFETY: We explicitly check for the correct number of elements,
        //   do not let the reference outlive the slice,
        //   and require exclusive access to the entire slice to mutate the chunk.
        Some(unsafe { Perm::as_mut(ptr.cast_array(), perm) })
    }
}

#[erasure(<[T]>::split_first_chunk::<N>)]
#[ensures(match result {
    None => self_@.len() < N@,
    Some((first, tail)) => N@ <= self_@.len() && first@ == self_@[..N@] && tail@ == self_@[N@..],
})]
/* pub const */
pub fn split_first_chunk<T, const N: usize>(self_: &[T]) -> Option<(&[T; N], &[T])> {
    let Some((first, tail)) = split_at_checked(self_, N) else {
        return None;
    };

    let (ptr, perm) = first.as_ptr_perm();
    let perm = ghost! { cast_array_perm(perm.into_inner()) };
    // SAFETY: We explicitly check for the correct number of elements,
    //   and do not let the references outlive the slice.
    Some((unsafe { Perm::as_ref(ptr.cast_array(), perm) }, tail))
}

#[erasure(<[T]>::split_first_chunk_mut::<N>)]
#[ensures(match result {
    None => self_@.len() < N@ && resolve(self_),
    Some((first, tail)) => N@ <= self_@.len() && first@ == self_@[..N@] && tail@ == self_@[N@..]
        && (^self_)@.len() == self_@.len() && (^self_)@ == (^first)@.concat((^tail)@),
})]
/* pub const */
pub fn split_first_chunk_mut<T, const N: usize>(
    self_: &mut [T],
) -> Option<(&mut [T; N], &mut [T])> {
    let Some((first, tail)) = split_at_mut_checked(self_, N) else {
        return None;
    };

    let (ptr, perm) = first.as_mut_ptr_perm();
    let perm = ghost! { cast_array_perm_mut(perm.into_inner()) };
    // SAFETY: We explicitly check for the correct number of elements,
    //   do not let the reference outlive the slice,
    //   and enforce exclusive mutability of the chunk by the split.
    Some((unsafe { Perm::as_mut(ptr.cast_array(), perm) }, tail))
}

#[erasure(<[T]>::split_last_chunk::<N>)]
#[ensures(match result {
    None => self_@.len() < N@,
    Some((init, last)) => N@ <= self_@.len() && init@ == self_@[..self_@.len() - N@] && last@ == self_@[self_@.len() - N@..],
})]
/* pub const */
pub fn split_last_chunk<T, const N: usize>(self_: &[T]) -> Option<(&[T], &[T; N])> {
    let Some(index) = self_.len().checked_sub(N) else {
        return None;
    };
    let (init, last) = split_at(self_, index);

    let (ptr, perm) = last.as_ptr_perm();
    let perm = ghost! { cast_array_perm(perm.into_inner()) };
    // SAFETY: We explicitly check for the correct number of elements,
    //   and do not let the references outlive the slice.
    Some((init, unsafe { Perm::as_ref(ptr.cast_array(), perm) }))
}

#[erasure(<[T]>::split_last_chunk_mut::<N>)]
#[ensures(match result {
    None => self_@.len() < N@ && resolve(self_),
    Some((init, last)) => N@ <= self_@.len() && init@ == self_@[..self_@.len() - N@] && last@ == self_@[self_@.len() - N@..]
        && (^self_)@.len() == self_@.len() && (^self_)@ == (^init)@.concat((^last)@),
})]
/* pub const */
pub fn split_last_chunk_mut<T, const N: usize>(self_: &mut [T]) -> Option<(&mut [T], &mut [T; N])> {
    let Some(index) = self_.len().checked_sub(N) else {
        return None;
    };
    let (init, last) = self_.split_at_mut(index);

    let (ptr, perm) = last.as_mut_ptr_perm();
    let perm = ghost! { cast_array_perm_mut(perm.into_inner()) };
    // SAFETY: We explicitly check for the correct number of elements,
    //   do not let the reference outlive the slice,
    //   and enforce exclusive mutability of the chunk by the split.
    Some((init, unsafe { Perm::as_mut(ptr.cast_array(), perm) }))
}

#[erasure(<[T]>::last_chunk::<N>)]
#[ensures(match result {
    None => self_@.len() < N@,
    Some(chunk) => N@ <= self_@.len() && chunk@ == self_@[self_@.len() - N@..],
})]
/* pub const */
pub fn last_chunk<T, const N: usize>(self_: &[T]) -> Option<&[T; N]> {
    // FIXME(const-hack): Without const traits, we need this instead of `get`.
    let Some(index) = self_.len().checked_sub(N) else {
        return None;
    };
    let (_, last) = split_at(self_, index);

    let (ptr, perm) = last.as_ptr_perm();
    let perm = ghost! { cast_array_perm(perm.into_inner()) };
    // SAFETY: We explicitly check for the correct number of elements,
    //   and do not let the references outlive the slice.
    Some(unsafe { Perm::as_ref(ptr.cast_array(), perm) })
}

#[erasure(<[T]>::last_chunk_mut::<N>)]
#[ensures(match result {
    None => self_@.len() < N@ && resolve(self_),
    Some(chunk) => N@ <= self_@.len() && chunk@ == self_@[self_@.len() - N@..]
        && (^self_)@ == self_@[..self_@.len() - N@].concat((^chunk)@),
})]
/* pub const */
pub fn last_chunk_mut<T, const N: usize>(self_: &mut [T]) -> Option<&mut [T; N]> {
    // FIXME(const-hack): Without const traits, we need this instead of `get`.
    let Some(index) = self_.len().checked_sub(N) else {
        return None;
    };
    let (_, last) = split_at_mut(self_, index);

    let (ptr, perm) = last.as_mut_ptr_perm();
    let perm = ghost! { cast_array_perm_mut(perm.into_inner()) };
    // SAFETY: We explicitly check for the correct number of elements,
    //   do not let the reference outlive the slice,
    //   and require exclusive access to the entire slice to mutate the chunk.
    Some(unsafe { Perm::as_mut(ptr.cast_array(), perm) })
}

// #[erasure(<[T]>::as_mut_ptr_range)] // TODO: self.len() is called later in core (in start.add(...)), for now...
#[ensures(*(*result.1).val() == *self_)]
#[ensures(*(^result.1).val() == ^self_)]
#[ensures(result.0.start as *const T == result.1.ward().thin())]
#[ensures(result.0.end as *const T == result.0.start.offset_logic(result.1.len()))]
/* pub const */
pub fn as_mut_ptr_range<T>(self_: &mut [T]) -> (Range<*mut T>, Ghost<&mut Perm<*const [T]>>) {
    let len = self_.len(); // Get the length before borrowing `self_`
    let (start, perm) = self_.as_mut_ptr_perm();
    // SAFETY: See as_ptr_range() above for why `add` here is safe.
    let end = unsafe { start.add_live(len, ghost! { perm.live() }) };
    (start..end, perm)
}

// #[erasure(<[T]>::reverse)] // TODO: (1) Unsupported a[i], (2) lift self.len() to the front
#[ensures((^self_)@ == self_@.reverse())]
/* pub const */
pub fn reverse<T>(self_: &mut [T]) {
    let _old = snapshot! { self_@ };
    let len = self_.len();
    let half_len = len / 2;
    let (Range { start, end }, perm) = as_mut_ptr_range(self_);
    let (perm1, perm2) = ghost! {
        perm.into_inner().split_at_mut(*Int::new(half_len as i128))
    }
    .split();
    let perm2 = ghost! {
        let i = *Int::new((len - 2 * half_len) as i128);
        perm2.into_inner().split_at_mut(i).1
    };
    proof_assert! { perm2.ward().thin().offset_logic(half_len@) == end as *const T };

    // These slices will skip the middle item for an odd length,
    // since that one doesn't need to move.
    let (front_half, back_half) =
        // SAFETY: Both are subparts of the original slice, so the memory
        // range is valid, and they don't overlap because they're each only
        // half (or less) of the original slice.
        unsafe {
            (
                raw::from_raw_parts_mut_perm(start, half_len, perm1),
                raw::from_raw_parts_mut_perm(end.sub_live(half_len, ghost! { perm2.live() }), half_len, perm2),
            )
        };

    proof_assert! { *_old == front_half@.concat(_old[half_len@..len@ - half_len@]).concat(back_half@) };
    proof_assert! { len@ - 2 * half_len@ == 0 || len@ - 2 * half_len@ == 1 };
    proof_assert! { _old[half_len@ .. len@ - half_len@].reverse() == _old[half_len@ .. len@ - half_len@] };
    ghost! { reverse_concat::<T>() };
    proof_assert! { (*_old).reverse() == back_half@.reverse().concat(_old[half_len@..len@ - half_len@]).concat(front_half@.reverse()) };

    // Introducing a function boundary here means that the two halves
    // get `noalias` markers, allowing better optimization as LLVM
    // knows that they're disjoint, unlike in the original slice.
    revswap(front_half, back_half, half_len);

    #[inline]
    #[requires(n@ == a@.len() && n@ == b@.len())]
    #[ensures((^a)@ == (*b)@.reverse())]
    #[ensures((^b)@ == (*a)@.reverse())]
    /* const */
    fn revswap<T>(a: &mut [T], b: &mut [T], n: usize) {
        debug_assert!(a.len() == n);
        debug_assert!(b.len() == n);

        let _a: Snapshot<Seq<T>> = snapshot! { a@ };
        let _b: Snapshot<Seq<T>> = snapshot! { b@ };

        // Because this function is first compiled in isolation,
        // this check tells LLVM that the indexing below is
        // in-bounds. Then after inlining -- once the actual
        // lengths of the slices are known -- it's removed.
        let (a, _) = a.split_at_mut(n);
        let (b, _) = b.split_at_mut(n);

        proof_assert! { forall<s: Seq<T>> s[0..] == s };

        let mut i = 0;
        #[invariant(n@ == a@.len() && n@ == b@.len())]
        #[invariant(i <= n)]
        #[invariant(a@ == _b[(n@ - i@)..].reverse().concat(_a[i@..]))]
        #[invariant(b@ == _b[..(n@ - i@)].concat(_a[..i@].reverse()))]
        while i < n {
            mem::swap(&mut a[i], &mut b[n - 1 - i]);
            proof_assert! { a@ == _b[(n@-i@)..].reverse().push_back(_b[n@-1-i@]).concat(_a[i@+1..]) };
            proof_assert! { b@ == _b[..(n@-1-i@)].push_back(_a[i@]).concat(_a[..i@].reverse()) };
            ghost! { reverse_push::<T>() };
            ghost! { concat_push::<T>() };
            ghost! { snoc_prefix::<T>()};
            ghost! { cons_suffix_of(_b, *Int::new((n-i) as i128)) };
            i += 1;
        }
    }
}

#[check(ghost)]
#[ensures(forall<a: Seq<T>, b> a.concat(b).reverse() == b.reverse().concat(a.reverse()))]
fn reverse_concat<T>() {}

#[check(ghost)]
#[ensures(forall<s: Seq<T>, x> s.push_front(x).reverse() == s.reverse().push_back(x))]
#[ensures(forall<s: Seq<T>, x> s.push_back(x).reverse() == s.reverse().push_front(x))]
fn reverse_push<T>() {}

#[check(ghost)]
#[ensures(forall<s: Seq<T>, x, t: Seq<T>> s.concat(t.push_front(x)) == s.push_back(x).concat(t))]
fn concat_push<T>() {}

#[check(ghost)]
#[requires(0 < i && i <= b.len())]
#[ensures(b[i-1..] == b[i..].push_front(b[i-1]))]
fn cons_suffix_of<T>(b: Snapshot<Seq<T>>, i: Int) {
    let _ = (b, i);
}

#[check(ghost)]
#[ensures(forall<a: Seq<T>, i> 0 <= i && i < a.len() ==> a[..i+1] == a[..i].push_back(a[i]))]
fn snoc_prefix<T>() {}

#[erasure(<[T]>::as_chunks::<N>)]
#[requires(N@ != 0)]
#[ensures(result.0@.len() == self_@.len() / N@)]
#[ensures(result.1@.len() == self_@.len() % N@)]
#[ensures(forall<i, j> 0 <= i && i < self_@.len() / N@ && 0 <= j && j < N@
    ==> result.0@[i]@[j] == self_@[i * N@ + j])]
#[ensures(forall<i> 0 <= i && i < self_@.len() % N@
    ==> result.1@[i] == self_@[self_@.len() / N@ * N@ + i])]
/* pub const */
pub fn as_chunks<T, const N: usize>(self_: &[T]) -> (&[[T; N]], &[T]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len_rounded_dperm = self_.len() / N * N;
    // SAFETY: The rounded-dperm value is always the same or smaller than the
    // original length, and thus must be in-bounds of the slice.
    let (multiple_of_n, remainder) = unsafe { split_at_unchecked(self_, len_rounded_dperm) };
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked(multiple_of_n) };
    proof_assert! {
        forall<i, j, len: Int> 0 <= i && i < len / N@ && 0 <= j && j < N@
        ==> i * N@ + j <= (len / N@ - 1) * N@ + N@
    };
    (array_slice, remainder)
}

#[erasure(<[T]>::as_rchunks::<N>)]
#[requires(N@ != 0)]
#[ensures(result.0@.len() == self_@.len() % N@)]
#[ensures(result.1@.len() == self_@.len() / N@)]
#[ensures(forall<i> 0 <= i && i < self_@.len() % N@
    ==> result.0@[i] == self_@[i])]
#[ensures(forall<i, j> 0 <= i && i < self_@.len() / N@ && 0 <= j && j < N@
    ==> result.1@[i]@[j] == self_@[self_@.len() % N@ + i * N@ + j])]
/* pub const */
pub fn as_rchunks<T, const N: usize>(self_: &[T]) -> (&[T], &[[T; N]]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len = self_.len() / N;
    let (remainder, multiple_of_n) = split_at(self_, self_.len() - len * N);
    let _mn = snapshot! { multiple_of_n@ };
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked(multiple_of_n) };
    proof_assert! {
        forall<i, j, len: Int> 0 <= i && i < len / N@ && 0 <= j && j < N@
        ==> len % N@ + i * N@ + j <= len % N@ + len / N@ * N@ - 1
    };
    proof_assert! { forall<i, j> 0 <= i && i < len@ && 0 <= j && j < N@
    ==> array_slice@[i]@[j] == _mn[i * N@ + j]};
    (remainder, array_slice)
}

#[erasure(<[T]>::as_chunks_mut::<N>)]
#[requires(N@ != 0)]
#[ensures(result.0@.len() == self_@.len() / N@)]
#[ensures(result.1@.len() == self_@.len() % N@)]
#[ensures(forall<i, j> 0 <= i && i < self_@.len() / N@ && 0 <= j && j < N@
    ==> result.0@[i]@[j] == self_@[i * N@ + j])]
#[ensures(forall<i> 0 <= i && i < self_@.len() % N@
    ==> result.1@[i] == self_@[self_@.len() / N@ * N@ + i])]
#[ensures(self_@.len() == (^self_)@.len())]
#[ensures(forall<i, j> 0 <= i && i < self_@.len() / N@ && 0 <= j && j < N@
    ==> (^result.0)@[i]@[j] == (^self_)@[i * N@ + j])]
#[ensures(forall<i> 0 <= i && i < self_@.len() % N@
    ==> (^result.1)@[i] == (^self_)@[self_@.len() / N@ * N@ + i])]
/* pub const */
pub fn as_chunks_mut<T, const N: usize>(self_: &mut [T]) -> (&mut [[T; N]], &mut [T]) {
    assert!(N != 0, "chunk size must be non-zero");
    let len_rounded_dperm = self_.len() / N * N;
    // SAFETY: The rounded-dperm value is always the same or smaller than the
    // original length, and thus must be in-bounds of the slice.
    let (multiple_of_n, remainder) = unsafe { split_at_mut_unchecked(self_, len_rounded_dperm) };
    // SAFETY: We already panicked for zero, and ensured by construction
    // that the length of the subslice is a multiple of N.
    let array_slice = unsafe { as_chunks_unchecked_mut(multiple_of_n) };
    proof_assert! {
        forall<i, j, len: Int> 0 <= i && i < len / N@ && 0 <= j && j < N@
        ==> i * N@ + j <= (len / N@ - 1) * N@ + N@
    };
    (array_slice, remainder)
}

/* pub const */
#[erasure(<[T]>::split_at_checked)]
#[ensures(match result {
    None => mid@ > self_@.len(),
    Some(result) => mid@ <= self_@.len()
        && self_@[0..mid@] == result.0@
        && self_@[mid@..self_@.len()] == result.1@
})]
pub fn split_at_checked<T>(self_: &[T], mid: usize) -> Option<(&[T], &[T])> {
    if mid <= self_.len() {
        // SAFETY: `[ptr; mid]` and `[mid; len]` are inside `self_`, which
        // fulfills the requirements of `split_at_unchecked`.
        Some(unsafe { split_at_unchecked(self_, mid) })
    } else {
        None
    }
}

/* pub const */
#[erasure(<[T]>::split_at_mut_checked)]
#[ensures(match result {
    None => mid@ > self_@.len() && resolve(self_),
    Some(result) => mid@ <= self_@.len()
        && self_@[0..mid@] == result.0@
        && self_@[mid@..self_@.len()] == result.1@
        && self_@.len() == (^self_)@.len()
        && (^self_)@[0..mid@] == (^result.0)@
        && (^self_)@[mid@..self_@.len()] == (^result.1)@
})]
pub fn split_at_mut_checked<T>(self_: &mut [T], mid: usize) -> Option<(&mut [T], &mut [T])> {
    if mid <= self_.len() {
        // SAFETY: `[ptr; mid]` and `[mid; len]` are inside `self_`, which
        // fulfills the requirements of `split_at_unchecked`.
        Some(unsafe { split_at_mut_unchecked(self_, mid) })
    } else {
        None
    }
}

// Try to just prove safety for now
// #[erasure(<[T]>::binary_search_by::<'a, F>)] // TODO: unsupported syntax
#[requires(forall<f2, x: T> f.hist_inv(f2) && self_@.contains(x) ==> f2.precondition((&x,)))]
pub fn binary_search_by<'a, T, F>(self_: &'a [T], mut f: F) -> Result<usize, usize>
where
    F: FnMut(&'a T) -> Ordering,
{
    let mut size = self_.len();
    if size == 0 {
        return Err(0);
    }
    let mut base = 0usize;

    let _f0 = snapshot! { f };
    // This loop intentionally doesn't have an early exit if the comparison
    // returns Equal. We want the number of loop iterations to depend *only*
    // on the size of the input slice so that the CPU can reliably predict
    // the loop count.
    #[invariant(base@ < self_@.len() && base@ + size@ <= self_@.len())]
    #[invariant(_f0.hist_inv(f))]
    #[variant(size@)]
    while size > 1 {
        let half = size / 2;
        let mid = base + half;

        // SAFETY: the call is made safe by the following invariants:
        // - `mid >= 0`: by definition
        // - `mid < size`: `mid = size / 2 + size / 4 + size / 8 ...`
        let cmp = f(unsafe { self_.get_unchecked(mid) });

        // Binary search interacts poorly with branch prediction, so force
        // the compiler to use conditional moves if supported by the target
        // architecture.
        base = select_unpredictable(cmp == Greater, base, mid);

        // This is imprecise in the case where `size` is odd and the
        // comparison returns Greater: the mid element still gets included
        // by `size` even though it's knperm to be larger than the element
        // being searched for.
        //
        // This is fine though: we gain more performance by keeping the
        // loop iteration count invariant (and thus predictable) than we
        // lose from considering one additional element.
        size -= half;
    }

    // SAFETY: base is always in [0, size) because base <= mid.
    let cmp = f(unsafe { self_.get_unchecked(base) });
    if cmp == Equal {
        // SAFETY: same as the `get_unchecked` above.
        unsafe { hint::assert_unchecked(base < self_.len()) };
        Ok(base)
    } else {
        let result = base + (cmp == Less) as usize;
        // SAFETY: same as the `get_unchecked` above.
        // Note that this is `<=`, unlike the assume in the `Ok` path.
        unsafe { hint::assert_unchecked(result <= self_.len()) };
        Err(result)
    }
}

#[requires(forall<f2, x: &mut T, y: &mut T> same_bucket.hist_inv(f2) ==> f2.precondition((x, y)))]
pub fn partition_dedup_by<T, F>(self_: &mut [T], mut same_bucket: F) -> (&mut [T], &mut [T])
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

    let len = self_.len();
    if len <= 1 {
        return (self_, &mut []);
    }

    let (ptr, mut perm) = self_.as_mut_ptr_perm();
    let _perm = snapshot! { perm };
    let mut next_read: usize = 1;
    let mut next_write: usize = 1;

    let _same_bucket = snapshot! { same_bucket };

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
        #[invariant(perm.ward().thin() == ptr)]
        #[invariant(perm.len() == len@)]
        #[invariant(^perm == ^_perm)]
        #[invariant(1 <= next_write@ && next_write@ <= next_read@ && next_read@ <= len@)]
        #[invariant(_same_bucket.hist_inv(same_bucket))]
        while next_read < len {
            let (mut perm, live) = ghost! { perm.live_mut() }.split();
            let (perm0, perm1) = ghost! { perm.split_at_mut(*Int::new(next_read as i128)) }.split();
            let ptr_read = ptr.add_live(next_read, live);
            let prev_ptr_write = ptr.add_live(next_write - 1, live);
            let mut read_perm = ghost! { perm1.into_inner().index_mut(0int) };
            let (prev_write_perm, write_perm) = ghost! { perm0.into_inner().split_at_mut(*Int::new(next_write as i128 - 1)).1.split_at_mut(1int) }.split();
            let prev_write_perm = ghost! { prev_write_perm.into_inner().index_mut(0int) };
            if !same_bucket(
                Perm::as_mut(ptr_read, ghost! { *read_perm }),
                Perm::as_mut(prev_ptr_write, prev_write_perm),
            ) {
                if next_read != next_write {
                    let ptr_write = prev_ptr_write.add_live(1, live);
                    let write_perm = ghost! { write_perm.into_inner().index_mut(0int) };
                    mem::swap(
                        Perm::as_mut(ptr_read, read_perm),
                        Perm::as_mut(ptr_write, write_perm),
                    );
                }
                next_write += 1;
            }
            next_read += 1;
        }
    }

    self_.split_at_mut(next_write)
}

#[trusted] // TODO
pub fn rotate_left<T>(self_: &mut [T], mid: usize) {
    assert!(mid <= self_.len());
    let k = self_.len() - mid;
    let p = self_.as_mut_ptr();

    // SAFETY: The range `[p.add(mid) - mid, p.add(mid) + k)` is trivially
    // valid for reading and writing, as required by `ptr_rotate`.
    unsafe {
        rotate::ptr_rotate(mid, p.add(mid), k);
    }
}

#[trusted] // TODO
pub fn rotate_right<T>(self_: &mut [T], k: usize) {
    assert!(k <= self_.len());
    let mid = self_.len() - k;
    let p = self_.as_mut_ptr();

    // SAFETY: The range `[p.add(mid) - mid, p.add(mid) + k)` is trivially
    // valid for reading and writing, as required by `ptr_rotate`.
    unsafe {
        rotate::ptr_rotate(mid, p.add(mid), k);
    }
}

// #[erasure(<[T]>::copy_from_slice)] // TODO: reordered self.len()
#[requires(self_@.len() == src@.len())]
#[ensures((^self_)@ == src@)]
/* pub const */
pub fn copy_from_slice<T>(self_: &mut [T], src: &[T])
where
    T: Copy,
{
    // The panic code path was put into a cold function to not bloat the
    // call site.
    // #[cfg_attr(not(feature = "panic_immediate_abort"), inline(never), cold)]
    // #[cfg_attr(feature = "panic_immediate_abort", inline)]
    #[track_caller]
    #[allow(unused_variables)]
    #[requires(false)]
    const fn len_mismatch_fail(dst_len: usize, src_len: usize) -> ! {
        // const_panic!(
        //     "copy_from_slice: source slice length does not match destination slice length",
        //     "copy_from_slice: source slice length ({src_len}) does not match destination slice length ({dst_len})",
        //     src_len: usize,
        //     dst_len: usize,
        // )
        panic!()
    }

    if self_.len() != src.len() {
        len_mismatch_fail(self_.len(), src.len());
    }

    let len = self_.len();
    let (src_ptr, src_perm) = src.as_ptr_perm();
    let (dst_ptr, dst_perm) = self_.as_mut_ptr_perm();
    // SAFETY: `self` is valid for `self.len()` elements by definition, and `src` was
    // checked to have the same length. The slices cannot overlap because
    // mutable references are exclusive.
    unsafe {
        crate::ptr::copy_nonoverlapping(src_ptr, dst_ptr, len, src_perm, dst_perm);
    }
}

#[trusted] // TODO
pub fn copy_within<T, R: RangeBounds<usize>>(self_: &mut [T], src: R, dest: usize)
where
    T: Copy,
{
    let Range {
        start: src_start,
        end: src_end,
    } = range(src, ..self_.len());
    let count = src_end - src_start;
    assert!(dest <= self_.len() - count, "dest is out of bounds");
    // SAFETY: the conditions for `ptr::copy` have all been checked above,
    // as have those for `ptr::add`.
    unsafe {
        // Derive both `src_ptr` and `dest_ptr` from the same loan
        let ptr = self_.as_mut_ptr();
        let src_ptr = ptr.add(src_start);
        let dest_ptr = ptr.add(dest);
        ptr::copy(src_ptr, dest_ptr, count);
    }
}

#[trusted] // TODO
pub fn swap_with_slice<T>(self_: &mut [T], other: &mut [T]) {
    assert!(
        self_.len() == other.len(),
        "destination and source slices have different lengths"
    );
    // SAFETY: `self` is valid for `self.len()` elements by definition, and `src` was
    // checked to have the same length. The slices cannot overlap because
    // mutable references are exclusive.
    unsafe {
        ptr::swap_nonoverlapping(self_.as_mut_ptr(), other.as_mut_ptr(), self_.len());
    }
}

#[trusted] // TODO
pub fn as_simd<T, const LANES: usize>(self_: &[T]) -> (&[T], &[Simd<T, LANES>], &[T])
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
    unsafe { self_.align_to() }
}

#[trusted] // TODO
pub fn as_simd_mut<T, const LANES: usize>(
    self_: &mut [T],
) -> (&mut [T], &mut [Simd<T, LANES>], &mut [T])
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
    unsafe { self_.align_to_mut() }
}

#[trusted] // TODO
// #[erasure(<[T]>::get_disjoint_mut::<I, N>)] // TODO: not the same traits
pub fn get_disjoint_mut<T, I, const N: usize>(
    self_: &mut [T],
    indices: [I; N],
) -> Result<[&mut I::Output; N], GetDisjointMutError>
where
    I: GetDisjointMutIndex + SliceIndex<[T]>,
{
    get_disjoint_check_valid(&indices, self_.len())?;
    // SAFETY: The `get_disjoint_check_valid()` call checked that all indices
    // are disjunct and in bounds.
    unsafe { Ok(get_disjoint_unchecked_mut(self_, indices)) }
}

pub trait ArraySliceExt<T, const N: usize> {
    fn as_flattened(&self) -> &[T];
    fn as_flattened_mut(&mut self) -> &mut [T];
}

#[erasure(<[[T; N]]>::as_flattened)]
#[ensures(result@ == self_@.flat_map(|chunk: [T; N]| chunk@))]
pub fn as_flattened<T, const N: usize>(self_: &[[T; N]]) -> &[T] {
    let len = if T::IS_ZST {
        self_.len().checked_mul(N).expect("slice len overflow")
    } else {
        // SAFETY: `self.len() * N` cannot overflow because `self` is
        // already in the address space.
        unsafe { self_.len().unchecked_mul(N) }
    };
    let (ptr, perm) = self_.as_ptr_perm();
    let perm = ghost! { cast_from_chunks_perm(perm.into_inner()) };
    // SAFETY: `[T]` is layout-identical to `[T; N]`
    unsafe { from_raw_parts_perm(ptr.cast(), len, perm) }
}

#[erasure(<[[T; N]]>::as_flattened_mut)]
#[ensures(result@ == self_@.flat_map(|chunk: [T; N]| chunk@))]
#[ensures((^self_)@.len() == self_@.len())]
#[ensures(forall<i> 0 <= i && i < self_@.len() ==> (^self_)@[i]@ == (^result)@[N@ * i..N@ * i + N@])]
pub fn as_flattened_mut<T, const N: usize>(self_: &mut [[T; N]]) -> &mut [T] {
    let len = if T::IS_ZST {
        self_.len().checked_mul(N).expect("slice len overflow")
    } else {
        // SAFETY: `self.len() * N` cannot overflow because `self` is
        // already in the address space.
        unsafe { self_.len().unchecked_mul(N) }
    };
    let (ptr, perm) = self_.as_mut_ptr_perm();
    let perm = ghost! { cast_from_chunks_perm_mut(perm.into_inner()) };
    // SAFETY: `[T]` is layout-identical to `[T; N]`
    unsafe { from_raw_parts_mut_perm(ptr.cast(), len, perm) }
}

#[ensures(result == if b { true_val } else { false_val })]
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
    use super::{Range, RangeInclusive /* range */};

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

#[trusted] // TODO
/// This checks every index against each other, and against `len`.
///
/// This will do `binomial(N + 1, 2) = N * (N + 1) / 2 = 0, 1, 3, 6, 10, ..`
/// comparison operations.
#[inline]
pub fn get_disjoint_check_valid<I: GetDisjointMutIndex, const N: usize>(
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
