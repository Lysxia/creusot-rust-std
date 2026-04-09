use crate::ptr::{PtrAddExt as _, read, write};
use core::mem::MaybeUninit;
use core::mem::SizedTypeProperties as _;
use core::{cmp, ptr};
#[cfg(creusot)]
use creusot_std::std::mem::size_of_logic;
use creusot_std::{ghost::perm::Perm, prelude::*};

type BufType = [usize; 32];

extern_spec! {
    mod core {
        mod intrinsics {
            #[check(terminates)]
            #[ensures(result@ == size_of_logic::<T>())]
            fn size_of<T>() -> usize;
        }
    }
}

/// Rotates the range `[mid-left, mid+right)` such that the element at `mid` becomes the first
/// element. Equivalently, rotates the range `left` elements to the left or `right` elements to the
/// right.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
// #[erasure(private core::slice::rotate::ptr_rotate)] // TODO: erase flag()
#[requires(mid as *const T == perm.ward().thin().offset_logic(left@))]
#[requires(left@ + right@ == perm.len())]
// Needs proof for ptr_rotate_gcd
// #[ensures((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@]))]
#[inline]
pub(super) unsafe fn ptr_rotate<T>(
    left: usize,
    mid: *mut T,
    right: usize,
    perm: Ghost<&mut Perm<*const [T]>>,
) {
    if T::IS_ZST {
        #[trusted]
        proof_assert!(false);
        return;
    }
    // abort early if the rotate is a no-op
    if (left == 0) || (right == 0) {
        return;
    }
    // `T` is not a zero-sized type, so it's okay to divide by its size.
    if flag(!cfg!(feature = "optimize_for_size"))
        && cmp::min(left, right) <= size_of::<BufType>() / size_of::<T>()
    {
        // SAFETY: guaranteed by the caller
        unsafe { ptr_rotate_memmove(left, mid, right, perm) };
    } else if flag(!cfg!(feature = "optimize_for_size"))
        && ((left + right < 24) || (size_of::<T>() > size_of::<[usize; 4]>()))
    {
        // SAFETY: guaranteed by the caller
        unsafe { ptr_rotate_gcd(left, mid, right, perm) }
    } else {
        // SAFETY: guaranteed by the caller
        unsafe { ptr_rotate_swap(left, mid, right, perm) }
    }
}

/// Hide the actual value of a compile-time flag to verify both code paths at the same time
fn flag(b: bool) -> bool {
    b
}

/// Algorithm 1 is used if `min(left, right)` is small enough to fit onto a stack buffer. The
/// `min(left, right)` elements are copied onto the buffer, `memmove` is applied to the others, and
/// the ones on the buffer are moved back into the hole on the opposite side of where they
/// originated.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
#[trusted]
#[erasure(private core::slice::rotate::ptr_rotate_memmove)]
#[inline]
#[requires(mid as *const T == perm.ward().thin().offset_logic(left@))]
#[requires(left@ + right@ == perm.len())]
#[ensures((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@]))]
unsafe fn ptr_rotate_memmove<T>(
    left: usize,
    mid: *mut T,
    right: usize,
    perm: Ghost<&mut Perm<*const [T]>>,
) {
    // The `[T; 0]` here is to ensure this is appropriately aligned for T
    let mut rawarray = MaybeUninit::<(BufType, [T; 0])>::uninit();
    let buf = rawarray.as_mut_ptr() as *mut T;
    // SAFETY: `mid-left <= mid-left+right < mid+right`
    let dim = unsafe { mid.sub(left).add(right) };
    if left <= right {
        // SAFETY:
        //
        // 1) The `if` condition about the sizes ensures `[mid-left; left]` will fit in
        //    `buf` without overflow and `buf` was created just above and so cannot be
        //    overlapped with any value of `[mid-left; left]`
        // 2) [mid-left, mid+right) are all valid for reading and writing and we don't care
        //    about overlaps here.
        // 3) The `if` condition about `left <= right` ensures writing `left` elements to
        //    `dim = mid-left+right` is valid because:
        //    - `buf` is valid and `left` elements were written in it in 1)
        //    - `dim+left = mid-left+right+left = mid+right` and we write `[dim, dim+left)`
        unsafe {
            // 1)
            ptr::copy_nonoverlapping(mid.sub(left), buf, left);
            // 2)
            ptr::copy(mid, mid.sub(left), right);
            // 3)
            ptr::copy_nonoverlapping(buf, dim, left);
        }
    } else {
        // SAFETY: same reasoning as above but with `left` and `right` reversed
        unsafe {
            ptr::copy_nonoverlapping(mid, buf, right);
            ptr::copy(mid.sub(left), dim, left);
            ptr::copy_nonoverlapping(buf, mid.sub(left), right);
        }
    }
}

/// Algorithm 2 is used for small values of `left + right` or for large `T`. The elements
/// are moved into their final positions one at a time starting at `mid - left` and advancing by
/// `right` steps modulo `left + right`, such that only one temporary is needed. Eventually, we
/// arrive back at `mid - left`. However, if `gcd(left + right, right)` is not 1, the above steps
/// skipped over elements. For example:
/// ```text
/// left = 10, right = 6
/// the `^` indicates an element in its final place
/// 6 7 8 9 10 11 12 13 14 15 . 0 1 2 3 4 5
/// after using one step of the above algorithm (The X will be overwritten at the end of the round,
/// and 12 is stored in a temporary):
/// X 7 8 9 10 11 6 13 14 15 . 0 1 2 3 4 5
///               ^
/// after using another step (now 2 is in the temporary):
/// X 7 8 9 10 11 6 13 14 15 . 0 1 12 3 4 5
///               ^                 ^
/// after the third step (the steps wrap around, and 8 is in the temporary):
/// X 7 2 9 10 11 6 13 14 15 . 0 1 12 3 4 5
///     ^         ^                 ^
/// after 7 more steps, the round ends with the temporary 0 getting put in the X:
/// 0 7 2 9 4 11 6 13 8 15 . 10 1 12 3 14 5
/// ^   ^   ^    ^    ^       ^    ^    ^
/// ```
/// Fortunately, the number of skipped over elements between finalized elements is always equal, so
/// we can just offset our starting position and do more rounds (the total number of rounds is the
/// `gcd(left + right, right)` value). The end result is that all elements are finalized once and
/// only once.
///
/// Algorithm 2 can be vectorized by chunking and performing many rounds at once, but there are too
/// few rounds on average until `left + right` is enormous, and the worst case of a single
/// round is always there.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
#[erasure(private core::slice::rotate::ptr_rotate_gcd)]
#[requires(left@ != 0 && right@ != 0)]
#[requires(mid as *const T == perm.ward().thin().offset_logic(left@))]
#[requires(left@ + right@ == perm.len())]
// #[ensures((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@]))]
#[inline]
unsafe fn ptr_rotate_gcd<T>(
    left: usize,
    mid: *mut T,
    right: usize,
    mut perm: Ghost<&mut Perm<*const [T]>>,
) {
    use split::Split;
    // Algorithm 2
    // Microbenchmarks indicate that the average performance for random shifts is better all
    // the way until about `left + right == 32`, but the worst case performance breaks even
    // around 16. 24 was chosen as middle ground. If the size of `T` is larger than 4
    // `usize`s, this algorithm also outperforms other algorithms.
    // SAFETY: callers must ensure `mid - left` is valid for reading and writing.
    let live = ghost! { perm.live_mut() };
    let x = unsafe { mid.sub_live(left, live) };
    // beginning of first round
    // SAFETY: see previous comment.
    let (perm0, mut perm1) = ghost! {
        Split::new(ghost! { *perm }, 0).into_inner()
    }
    .split();
    let (mut tmp, perm0) = unsafe { read(x, perm0) };
    let mut i = right;
    // `gcd` can be found before hand by calculating `gcd(left + right, right)`,
    // but it is faster to do one loop which calculates the gcd as a side effect, then
    // doing the rest of the chunk
    let mut gcd = right;
    // benchmarks reveal that it is faster to swap temporaries all the way through instead
    // of reading one temporary once, copying backwards, and then writing that temporary at
    // the very end. This is possibly due to the fact that swapping or replacing temporaries
    // uses only one memory address in the loop instead of needing to manage two.
    #[invariant(inv(tmp))]
    #[invariant(0 < i@ && i@ < live.len()@)]
    #[invariant(perm1.len() == live.len()@)]
    #[invariant(perm1.ix() == 0usize)]
    #[invariant(perm1.base() == x as *const T)]
    #[invariant(0usize < gcd && gcd <= right && gcd <= i)]
    loop {
        // [long-safety-expl]
        // SAFETY: callers must ensure `[left, left+mid+right)` are all valid for reading and
        // writing.
        //
        // - `i` start with `right` so `mid-left <= x+i = x+right = mid-left+right < mid+right`
        // - `i <= left+right-1` is always true
        //   - if `i < left`, `right` is added so `i < left+right` and on the next
        //     iteration `left` is removed from `i` so it doesn't go further
        //   - if `i >= left`, `left` is removed immediately and so it doesn't go further.
        // - overflows cannot happen for `i` since the function's safety contract ask for
        //   `mid+right-1 = x+left+right` to be valid for writing
        // - underflows cannot happen because `i` must be bigger or equal to `left` for
        //   a subtraction of `left` to happen.
        //
        // So `x+i` is valid for reading and writing if the caller respected the contract
        let perm1 = ghost! {
            Split::index_mut(ghost! { &mut *perm1 }, i).into_inner()
        };
        tmp = unsafe { replace(x.add_live_(i, live), tmp, perm1) };
        // instead of incrementing `i` and then checking if it is outside the bounds, we
        // check if `i` will go outside the bounds on the next increment. This prevents
        // any wrapping of pointers or `usize`.
        if i >= left {
            i -= left;
            if i == 0 {
                // end of first round
                // SAFETY: tmp has been read from a valid source and x is valid for writing
                // according to the caller.
                unsafe { write(x, tmp, perm0) };
                break;
            }
            // this conditional must be here if `left + right >= 15`
            if i < gcd {
                gcd = i;
            }
        } else {
            i += right;
        }
    }
    proof_assert! { gcd <= left && gcd <= right };
    // finish the chunk with more rounds
    // FIXME(const-hack): Use `for start in 1..gcd` when available in const
    let mut start = 1;
    #[invariant(1usize <= start && start <= gcd)]
    #[invariant(left@ + right@ == perm.len())]
    #[invariant(perm.ward().thin() == live.ward())]
    while start < gcd {
        let (perm0_, mut perm1) = ghost! {
            Split::new(ghost! { *perm }, start).into_inner()
        }
        .split();
        proof_assert! { *perm0_.ward() == live.ward().offset_logic(start@) };
        // SAFETY: `gcd` is at most equal to `right` so all values in `1..gcd` are valid for
        // reading and writing as per the function's safety contract, see [long-safety-expl]
        // above
        let (tmp_, perm0) = unsafe { read(x.add_live_(start, live), perm0_) };
        tmp = tmp_;
        // [safety-expl-addition]
        //
        // Here `start < gcd` so `start < right` so `i < right+right`: `right` being the
        // greatest common divisor of `(left+right, right)` means that `left = right` so
        // `i < left+right` so `x+i = mid-left+i` is always valid for reading and writing
        // according to the function's safety contract.
        i = start + right;
        #[invariant(inv(tmp))]
        #[invariant(0 <= i@ && i@ < live.len()@)]
        #[invariant(i != start)]
        #[invariant(perm1.len() == live.len()@)]
        #[invariant(perm1.ix() == start)]
        #[invariant(perm1.base() == x as *const T)]
        loop {
            // SAFETY: see [long-safety-expl] and [safety-expl-addition]
            let perm1 = ghost! {
                Split::index_mut(ghost! { &mut *perm1 }, i).into_inner()
            };
            tmp = unsafe { replace(x.add_live(i, live), tmp, perm1) };
            if i >= left {
                i -= left;
                if i == start {
                    // SAFETY: see [long-safety-expl] and [safety-expl-addition]
                    unsafe { write(x.add_live(start, live), tmp, perm0) };
                    break;
                }
            } else {
                i += right;
            }
        }
        start += 1;
    }
}

mod split {
    use creusot_std::{ghost::perm::Perm, prelude::*};

    pub struct Split<'a, T>(usize, &'a mut Perm<*const [T]>, &'a mut Perm<*const [T]>);

    impl<'a, T> Invariant for Split<'a, T> {
        #[logic]
        fn invariant(self) -> bool {
            pearlite! {
                self.1.len() == self.0@
                && self.2.ward().thin() == self.base().offset_logic(self.0@ + 1)
            }
        }
    }

    impl<'a, T> Split<'a, T> {
        #[logic]
        pub fn len(self) -> Int {
            pearlite! {
                self.1.len() + self.2.len() + 1
            }
        }

        #[logic]
        pub fn base(self) -> *const T {
            pearlite! {
                self.1.ward().thin()
            }
        }

        #[logic]
        pub fn ix(self) -> usize {
            self.0
        }

        #[check(ghost)]
        #[requires(i@ < perm.len())]
        #[ensures((^perm).ward() == (*perm).ward())]
        #[ensures((*result).1.len() == perm.len())]
        #[ensures((*result).1.ix() == i)]
        #[ensures(*(*result).0.ward() == (*perm).ward().thin().offset_logic(i@))]
        #[ensures((*result).1.base() == perm.ward().thin())]
        pub fn new(
            perm: Ghost<&'a mut Perm<*const [T]>>,
            i: usize,
        ) -> Ghost<(&'a mut Perm<*const T>, Self)> {
            ghost! {
                let (left, right) = perm.into_inner().split_at_mut(*Int::new(i as i128));
                let (pi, right) = right.split_at_mut(1int);
                (pi.index_mut(0int), Split(i, left, right))
            }
        }

        #[check(ghost)]
        #[requires(i@ < self_.len() && i != self_.ix())]
        #[ensures((^self_).len() == (*self_).len())]
        #[ensures((^self_).base() == (*self_).base())]
        #[ensures((^self_).ix() == (*self_).ix())]
        #[ensures(*result.ward() == self_.base().offset_logic(i@))]
        pub fn index_mut<'b>(
            self_: Ghost<&'b mut Self>,
            i: usize,
        ) -> Ghost<&'b mut Perm<*const T>> {
            ghost! {
                let j = self_.0;
                if i < j {
                    self_.into_inner().1.index_mut(*Int::new(i as i128))
                } else {
                    self_.into_inner().2.index_mut(*Int::new((i - j - 1) as i128))
                }
            }
        }
    }
}

#[trusted] // Axiomatization of std's replace
#[erasure(<*mut T>::replace)]
#[requires(src as *const T == *perm.ward())]
#[ensures(dst == *(^perm).val())]
#[ensures(result == *perm.val())]
unsafe fn replace<T>(src: *mut T, dst: T, _perm: Ghost<&mut Perm<*const T>>) -> T {
    unsafe { src.replace(dst) }
}

/// Algorithm 3 utilizes repeated swapping of `min(left, right)` elements.
///
/// ///
/// ```text
/// left = 11, right = 4
/// [4 5 6 7 8 9 10 11 12 13 14 . 0 1 2 3]
///                  ^  ^  ^  ^   ^ ^ ^ ^ swapping the right most elements with elements to the left
/// [4 5 6 7 8 9 10 . 0 1 2 3] 11 12 13 14
///        ^ ^ ^  ^   ^ ^ ^ ^ swapping these
/// [4 5 6 . 0 1 2 3] 7 8 9 10 11 12 13 14
/// we cannot swap any more, but a smaller rotation problem is left to solve
/// ```
/// when `left < right` the swapping happens from the left instead.
///
/// # Safety
///
/// The specified range must be valid for reading and writing.
#[erasure(private core::slice::rotate::ptr_rotate_swap)]
#[requires(mid as *const T == perm.ward().thin().offset_logic(left@))]
#[requires(left@ + right@ == perm.len())]
#[ensures((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@]))]
#[inline]
unsafe fn ptr_rotate_swap<T>(
    mut left: usize,
    mut mid: *mut T,
    mut right: usize,
    mut perm: Ghost<&mut Perm<*const [T]>>,
) {
    let _perm0: Snapshot<&mut Perm<*const [T]>> = snapshot! { *perm };
    let _left0: Snapshot<Int> = snapshot! { left@ };
    #[invariant(mid as *const T == perm.ward().thin().offset_logic(left@))]
    #[invariant(left@ + right@ == perm.len())]
    #[invariant((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@])
        ==> (^_perm0).val()@ == (*_perm0).val()@[*_left0..].concat((*_perm0).val()@[..*_left0]))]
    loop {
        if left >= right {
            // Algorithm 3
            // There is an alternate way of swapping that involves finding where the last swap
            // of this algorithm would be, and swapping using that last chunk instead of swapping
            // adjacent chunks like this algorithm is doing, but this way is still faster.
            #[invariant(left >= right)]
            #[invariant(mid as *const T == perm.ward().thin().offset_logic(left@))]
            #[invariant(left@ + right@ == perm.len())]
            #[invariant((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@])
                ==> (^_perm0).val()@ == (*_perm0).val()@[*_left0..].concat((*_perm0).val()@[..*_left0]))]
            loop {
                let _perm: Snapshot<&mut Perm<*const [T]>> = snapshot! { *perm };
                let (mut perm01, perm2) = ghost! {
                    perm.into_inner().split_at_mut(*Int::new(left as i128))
                }
                .split();
                let mut perm1 = ghost! {
                    perm01.split_at_mut(*Int::new((left - right) as i128)).1
                };
                let live = ghost! { perm1.live_mut() };
                ghost! { ptr_rotate_swap_lemma_for_sub_live(mid, right, &live) };
                // SAFETY:
                // `left >= right` so `[mid-right, mid+right)` is valid for reading and writing
                // Subtracting `right` from `mid` each turn is counterbalanced by the addition and
                // check after it.
                unsafe {
                    crate::ptr::swap_nonoverlapping(
                        mid.sub_live(right, live),
                        mid,
                        right,
                        ghost! { *perm1 },
                        perm2,
                    );
                    mid = mid.sub_live(right, live);
                }
                perm = perm01; // ghost
                let _left = snapshot!(left);
                left -= right;
                ghost! { ptr_rotate_swap_lemma(left, *_left.into_ghost(), _perm, snapshot!(*perm)) };
                if left < right {
                    break;
                }
            }
        } else {
            // Algorithm 3, `left < right`
            #[invariant(left <= right)]
            #[invariant(mid as *const T == perm.ward().thin().offset_logic(left@))]
            #[invariant(left@ + right@ == perm.len())]
            #[invariant((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@])
                ==> (^_perm0).val()@ == (*_perm0).val()@[*_left0..].concat((*_perm0).val()@[..*_left0]))]
            loop {
                let _perm: Snapshot<&mut Perm<*const [T]>> = snapshot! { *perm };
                let (perm0, mut perm12) = ghost! {
                    perm.into_inner().split_at_mut(*Int::new(left as i128))
                }
                .split();
                let mut perm1 = ghost! {
                    perm12.split_at_mut(*Int::new(left as i128)).0
                };
                // SAFETY: `[mid-left, mid+left)` is valid for reading and writing because
                // `left < right` so `mid+left < mid+right`.
                // Adding `left` to `mid` each turn is counterbalanced by the subtraction and check
                // after it.
                unsafe {
                    crate::ptr::swap_nonoverlapping(
                        mid.sub_live(left, ghost! { perm0.live() }),
                        mid,
                        left,
                        perm0,
                        ghost! { *perm1 },
                    );
                    mid = mid.add_live_(left, ghost! { perm1.live() });
                }
                perm = perm12; // ghost
                right -= left;
                ghost! { ptr_rotate_swap_lemma2::<T>(left, _perm, snapshot!(*perm)) };
                if right < left {
                    break;
                }
            }
        }
        if (right == 0) || (left == 0) {
            proof_assert! { forall<s: Seq<T>> s[s.len()..] == Seq::empty() };
            proof_assert! { forall<s: Seq<T>> s[..s.len()] == s };
            proof_assert! { forall<s: Seq<T>> Seq::empty().concat(s) == s };
            proof_assert! { forall<s: Seq<T>> s.concat(Seq::empty()) == s };
            return;
        }
    }
}

#[check(ghost)]
#[requires(mid as *const T == live.ward().offset_logic(len@))]
#[requires(len == live.len())]
#[ensures(live.contains_range(mid as *const T, - len@))]
fn ptr_rotate_swap_lemma_for_sub_live<T>(
    mid: *mut T,
    len: usize,
    live: &Ghost<creusot_std::std::ptr::PtrLive<T>>,
) {
    let _ = (mid, len, live);
}

#[check(ghost)]
#[requires(left <= len && len@ == perm.len() && prev.len() == perm.len() + len@ - left@)]
#[requires((^prev).len() == prev.len())]
#[requires(perm.val()@[..left@] == prev.val()@[..left@])]
#[requires(perm.val()@[left@..] == prev.val()@[len@..])]
#[requires((^prev).val()@[len@..] == prev.val()@[left@..len@])]
#[requires((^prev).val()@[..len@] == (^perm).val()@)]
#[ensures((^perm).val()@ == perm.val()@[left@..].concat(perm.val()@[..left@])
    ==> (^prev).val()@ == (*prev).val()@[len@..].concat((*prev).val()@[..len@]))]
fn ptr_rotate_swap_lemma<T>(
    left: usize,
    len: usize,
    prev: Snapshot<&mut Perm<*const [T]>>,
    perm: Snapshot<&mut Perm<*const [T]>>,
) {
    let _ = (left, len, prev, perm);
    proof_assert! { (^prev).val()@ == (^prev).val()@[..len@].concat((^prev).val()@[len@..]) }
}

#[check(ghost)]
#[requires(left@ <= perm.len() && prev.len() == left@ + perm.len())]
#[requires((^prev).len() == prev.len())]
#[requires(perm.val()@[..left@] == prev.val()@[..left@])]
#[requires(perm.val()@[left@..] == prev.val()@[left@ + left@..])]
#[requires((^prev).val()@[..left@] == prev.val()@[left@..left@ + left@])]
#[requires((^prev).val()@[left@..] == (^perm).val()@)]
#[ensures((^perm).val()@ == perm.val()@[left@..].concat(perm.val()@[..left@])
    ==> (^prev).val()@ == (*prev).val()@[left@..].concat((*prev).val()@[..left@]))]
fn ptr_rotate_swap_lemma2<T>(
    left: usize,
    prev: Snapshot<&mut Perm<*const [T]>>,
    perm: Snapshot<&mut Perm<*const [T]>>,
) {
    let _ = (left, prev, perm);
    proof_assert! { (^prev).val()@ == (^prev).val()@[..left@].concat((^prev).val()@[left@..]) }
}
