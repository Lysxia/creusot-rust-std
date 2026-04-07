use crate::ptr::PtrAddExt as _;
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
#[ensures((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@]))]
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
#[trusted]
#[erasure(private core::slice::rotate::ptr_rotate_gcd)]
#[requires(left@ != 0 && right@ != 0)]
#[requires(mid as *const T == perm.ward().thin().offset_logic(left@))]
#[requires(left@ + right@ == perm.len())]
#[ensures((^perm).val()@ == (*perm).val()@[left@..].concat((*perm).val()@[..left@]))]
#[inline]
unsafe fn ptr_rotate_gcd<T>(
    left: usize,
    mid: *mut T,
    right: usize,
    perm: Ghost<&mut Perm<*const [T]>>,
) {
    // Algorithm 2
    // Microbenchmarks indicate that the average performance for random shifts is better all
    // the way until about `left + right == 32`, but the worst case performance breaks even
    // around 16. 24 was chosen as middle ground. If the size of `T` is larger than 4
    // `usize`s, this algorithm also outperforms other algorithms.
    // SAFETY: callers must ensure `mid - left` is valid for reading and writing.
    let x = unsafe { mid.sub_live(left, ghost! { perm.live() }) };
    // beginning of first round
    // SAFETY: see previous comment.
    let mut tmp: T = unsafe { x.read() };
    let mut i = right;
    // `gcd` can be found before hand by calculating `gcd(left + right, right)`,
    // but it is faster to do one loop which calculates the gcd as a side effect, then
    // doing the rest of the chunk
    let mut gcd = right;
    // benchmarks reveal that it is faster to swap temporaries all the way through instead
    // of reading one temporary once, copying backwards, and then writing that temporary at
    // the very end. This is possibly due to the fact that swapping or replacing temporaries
    // uses only one memory address in the loop instead of needing to manage two.
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
        tmp = unsafe { x.add(i).replace(tmp) };
        // instead of incrementing `i` and then checking if it is outside the bounds, we
        // check if `i` will go outside the bounds on the next increment. This prevents
        // any wrapping of pointers or `usize`.
        if i >= left {
            i -= left;
            if i == 0 {
                // end of first round
                // SAFETY: tmp has been read from a valid source and x is valid for writing
                // according to the caller.
                unsafe { x.write(tmp) };
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
    // finish the chunk with more rounds
    for start in 1..gcd {
        // SAFETY: `gcd` is at most equal to `right` so all values in `1..gcd` are valid for
        // reading and writing as per the function's safety contract, see [long-safety-expl]
        // above
        tmp = unsafe { x.add(start).read() };
        // [safety-expl-addition]
        //
        // Here `start < gcd` so `start < right` so `i < right+right`: `right` being the
        // greatest common divisor of `(left+right, right)` means that `left = right` so
        // `i < left+right` so `x+i = mid-left+i` is always valid for reading and writing
        // according to the function's safety contract.
        i = start + right;
        loop {
            // SAFETY: see [long-safety-expl] and [safety-expl-addition]
            tmp = unsafe { x.add(i).replace(tmp) };
            if i >= left {
                i -= left;
                if i == start {
                    // SAFETY: see [long-safety-expl] and [safety-expl-addition]
                    unsafe { x.add(start).write(tmp) };
                    break;
                }
            } else {
                i += right;
            }
        }
    }
}

#[trusted]
#[erasure(<*mut T>::replace)]
#[requires(src as *const T == *perm.ward())]
#[ensures(dst == *(^perm).val())]
#[ensures(result == *perm.val())]
unsafe fn replace_perm<T>(src: *mut T, dst: T, perm: Ghost<&mut Perm<*const T>>) -> T {
    unsafe { src.replace(dst) }
}

// #[trusted]
// #[erasure(<*mut T>::read)]
// unsafe fn read_perm<T>(p: *mut T, perm: Ghost<&Perm<*const T>>) -> T {
//     todo!()
// }

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
                #[trusted] // TODO: move to creusot-std
                proof_assert! {
                    forall<p: *const T, q: *const T, i: Int>
                        p.sub_logic(q.offset_logic(i)) == p.sub_logic(q) - i
                };
                let (mut perm01, perm2) = ghost! {
                    perm.into_inner().split_at_mut(*Int::new(left as i128))
                }
                .split();
                let mut perm1 = ghost! {
                    perm01.split_at_mut(*Int::new((left - right) as i128)).1
                };
                // SAFETY:
                // `left >= right` so `[mid-right, mid+right)` is valid for reading and writing
                // Subtracting `right` from `mid` each turn is counterbalanced by the addition and
                // check after it.
                unsafe {
                    crate::ptr::swap_nonoverlapping(
                        mid.sub_live(right, ghost! { perm1.live() }),
                        mid,
                        right,
                        ghost! { *perm1 },
                        perm2,
                    );
                    mid = mid.sub_live(right, ghost! { perm1.live() });
                }
                perm = perm01; // ghost
                let _left = snapshot! { left@ };
                left -= right;
                proof_assert! { perm.val()@[..left@] == _perm.val()@[..left@] };
                proof_assert! { perm.val()@[left@..] == _perm.val()@[left@ + right@..] };
                proof_assert! { (^_perm).val()@[left@ + right@..] == _perm.val()@[left@..left@ + right@] };
                proof_assert! { (^_perm).val()@[..left@ + right@] == (^perm).val()@ };
                proof_assert! {
                    (^_perm).val()@[..*_left] == perm.val()@[left@..].concat(perm.val()@[..left@])
                    ==> (^_perm).val()@ == (*_perm).val()@[*_left..].concat((*_perm).val()@[..*_left])
                }
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
                proof_assert! { perm.val()@[..left@] == _perm.val()@[..left@] };
                proof_assert! { perm.val()@[left@..] == _perm.val()@[left@ + left@..] };
                proof_assert! { (^_perm).val()@[..left@] == _perm.val()@[left@..left@ + left@] };
                proof_assert! { (^_perm).val()@[left@..] == (^perm).val()@ };
                proof_assert! {
                    (^_perm).val()@[left@..] == perm.val()@[left@..].concat(perm.val()@[..left@])
                    ==> (^_perm).val()@ == (*_perm).val()@[left@..].concat((*_perm).val()@[..left@])
                }
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
