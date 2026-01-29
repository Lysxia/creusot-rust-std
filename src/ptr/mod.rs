use crate::{
    intrinsics::{self, const_eval_select},
    ub_checks,
};
use ::core::mem::SizedTypeProperties as _;
use core::hint::assert_unchecked as assume;
use creusot_std::{ghost::perm::Perm, prelude::*, std::ptr::PtrLive};
use std::{
    mem::{self, MaybeUninit},
    num::NonZero,
};
mod const_ptr;
mod mut_ptr;

pub trait PtrAddExt<T> {
    /// Restriction of `add` that requires evidence that the addition is safe.
    /// We simply require a borrow of the `Perm<*const [T]>` token for the result pointer.
    /// In particular, this accounts for one-past-the-end pointers, which point to a zero-sized slice.
    ///
    /// From https://doc.rust-lang.org/std/primitive.pointer.html#method.add:
    ///
    /// > If any of the following conditions are violated, the result is Undefined Behavior:
    /// > - The offset in bytes, `count * size_of::<T>()`, computed on mathematical
    /// >   integers (without “wrapping around”), must fit in an `isize`.
    /// > - If the computed offset is non-zero, then `self` must be derived from a
    /// >   pointer to some allocated object, and the entire memory range between
    /// >   `self` and the result must be in bounds of that allocated object.
    /// >   In particular, this range must not “wrap around” the edge of the address space.
    ///
    #[requires(false)]
    unsafe fn add_live(self, offset: usize, perm: Ghost<PtrLive<T>>) -> Self;

    #[requires(false)]
    unsafe fn sub_live(self, offset: usize, perm: Ghost<PtrLive<T>>) -> Self;
}

/// Align pointer `p`.
///
/// Calculate offset (in terms of elements of `size_of::<T>()` stride) that has to be applied
/// to pointer `p` so that pointer `p` would get aligned to `a`.
///
/// # Safety
/// `a` must be a power of two.
///
/// # Notes
/// This implementation has been carefully tailored to not panic. It is UB for this to panic.
/// The only real change that can be made here is change of `INV_TABLE_MOD_16` and associated
/// constants.
///
/// If we ever decide to make it possible to call the intrinsic with `a` that is not a
/// power-of-two, it will probably be more prudent to just change to a naive implementation rather
/// than trying to adapt this to accommodate that change.
///
/// Any questions go to @nagisa.
#[allow(ptr_to_integer_transmute_in_consts)]
// #[safety::requires(a.is_power_of_two())]
// #[safety::ensures(|result| {
//     let stride = mem::size_of::<T>();
//     // ZSTs
//     if stride == 0 {
//         if p.addr() % a == 0 {
//             return *result == 0;
//         } else {
//             return *result == usize::MAX;
//         }
//     }

//     // In this case, the pointer cannot be aligned
//     if (a % stride == 0) && (p.addr() % stride != 0) {
//         return *result == usize::MAX;
//     }

//     // Checking if the answer should indeed be usize::MAX when a % stride != 0
//     // requires computing gcd(a, stride), which is too expensive without
//     // quantifiers (https://model-checking.github.io/kani/rfc/rfcs/0010-quantifiers.html).
//     // This should be updated once quantifiers are available.
//     if (a % stride != 0 && *result == usize::MAX) {
//         return true;
//     }

//     // If we reach this case, either:
//     //  - a % stride == 0 and p.addr() % stride == 0, so it is definitely possible to align the pointer
//     //  - a % stride != 0 and result != usize::MAX, so align_offset is claiming that it's possible to align the pointer
//     // Check that applying the returned result does indeed produce an aligned address
//     let product = usize::wrapping_mul(*result, stride);
//     let new_addr = usize::wrapping_add(product, p.addr());
//     *result != usize::MAX && new_addr % a == 0
// })]
#[trusted] // TODO
pub(crate) unsafe fn align_offset<T: Sized>(p: *const T, a: usize) -> usize {
    // FIXME(#75598): Direct use of these intrinsics improves codegen significantly at opt-level <=
    // 1, where the method versions of these operations are not inlined.
    use intrinsics::{
        cttz_nonzero, exact_div, mul_with_overflow, unchecked_rem, unchecked_shl, unchecked_shr,
        unchecked_sub, wrapping_add, wrapping_mul, wrapping_sub,
    };

    /// Calculate multiplicative modular inverse of `x` modulo `m`.
    ///
    /// This implementation is tailored for `align_offset` and has following preconditions:
    ///
    /// * `m` is a power-of-two;
    /// * `x < m`; (if `x ≥ m`, pass in `x % m` instead)
    ///
    /// Implementation of this function shall not panic. Ever.
    // #[safety::requires(m.is_power_of_two())]
    // #[safety::requires(x < m)]
    // TODO: add ensures contract to check that the answer is indeed correct
    // This will require quantifiers (https://model-checking.github.io/kani/rfc/rfcs/0010-quantifiers.html)
    // so that we can add a precondition that gcd(x, m) = 1 like so:
    // ∀d, d > 0 ∧ x % d = 0 ∧ m % d = 0 → d = 1
    // With this precondition, we can then write this postcondition to check the correctness of the answer:
    // #[safety::ensures(|result| wrapping_mul(*result, x) % m == 1)]
    #[trusted] // TODO
    #[inline]
    const unsafe fn mod_inv(x: usize, m: usize) -> usize {
        // /// Multiplicative modular inverse table modulo 2⁴ = 16.
        // ///
        // /// Note, that this table does not contain values where inverse does not exist (i.e., for
        // /// `0⁻¹ mod 16`, `2⁻¹ mod 16`, etc.)
        #[allow(non_snake_case)]
        /* const */
        let INV_TABLE_MOD_16: [u8; 8] = [1, 11, 13, 7, 9, 3, 5, 15];
        // /// Modulo for which the `INV_TABLE_MOD_16` is intended.
        #[allow(non_snake_case)]
        /* const */
        let INV_TABLE_MOD: usize = 16;

        // SAFETY: `m` is required to be a power-of-two, hence non-zero.
        let m_minus_one = unsafe { unchecked_sub(m, 1) };
        let mut inverse = INV_TABLE_MOD_16[(x & (INV_TABLE_MOD - 1)) >> 1] as usize;
        let mut mod_gate = INV_TABLE_MOD;
        // We iterate "up" using the following formula:
        //
        // $$ xy ≡ 1 (mod 2ⁿ) → xy (2 - xy) ≡ 1 (mod 2²ⁿ) $$
        //
        // This application needs to be applied at least until `2²ⁿ ≥ m`, at which point we can
        // finally reduce the computation to our desired `m` by taking `inverse mod m`.
        //
        // This computation is `O(log log m)`, which is to say, that on 64-bit machines this loop
        // will always finish in at most 4 iterations.
        loop {
            // y = y * (2 - xy) mod n
            //
            // Note, that we use wrapping operations here intentionally – the original formula
            // uses e.g., subtraction `mod n`. It is entirely fine to do them `mod
            // usize::MAX` instead, because we take the result `mod n` at the end
            // anyway.
            if mod_gate >= m {
                break;
            }
            inverse = wrapping_mul(inverse, wrapping_sub(2usize, wrapping_mul(x, inverse)));
            let (new_gate, overflow) = mul_with_overflow(mod_gate, mod_gate);
            if overflow {
                break;
            }
            mod_gate = new_gate;
        }
        inverse & m_minus_one
    }

    let stride = size_of::<T>();

    let addr: usize = p.addr();

    // SAFETY: `a` is a power-of-two, therefore non-zero.
    let a_minus_one = unsafe { unchecked_sub(a, 1) };

    if stride == 0 {
        // SPECIAL_CASE: handle 0-sized types. No matter how many times we step, the address will
        // stay the same, so no offset will be able to align the pointer unless it is already
        // aligned. This branch _will_ be optimized out as `stride` is knperm at compile-time.
        let p_mod_a = addr & a_minus_one;
        return if p_mod_a == 0 { 0 } else { usize::MAX };
    }

    // SAFETY: `stride == 0` case has been handled by the special case above.
    let a_mod_stride = unsafe { unchecked_rem(a, stride) };
    if a_mod_stride == 0 {
        // SPECIAL_CASE: In cases where the `a` is divisible by `stride`, byte offset to align a
        // pointer can be computed more simply through `-p (mod a)`. In the off-chance the byte
        // offset is not a multiple of `stride`, the input pointer was misaligned and no pointer
        // offset will be able to produce a `p` aligned to the specified `a`.
        //
        // The naive `-p (mod a)` equation inhibits LLVM's ability to select instructions
        // like `lea`. We compute `(round_up_to_next_alignment(p, a) - p)` instead. This
        // redistributes operations around the load-bearing, but pessimizing `and` instruction
        // sufficiently for LLVM to be able to utilize the various optimizations it knows about.
        //
        // LLVM handles the branch here particularly nicely. If this branch needs to be evaluated
        // at runtime, it will produce a mask `if addr_mod_stride == 0 { 0 } else { usize::MAX }`
        // in a branch-free way and then bitwise-OR it with whatever result the `-p mod a`
        // computation produces.

        let aligned_address = wrapping_add(addr, a_minus_one) & wrapping_sub(0, a);
        let byte_offset = wrapping_sub(aligned_address, addr);
        // FIXME: Remove the assume after <https://github.com/llvm/llvm-project/issues/62502>
        // SAFETY: Masking by `-a` can only affect the low bits, and thus cannot have reduced
        // the value by more than `a-1`, so even though the intermediate values might have
        // wrapped, the byte_offset is always in `[0, a)`.
        unsafe { assume(byte_offset < a) };

        // SAFETY: `stride == 0` case has been handled by the special case above.
        let addr_mod_stride = unsafe { unchecked_rem(addr, stride) };

        return if addr_mod_stride == 0 {
            // SAFETY: `stride` is non-zero. This is guaranteed to divide exactly as well, because
            // addr has been verified to be aligned to the original type’s alignment requirements.
            unsafe { exact_div(byte_offset, stride) }
        } else {
            usize::MAX
        };
    }

    // GENERAL_CASE: From here on we’re handling the very general case where `addr` may be
    // misaligned, there isn’t an obvious relationship between `stride` and `a` that we can take an
    // advantage of, etc. This case produces machine code that isn’t particularly high quality,
    // compared to the special cases above. The code produced here is still within the realm of
    // miracles, given the situations this case has to deal with.

    // SAFETY: a is power-of-two hence non-zero. stride == 0 case is handled above.
    // FIXME(const-hack) replace with min
    let gcdpow = unsafe {
        let x = cttz_nonzero(stride);
        let y = cttz_nonzero(a);
        if x < y { x } else { y }
    };
    // SAFETY: gcdpow has an upper-bound that’s at most the number of bits in a `usize`.
    let gcd = unsafe { unchecked_shl(1usize, gcdpow) };
    // SAFETY: gcd is always greater or equal to 1.
    if addr & unsafe { unchecked_sub(gcd, 1) } == 0 {
        // This branch solves for the following linear congruence equation:
        //
        // ` p + so = 0 mod a `
        //
        // `p` here is the pointer value, `s` - stride of `T`, `o` offset in `T`s, and `a` - the
        // requested alignment.
        //
        // With `g = gcd(a, s)`, and the above condition asserting that `p` is also divisible by
        // `g`, we can denote `a' = a/g`, `s' = s/g`, `p' = p/g`, then this becomes equivalent to:
        //
        // ` p' + s'o = 0 mod a' `
        // ` o = (a' - (p' mod a')) * (s'^-1 mod a') `
        //
        // The first term is "the relative alignment of `p` to `a`" (divided by the `g`), the
        // second term is "how does incrementing `p` by `s` bytes change the relative alignment of
        // `p`" (again divided by `g`). Division by `g` is necessary to make the inverse well
        // formed if `a` and `s` are not co-prime.
        //
        // Furthermore, the result produced by this solution is not "minimal", so it is necessary
        // to take the result `o mod lcm(s, a)`. This `lcm(s, a)` is the same as `a'`.

        // SAFETY: `gcdpow` has an upper-bound not greater than the number of trailing 0-bits in
        // `a`.
        let a2 = unsafe { unchecked_shr(a, gcdpow) };
        // SAFETY: `a2` is non-zero. Shifting `a` by `gcdpow` cannot shift out any of the set bits
        // in `a` (of which it has exactly one).
        let a2minus1 = unsafe { unchecked_sub(a2, 1) };
        // SAFETY: `gcdpow` has an upper-bound not greater than the number of trailing 0-bits in
        // `a`.
        let s2 = unsafe { unchecked_shr(stride & a_minus_one, gcdpow) };
        // SAFETY: `gcdpow` has an upper-bound not greater than the number of trailing 0-bits in
        // `a`. Furthermore, the subtraction cannot overflow, because `a2 = a >> gcdpow` will
        // always be strictly greater than `(p % a) >> gcdpow`.
        let minusp2 = unsafe { unchecked_sub(a2, unchecked_shr(addr & a_minus_one, gcdpow)) };
        // SAFETY: `a2` is a power-of-two, as proven above. `s2` is strictly less than `a2`
        // because `(s % a) >> gcdpow` is strictly less than `a >> gcdpow`.
        return wrapping_mul(minusp2, unsafe { mod_inv(s2, a2) }) & a2minus1;
    }

    // Cannot be aligned at all.
    usize::MAX
}

/// Restriction of `ptr::swap` to pointers that are either disjoint (non-overlapping) or equal;
/// this is guaranteed by construction of the `DisjointOrEqual` token.
///
/// Specifying `ptr::swap` so that it allows overlapping pointers is future work.
#[allow(unused_variables)]
#[trusted] // TODO: verify swap?
#[erasure(::core::ptr::swap)]
#[requires(a as *const T == *perm.left().ward() && b as *const T == *perm.right().ward())]
#[ensures((^perm.left()).ward() == perm.left().ward() && (^perm.left()).val() == perm.right().val())]
#[ensures((^perm.right()).ward() == perm.right().ward() && (^perm.right()).val() == perm.left().val())]
pub unsafe fn swap_disjoint<T>(a: *mut T, b: *mut T, perm: Ghost<DisjointOrEqual<T>>) {
    // SAFETY: `a` and `b` are disjoint pointers, so this is safe.
    unsafe { ::core::ptr::swap(a, b) }
}

pub enum DisjointOrEqual<'a, T> {
    Equal(&'a mut Perm<*const T>),
    Disjoint(&'a mut Perm<*const T>, &'a mut Perm<*const T>),
}

impl<'a, T> DisjointOrEqual<'a, T> {
    #[logic(open)]
    pub fn left(self) -> &'a mut Perm<*const T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(p, _) => p,
        }
    }

    #[logic(open)]
    pub fn right(self) -> &'a mut Perm<*const T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(_, p) => p,
        }
    }

    #[check(ghost)]
    #[ensures(result == self.left())]
    pub fn left_ghost(&self) -> &Perm<*const T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(p, _) => p,
        }
    }

    #[check(ghost)]
    #[ensures(result == self.right())]
    pub fn right_ghost(&self) -> &Perm<*const T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(_, p) => p,
        }
    }

    #[check(ghost)]
    #[ensures(*result == *self.left())]
    #[ensures(^result == *(^self).left())]
    pub fn left_mut_ghost(&mut self) -> &mut Perm<*const T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(p, _) => p,
        }
    }

    #[check(ghost)]
    #[ensures(*result == *self.right())]
    #[ensures(^result == *(^self).right())]
    pub fn right_mut_ghost(&mut self) -> &mut Perm<*const T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(_, p) => p,
        }
    }
}

/// Swaps the values at two mutable locations of the same type, without
/// deinitializing either.
///
/// But for the following exceptions, this function is semantically
/// equivalent to [`mem::swap`]:
///
/// * It operates on raw pointers instead of references. When references are
///   available, [`mem::swap`] should be preferred.
///
/// * The two pointed-to values may overlap. If the values do overlap, then the
///   overlapping region of memory from `x` will be used. This is demonstrated
///   in the second example below.
///
/// * The operation is "untyped" in the sense that data may be uninitialized or otherwise violate
///   the requirements of `T`. The initialization state is preserved exactly.
///
/// # Safety
///
/// Behavior is undefined if any of the following conditions are violated:
///
/// * Both `x` and `y` must be valid for both reads and writes. They must remain valid even when the
///   other pointer is written. (This means if the memory ranges overlap, the two pointers must not
///   be subject to aliasing restrictions relative to each other.)
///
/// * Both `x` and `y` must be properly aligned.
///
/// Note that even if `T` has size `0`, the pointers must be properly aligned.
#[inline]
#[trusted]
#[allow(unreachable_code, unused)]
#[requires(false)]
pub const unsafe fn swap<T>(x: *mut T, y: *mut T) {
    // Give ourselves some scratch space to work with.
    // We do not have to worry about drops: `MaybeUninit` does nothing when dropped.
    let mut tmp = MaybeUninit::<T>::uninit();

    // Perform the swap
    // SAFETY: the caller must guarantee that `x` and `y` are
    // valid for writes and properly aligned. `tmp` cannot be
    // overlapping either `x` or `y` because `tmp` was just allocated
    // on the stack as a separate allocation.
    unsafe {
        copy_nonoverlapping(x, tmp.as_mut_ptr(), 1, todo!(), todo!());
        copy(y, x, 1); // `x` and `y` may overlap
        copy_nonoverlapping(tmp.as_ptr(), y, 1, todo!(), todo!());
    }
}

/// Swaps `count * size_of::<T>()` bytes between the two regions of memory
/// beginning at `x` and `y`. The two regions must *not* overlap.
///
/// The operation is "untyped" in the sense that data may be uninitialized or otherwise violate the
/// requirements of `T`. The initialization state is preserved exactly.
///
/// # Safety
///
/// Behavior is undefined if any of the following conditions are violated:
///
/// * Both `x` and `y` must be valid for both reads and writes of `count *
///   size_of::<T>()` bytes.
///
/// * Both `x` and `y` must be properly aligned.
///
/// * The region of memory beginning at `x` with a size of `count *
///   size_of::<T>()` bytes must *not* overlap with the region of memory
///   beginning at `y` with the same size.
///
/// Note that even if the effectively copied size (`count * size_of::<T>()`) is `0`,
/// the pointers must be properly aligned.
#[inline]
#[trusted]
#[requires(x as *const T == x_perm.ward().thin() && count@ == x_perm.len())]
#[requires(y as *const T == y_perm.ward().thin() && count@ == y_perm.len())]
#[ensures((^x_perm).val()@ == y_perm.val()@ && (^y_perm).val()@ == x_perm.val()@)]
#[ensures(x as *const T == (^x_perm).ward().thin())]
#[ensures(y as *const T == (^y_perm).ward().thin())]
pub const unsafe fn swap_nonoverlapping<T>(
    x: *mut T,
    y: *mut T,
    count: usize,
    x_perm: Ghost<&mut Perm<*const [T]>>,
    y_perm: Ghost<&mut Perm<*const [T]>>,
) {
    ub_checks::assert_unsafe_precondition!(
        check_library_ub,
        "ptr::swap_nonoverlapping requires that both pointer arguments are aligned and non-null \
        and the specified memory ranges do not overlap",
        pearlite! { false },
        (
            x: *mut () = x as *mut (),
            y: *mut () = y as *mut (),
            size: usize = size_of::<T>(),
            align: usize = align_of::<T>(),
            count: usize = count,
        ) => {
            let zero_size = size == 0 || count == 0;
            ub_checks::maybe_is_aligned_and_not_null(x, align, zero_size)
                && ub_checks::maybe_is_aligned_and_not_null(y, align, zero_size)
                && ub_checks::maybe_is_nonoverlapping(x, y, size, count)
        }
    );

    const_eval_select!(
        @capture[T] { x: *mut T, y: *mut T, count: usize, x_perm: Ghost<&mut Perm<*const [T]>>, y_perm: Ghost<&mut Perm<*const [T]>> }:
        if const {
            // At compile-time we want to always copy this in chunks of `T`, to ensure that if there
            // are pointers inside `T` we will copy them in one go rather than trying to copy a part
            // of a pointer (which would not work).
            // SAFETY: Same preconditions as this function
            unsafe { swap_nonoverlapping_const(x, y, count, x_perm, y_perm) }
        } else {
            let _ = (x_perm, y_perm);
            // Going though a slice here helps codegen know the size fits in `isize`
            let slice = std::ptr::slice_from_raw_parts_mut(x, count);
            // SAFETY: This is all readable from the pointer, meaning it's one
            // allocation, and thus cannot be more than isize::MAX bytes.
            let bytes = unsafe { mem::size_of_val_raw::<[T]>(slice) };
            if let Some(bytes) = NonZero::new(bytes) {
                // SAFETY: These are the same ranges, just expressed in a different
                // type, so they're still non-overlapping.
                unsafe { swap_nonoverlapping_bytes(x.cast(), y.cast(), bytes) };
            }
        }
    )
}

/// Same behavior and safety conditions as [`swap_nonoverlapping`]
#[inline]
#[trusted]
#[allow(unreachable_code, unused)]
#[requires(x as *const T == x_perm.ward().thin() && count@ == x_perm.len())]
#[requires(y as *const T == y_perm.ward().thin() && count@ == y_perm.len())]
#[ensures((^x_perm).val()@ == y_perm.val()@ && (^y_perm).val()@ == x_perm.val()@)]
#[ensures(x as *const T == (^x_perm).ward().thin())]
#[ensures(y as *const T == (^y_perm).ward().thin())]
const unsafe fn swap_nonoverlapping_const<T>(
    x: *mut T,
    y: *mut T,
    count: usize,
    x_perm: Ghost<&mut Perm<*const [T]>>,
    y_perm: Ghost<&mut Perm<*const [T]>>,
) {
    let mut i = 0;
    while i < count {
        // SAFETY: By precondition, `i` is in-bounds because it's below `n`
        let x = unsafe { x.add(i) };
        // SAFETY: By precondition, `i` is in-bounds because it's below `n`
        // and it's distinct from `x` since the ranges are non-overlapping
        let y = unsafe { y.add(i) };

        // SAFETY: we're only ever given pointers that are valid to read/write,
        // including being aligned, and nothing here panics so it's drop-safe.
        unsafe {
            // Note that it's critical that these use `copy_nonoverlapping`,
            // rather than `read`/`write`, to avoid #134713 if T has padding.
            let mut temp = MaybeUninit::<T>::uninit();
            copy_nonoverlapping(x, temp.as_mut_ptr(), 1, todo!(), todo!());
            copy_nonoverlapping(y, x, 1, todo!(), todo!());
            copy_nonoverlapping(temp.as_ptr(), y, 1, todo!(), todo!());
        }

        i += 1;
    }
}

// Don't let MIR inline this, because we really want it to keep its noalias metadata
// #[rustc_no_mir_inline]
#[inline]
#[trusted]
#[requires(false)]
fn swap_chunk<const N: usize>(x: &mut MaybeUninit<[u8; N]>, y: &mut MaybeUninit<[u8; N]>) {
    let a = *x;
    let b = *y;
    *x = b;
    *y = a;
}

#[inline]
#[trusted]
#[requires(false)]
unsafe fn swap_nonoverlapping_bytes(x: *mut u8, y: *mut u8, bytes: NonZero<usize>) {
    // Same as `swap_nonoverlapping::<[u8; N]>`.
    unsafe fn swap_nonoverlapping_chunks<const N: usize>(
        x: *mut MaybeUninit<[u8; N]>,
        y: *mut MaybeUninit<[u8; N]>,
        chunks: NonZero<usize>,
    ) {
        let chunks = chunks.get();
        for i in 0..chunks {
            // SAFETY: i is in [0, chunks) so the adds and dereferences are in-bounds.
            unsafe { swap_chunk(&mut *x.add(i), &mut *y.add(i)) };
        }
    }

    // Same as `swap_nonoverlapping_bytes`, but accepts at most 1+2+4=7 bytes
    #[inline]
    unsafe fn swap_nonoverlapping_short(x: *mut u8, y: *mut u8, bytes: NonZero<usize>) {
        // Tail handling for auto-vectorized code sometimes has element-at-a-time behaviour,
        // see <https://github.com/rust-lang/rust/issues/134946>.
        // By swapping as different sizes, rather than as a loop over bytes,
        // we make sure not to end up with, say, seven byte-at-a-time copies.

        let bytes = bytes.get();
        let mut i = 0;
        macro_rules! swap_prefix {
            ($($n:literal)+) => {$(
                if (bytes & $n) != 0 {
                    // SAFETY: `i` can only have the same bits set as those in bytes,
                    // so these `add`s are in-bounds of `bytes`.  But the bit for
                    // `$n` hasn't been set yet, so the `$n` bytes that `swap_chunk`
                    // will read and write are within the usable range.
                    unsafe { swap_chunk::<$n>(&mut*x.add(i).cast(), &mut*y.add(i).cast()) };
                    i |= $n;
                }
            )+};
        }
        swap_prefix!(4 2 1);
        debug_assert_eq!(i, bytes);
    }

    const CHUNK_SIZE: usize = size_of::<*const ()>();
    let bytes = bytes.get();

    let chunks = bytes / CHUNK_SIZE;
    let tail = bytes % CHUNK_SIZE;
    if let Some(chunks) = NonZero::new(chunks) {
        // SAFETY: this is bytes/CHUNK_SIZE*CHUNK_SIZE bytes, which is <= bytes,
        // so it's within the range of our non-overlapping bytes.
        unsafe { swap_nonoverlapping_chunks::<CHUNK_SIZE>(x.cast(), y.cast(), chunks) };
    }
    if let Some(tail) = NonZero::new(tail) {
        const { assert!(CHUNK_SIZE <= 8) };
        let delta = chunks * CHUNK_SIZE;
        // SAFETY: the tail length is below CHUNK SIZE because of the remainder,
        // and CHUNK_SIZE is at most 8 by the const assert, so tail <= 7
        unsafe { swap_nonoverlapping_short(x.add(delta), y.add(delta), tail) };
    }
}

/// Copies `count * size_of::<T>()` bytes from `src` to `dst`. The source
/// and destination may overlap.
///
/// The copy is "untyped" in the sense that data may be uninitialized or otherwise violate the
/// requirements of `T`. The initialization state is preserved exactly.
///
/// # Safety
///
/// Behavior is undefined if any of the following conditions are violated:
///
/// * `src` must be [valid] for reads of `count * size_of::<T>()` bytes.
///
/// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes, and must remain valid even
///   when `src` is read for `count * size_of::<T>()` bytes. (This means if the memory ranges
///   overlap, the `dst` pointer must not be invalidated by `src` reads.)
///
/// * Both `src` and `dst` must be properly aligned.
///
/// Like [`read`], `copy` creates a bitwise copy of `T`, regardless of
/// whether `T` is [`Copy`]. If `T` is not [`Copy`], using both the values
/// in the region beginning at `*src` and the region beginning at `*dst` can
/// [violate memory safety][read-ownership].
///
/// Note that even if the effectively copied size (`count * size_of::<T>()`) is
/// `0`, the pointers must be properly aligned.
#[trusted] // TODO
#[erasure(core::ptr::copy::<T>)]
#[requires(false)]
/* pub const */
pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
    // SAFETY: the safety contract for `copy` must be upheld by the caller.
    unsafe {
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "ptr::copy requires that both pointer arguments are aligned and non-null",
            pearlite! { src.is_aligned_to_logic(align) && (zero_size || !src.is_null_logic())
                && dst.is_aligned_to_logic(align) && (zero_size || !dst.is_null_logic()) },
            (
                src: *const () = src as *const (),
                dst: *mut () = dst as *mut (),
                align: usize = align_of::<T>(),
                zero_size: bool = T::IS_ZST || count == 0,
            ) =>
            ub_checks::maybe_is_aligned_and_not_null(src, align, zero_size)
                && ub_checks::maybe_is_aligned_and_not_null(dst, align, zero_size)
        );
        crate::intrinsics::copy(src, dst, count)
    }
}

// The nonoverlap is guaranteed by the permissions' ownership.
#[trusted] // TODO: need fact: nonoverlapping allocations have distant addresses
#[erasure(core::ptr::copy_nonoverlapping::<T>)]
#[requires(src_perm.ward().thin() == src && src_perm.len() == count@)]
#[requires(dst_perm.ward().thin() == dst as *const T && dst_perm.len() == count@)]
#[ensures((^dst_perm).val()@ == src_perm.val()@)]
/* pub const */
pub unsafe fn copy_nonoverlapping<T>(
    src: *const T,
    dst: *mut T,
    count: usize,
    src_perm: Ghost<&Perm<*const [T]>>,
    dst_perm: Ghost<&mut Perm<*const [T]>>,
) {
    ub_checks::assert_unsafe_precondition!(
        check_language_ub,
        "ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null \
        and the specified memory ranges do not overlap",
        pearlite! { src.is_aligned_to_logic(align) && (count@ == 0 || size@ == 0 || !src.is_null_logic())
            && dst.is_aligned_to_logic(align) && (count@ == 0 || size@ == 0 || !dst.is_null_logic())
            && false /* TODO */ },
        (
            src: *const () = src as *const (),
            dst: *mut () = dst as *mut (),
            size: usize = size_of::<T>(),
            align: usize = align_of::<T>(),
            count: usize = count,
        ) => {
            let zero_size = count == 0 || size == 0;
            ub_checks::maybe_is_aligned_and_not_null(src, align, zero_size)
                && ub_checks::maybe_is_aligned_and_not_null(dst, align, zero_size)
                && ub_checks::maybe_is_nonoverlapping(src, dst, size, count)
        }
    );

    // SAFETY: the safety contract for `copy_nonoverlapping` must be
    // upheld by the caller.
    unsafe { crate::intrinsics::copy_nonoverlapping(src, dst, count, src_perm, dst_perm) }
}

#[allow(unused_variables)]
#[trusted] // Specify transmute
#[check(ghost_trusted)]
#[requires(0 < N@)]
#[requires(perm.len() % N@ == 0)]
#[ensures(*result.ward() as *const T == *perm.ward() as *const T)]
#[ensures(result.len() == perm.len() / N@)]
#[ensures(forall<i, j> 0 <= i && i < perm.len() / N@ && 0 <= j && j < N@
    ==> result.val()@[i]@[j] == perm.val()@[i * N@ + j])]
pub fn cast_chunks_perm<const N: usize, T>(perm: &Perm<*const [T]>) -> &Perm<*const [[T; N]]> {
    unreachable!("ghost code")
}

#[allow(unused_variables)]
#[trusted] // Specify transmute
#[check(ghost_trusted)]
#[requires(0 < N@)]
#[requires(perm.len() % N@ == 0)]
#[ensures(*result.ward() as *const T == *perm.ward() as *const T)]
#[ensures(result.len() == perm.len() / N@)]
#[ensures(forall<i, j> 0 <= i && i < perm.len() / N@ && 0 <= j && j < N@
    ==> result.val()@[i]@[j] == perm.val()@[i * N@ + j])]
#[ensures(perm.ward() == (^perm).ward())]
#[ensures(forall<i, j> 0 <= i && i < perm.len() / N@ && 0 <= j && j < N@
    ==> (^result).val()@[i]@[j] == (^perm).val()@[i * N@ + j])]
pub fn cast_chunks_perm_mut<const N: usize, T>(
    perm: &mut Perm<*const [T]>,
) -> &mut Perm<*const [[T; N]]> {
    unreachable!("ghost code")
}

#[allow(unused_variables)]
#[trusted]
#[check(ghost_trusted)]
#[ensures(*result.ward() as *const T == *perm.ward() as *const T)]
#[ensures(result.val()@ == perm.val()@.flat_map(|chunk: [T; N]| chunk@))]
pub fn cast_from_chunks_perm<const N: usize, T>(perm: &Perm<*const [[T; N]]>) -> &Perm<*const [T]> {
    unreachable!("ghost code")
}

#[allow(unused_variables)]
#[trusted]
#[check(ghost_trusted)]
#[ensures(*result.ward() as *const T == *perm.ward() as *const T)]
#[ensures(result.val()@ == perm.val()@.flat_map(|chunk: [T; N]| chunk@))]
#[ensures(perm.ward() == (^perm).ward())]
#[ensures(forall<i> 0 <= i && i < perm.len() ==> (^perm).val()@[i]@ == (^result).val()@[N@ * i .. N@ * i + N@])]
pub fn cast_from_chunks_perm_mut<const N: usize, T>(
    perm: &mut Perm<*const [[T; N]]>,
) -> &mut Perm<*const [T]> {
    unreachable!("ghost code")
}

#[allow(unused_variables)]
#[trusted]
#[check(ghost_trusted)]
#[requires(perm.len() == N@)]
#[ensures(*result.ward() == *perm.ward() as *const [T; N])]
#[ensures(result.val()@ == perm.val()@)]
pub fn cast_array_perm<const N: usize, T>(perm: &Perm<*const [T]>) -> &Perm<*const [T; N]> {
    unreachable!("ghost code")
}

#[allow(unused_variables)]
#[trusted]
#[check(ghost_trusted)]
#[requires(perm.len() == N@)]
#[ensures(*result.ward() == *perm.ward() as *const [T; N])]
#[ensures(result.val()@ == perm.val()@)]
#[ensures(perm.ward() == (^perm).ward())]
#[ensures((^result).val()@ == (^perm).val()@)]
pub fn cast_array_perm_mut<const N: usize, T>(
    perm: &mut Perm<*const [T]>,
) -> &mut Perm<*const [T; N]> {
    unreachable!("ghost code")
}
