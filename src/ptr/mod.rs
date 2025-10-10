use crate::intrinsics;
use core::hint::assert_unchecked as assume;
use creusot_contracts::ghost::PtrOwn;
use creusot_contracts::*;

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
#[trusted]
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
    #[trusted]
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
        // aligned. This branch _will_ be optimized out as `stride` is known at compile-time.
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
#[trusted]
#[erasure(::std::ptr::swap)]
#[requires(a as *const T == own.left().ptr() && b as *const T == own.right().ptr())]
#[ensures((^own.left()).ptr() == own.left().ptr() && (^own.left()).val() == own.right().val())]
#[ensures((^own.right()).ptr() == own.right().ptr() && (^own.right()).val() == own.left().val())]
pub unsafe fn swap_disjoint<T>(a: *mut T, b: *mut T, own: Ghost<DisjointOrEqual<T>>) {
    // SAFETY: `a` and `b` are disjoint pointers, so this is safe.
    unsafe { ::std::ptr::swap(a, b) }
}

pub enum DisjointOrEqual<'a, T> {
    Equal(&'a mut PtrOwn<T>),
    Disjoint(&'a mut PtrOwn<T>, &'a mut PtrOwn<T>),
}

impl<'a, T> DisjointOrEqual<'a, T> {
    #[logic(open)]
    pub fn left(self) -> &'a mut PtrOwn<T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(p, _) => p,
        }
    }

    #[logic(open)]
    pub fn right(self) -> &'a mut PtrOwn<T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(_, p) => p,
        }
    }

    #[check(ghost)]
    #[ensures(result == self.left())]
    pub fn left_ghost(&self) -> &PtrOwn<T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(p, _) => p,
        }
    }

    #[check(ghost)]
    #[ensures(result == self.right())]
    pub fn right_ghost(&self) -> &PtrOwn<T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(_, p) => p,
        }
    }

    #[check(ghost)]
    #[ensures(*result == *self.left())]
    #[ensures(^result == *(^self).left())]
    pub fn left_mut_ghost(&mut self) -> &mut PtrOwn<T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(p, _) => p,
        }
    }

    #[check(ghost)]
    #[ensures(*result == *self.right())]
    #[ensures(^result == *(^self).right())]
    pub fn right_mut_ghost(&mut self) -> &mut PtrOwn<T> {
        match self {
            DisjointOrEqual::Equal(p) => p,
            DisjointOrEqual::Disjoint(_, p) => p,
        }
    }
}

#[allow(unused_variables)]
#[trusted]
#[check(ghost_trusted)]
#[requires(0 < N@)]
#[requires(own.len() % N@ == 0)]
#[ensures(result.ptr() as *const T == own.ptr() as *const T)]
#[ensures(result.len() == own.len() / N@)]
#[ensures(forall<i, j> 0 <= i && i < own.len() / N@ && 0 <= j && j < N@
    ==> result.val()@[i]@[j] == own.val()@[i * N@ + j])]
pub fn cast_array_own<const N: usize, T>(own: &PtrOwn<[T]>) -> &PtrOwn<[[T; N]]> {
    unreachable!("ghost code")
}

#[allow(unused_variables)]
#[trusted]
#[check(ghost_trusted)]
#[requires(0 < N@)]
#[requires(own.len() % N@ == 0)]
#[ensures(result.ptr() as *const T == own.ptr() as *const T)]
#[ensures(result.len() == own.len() / N@)]
#[ensures(forall<i, j> 0 <= i && i < own.len() / N@ && 0 <= j && j < N@
    ==> result.val()@[i]@[j] == own.val()@[i * N@ + j])]
#[ensures(own.ptr() == (^own).ptr())]
#[ensures(forall<i, j> 0 <= i && i < own.len() / N@ && 0 <= j && j < N@
    ==> (^result).val()@[i]@[j] == (^own).val()@[i * N@ + j])]
pub fn cast_array_own_mut<const N: usize, T>(own: &mut PtrOwn<[T]>) -> &mut PtrOwn<[[T; N]]> {
    unreachable!("ghost code")
}
