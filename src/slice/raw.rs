use crate::ub_checks;
use ::std::ptr;
use creusot_contracts::{ghost::PtrOwn, prelude::*};

#[requires(own.ptr().thin() == data)]
#[requires(len@ == own.len())]
#[ensures(result@ == own.val()@)]
#[erasure(::std::slice::from_raw_parts)]
pub unsafe fn from_raw_parts_own<'a, T>(
    data: *const T,
    len: usize,
    own: Ghost<&'a PtrOwn<[T]>>,
) -> &'a [T] {
    ghost! {
        own.live();
        div_mono_lemma();
    };
    // SAFETY: the caller must uphold the safety contract for `from_raw_parts`.
    unsafe {
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "slice::from_raw_parts requires the pointer to be aligned and non-null, and the total size of the slice not to exceed `isize::MAX`",
            pearlite!{ data.is_aligned_to_logic(align) && !data.is_null_logic() && (size@ > 0 ==> len@ <= isize::MAX@ / size@) },
            (
                data: *mut () = data as *mut (),
                size: usize = size_of::<T>(),
                align: usize = align_of::<T>(),
                len: usize = len,
            ) =>
            ub_checks::maybe_is_aligned_and_not_null(data, align, false)
                && ub_checks::is_valid_allocation_size(size, len)
        );
        PtrOwn::as_ref(std::ptr::slice_from_raw_parts(data, len), own)
    }
}

#[requires(own.ptr().thin() == data as *const T)]
#[requires(len@ == own.len())]
#[ensures(result@ == own.val()@)]
#[ensures((^*own).ptr().thin() == data as *const T)]
#[ensures((^result)@ == (^*own).val()@)]
#[erasure(::std::slice::from_raw_parts_mut)]
pub unsafe fn from_raw_parts_mut_own<T>(
    data: *mut T,
    len: usize,
    own: Ghost<&mut PtrOwn<[T]>>,
) -> &mut [T] {
    ghost! {
        own.live();
        div_mono_lemma();
    };
    // SAFETY: the caller must uphold the safety contract for `from_raw_parts_mut`.
    unsafe {
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "slice::from_raw_parts_mut requires the pointer to be aligned and non-null, and the total size of the slice not to exceed `isize::MAX`",
            pearlite!{ data.is_aligned_to_logic(align) && !data.is_null_logic() && (size@ > 0 ==> len@ <= isize::MAX@ / size@) },
            (
                data: *mut () = data as *mut (),
                size: usize = size_of::<T>(),
                align: usize = align_of::<T>(),
                len: usize = len,
            ) =>
            ub_checks::maybe_is_aligned_and_not_null(data, align, false)
                && ub_checks::is_valid_allocation_size(size, len)
        );
        PtrOwn::as_mut(std::ptr::slice_from_raw_parts_mut(data, len), own)
    }
}

#[check(ghost)]
#[ensures(forall<a: Int, b: Int, d: Int> 0 <= a && 0 < d && a * d <= b ==> a <= b / d)]
fn div_mono_lemma() {}

/// Use `from_raw_parts_own` instead.
#[trusted]
#[requires(false)]
pub const unsafe fn from_raw_parts<'a, T>(data: *const T, len: usize) -> &'a [T] {
    // SAFETY: the caller must uphold the safety contract for `from_raw_parts`.
    unsafe {
        // ub_checks::assert_unsafe_precondition!(
        //     check_language_ub,
        //     "slice::from_raw_parts requires the pointer to be aligned and non-null, and the total size of the slice not to exceed `isize::MAX`",
        //     (
        //         data: *mut () = data as *mut (),
        //         size: usize = size_of::<T>(),
        //         align: usize = align_of::<T>(),
        //         len: usize = len,
        //     ) =>
        //     ub_checks::maybe_is_aligned_and_not_null(data, align, false)
        //         && ub_checks::is_valid_allocation_size(size, len)
        // );
        &*ptr::slice_from_raw_parts(data, len)
    }
}

/// Use `from_raw_parts_mut_own` instead.
#[trusted]
#[requires(false)]
pub const unsafe fn from_raw_parts_mut<'a, T>(data: *mut T, len: usize) -> &'a mut [T] {
    // SAFETY: the caller must uphold the safety contract for `from_raw_parts_mut`.
    unsafe {
        // ub_checks::assert_unsafe_precondition!(
        //     check_language_ub,
        //     "slice::from_raw_parts_mut requires the pointer to be aligned and non-null, and the total size of the slice not to exceed `isize::MAX`",
        //     (
        //         data: *mut () = data as *mut (),
        //         size: usize = size_of::<T>(),
        //         align: usize = align_of::<T>(),
        //         len: usize = len,
        //     ) =>
        //     ub_checks::maybe_is_aligned_and_not_null(data, align, false)
        //         && ub_checks::is_valid_allocation_size(size, len)
        // );
        &mut *ptr::slice_from_raw_parts_mut(data, len)
    }
}
