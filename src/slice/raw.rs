use ::std::ptr;
use creusot_contracts::{*, ptr_own::{BlockOwn, PtrOwn}};

#[trusted]
#[requires(own.ptr() == data.raw())]
#[requires(len@ == own.len())]
#[ensures(result@ == own.contents())]
pub unsafe fn from_raw_parts_own<'a, T>(data: *const T, len: usize, own: Ghost<&'a BlockOwn<T>>) -> &'a [T] {
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
        let (ptr, own) = std::slice::slice_from_raw_parts(data, len, own);
        PtrOwn::as_ref(ptr, own)
    }
}

#[trusted]
#[requires(own.ptr() == data.raw())]
#[requires(len@ == own.len())]
#[ensures(result@ == own.contents())]
#[ensures((^own.inner_logic()).ptr() == data.raw())]
#[ensures((^result)@ == (^own.inner_logic()).contents())]
pub unsafe fn from_raw_parts_mut_own<'a, T>(data: *mut T, len: usize, own: Ghost<&'a mut BlockOwn<T>>) -> &'a mut [T] {
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
        let (ptr, own) = std::slice::slice_from_raw_parts_mut(data, len, own);
        PtrOwn::as_mut(ptr, own)
    }
}

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