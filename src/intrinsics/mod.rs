#![allow(unused_variables)]
pub use ::core::intrinsics::const_eval_select;
#[cfg(creusot)]
use creusot_std::std::ptr::metadata_logic;
use creusot_std::{ghost::perm::Perm, prelude::*, std::ptr::PtrLive};

// Intrinsics: we specialize all the intrinsics to usize so that
// we can specify them.

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::exact_div)]
#[requires(0 < y@ && x@ % y@ == 0)]
#[ensures(result@ == x@ / y@)]
pub const unsafe fn exact_div(x: usize, y: usize) -> usize {
    unsafe { ::core::intrinsics::exact_div(x, y) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::cttz_nonzero)]
#[requires(x@ != 0)]
pub const unsafe fn cttz_nonzero(x: usize) -> u32 {
    unsafe { ::core::intrinsics::cttz_nonzero(x) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::mul_with_overflow)]
#[ensures(result.0@ == x@ * y@ % (usize::MAX@ + 1))]
#[ensures(result.1 == (x@ * y@ <= usize::MAX@))]
pub const fn mul_with_overflow(x: usize, y: usize) -> (usize, bool) {
    ::core::intrinsics::mul_with_overflow(x, y)
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::unchecked_rem)]
#[requires(y@ != 0)]
#[ensures(result@ == x@ % y@)]
pub const unsafe fn unchecked_rem(x: usize, y: usize) -> usize {
    unsafe { ::core::intrinsics::unchecked_rem(x, y) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::unchecked_shl)]
#[requires(y@ < usize::BITS@)]
#[ensures(result == x << y)]
pub const unsafe fn unchecked_shl(x: usize, y: u32) -> usize {
    unsafe { ::core::intrinsics::unchecked_shl(x, y) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::unchecked_shr)]
#[requires(y@ < usize::BITS@)]
#[ensures(result == x >> y)]
pub const unsafe fn unchecked_shr(x: usize, y: u32) -> usize {
    unsafe { ::core::intrinsics::unchecked_shr(x, y) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::unchecked_sub)]
#[requires(0 <= x@ - y@)]
#[ensures(result@ == x@ - y@)]
pub const unsafe fn unchecked_sub(x: usize, y: usize) -> usize {
    unsafe { ::core::intrinsics::unchecked_sub(x, y) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::unchecked_sub)]
#[requires(isize::MIN@ <= x@ - y@ && x@ - y@ <= isize::MAX@)]
#[ensures(result@ == x@ - y@)]
pub const unsafe fn unchecked_sub_isize(x: isize, y: isize) -> isize {
    unsafe { ::core::intrinsics::unchecked_sub(x, y) }
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::wrapping_add)]
#[ensures(result@ == a@ + b@ % (usize::MAX@ + 1))]
pub const fn wrapping_add(a: usize, b: usize) -> usize {
    ::core::intrinsics::wrapping_add(a, b)
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::wrapping_mul)]
#[ensures(result@ == a@ * b@ % (usize::MAX@ + 1))]
pub const fn wrapping_mul(a: usize, b: usize) -> usize {
    ::core::intrinsics::wrapping_mul(a, b)
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::wrapping_sub)]
#[ensures(result@ == a@ - b@ % (usize::MAX@ + 1))]
pub const fn wrapping_sub(a: usize, b: usize) -> usize {
    ::core::intrinsics::wrapping_sub(a, b)
}

#[trusted]
#[erasure(core::intrinsics::slice_get_unchecked::<&T, &[T], T>)]
#[requires(index@ < slice@.len())]
#[ensures(*result == slice@[index@])]
pub unsafe fn slice_get_unchecked_ref<T>(slice: &[T], index: usize) -> &T {
    unsafe { core::intrinsics::slice_get_unchecked(slice, index) }
}

#[trusted]
#[erasure(core::intrinsics::slice_get_unchecked::<&mut T, &mut [T], T>)]
#[requires(index@ < slice@.len())]
#[ensures(*result == (*slice)@[index@])]
#[ensures(^result == (^slice)@[index@])]
#[ensures(forall<i: Int> i != index@ ==> (*slice)@.get(i) == (^slice)@.get(i))]
pub unsafe fn slice_get_unchecked_mut<T>(slice: &mut [T], index: usize) -> &mut T {
    unsafe { core::intrinsics::slice_get_unchecked(slice, index) }
}

#[trusted]
#[erasure(core::intrinsics::slice_get_unchecked::<*const T, *const [T], T>)]
#[requires(*perm.ward() == ptr)]
#[requires(index < metadata_logic(ptr))]
#[ensures(result == (ptr as *const T).offset_logic(index@))]
pub unsafe fn slice_get_unchecked_raw<T>(
    ptr: *const [T],
    index: usize,
    perm: Ghost<&Perm<*const [T]>>,
) -> *const T {
    unsafe { core::intrinsics::slice_get_unchecked(ptr, index) }
}

/// This only needs a `&Ptrperm` instead of `&mut Ptrperm` because it doesn't mutate anything.
#[trusted]
#[erasure(core::intrinsics::slice_get_unchecked::<*mut T, *mut [T], T>)]
#[requires(*perm.ward() == ptr as *const [T])]
#[requires(index < metadata_logic(ptr))]
#[ensures(result == (ptr as *const T).offset_logic(index@) as *mut T)]
pub unsafe fn slice_get_unchecked_raw_mut<T>(
    ptr: *mut [T],
    index: usize,
    perm: Ghost<&Perm<*const [T]>>,
) -> *mut T {
    unsafe { core::intrinsics::slice_get_unchecked(ptr, index) }
}

#[trusted]
#[erasure(core::intrinsics::aggregate_raw_ptr::<*const [T], *const T, usize>)]
#[ensures(result as *const T == ptr && metadata_logic(result) == len)]
pub fn aggregate_raw_ptr_slice<T>(ptr: *const T, len: usize) -> *const [T] {
    core::intrinsics::aggregate_raw_ptr(ptr, len)
}

#[trusted]
#[erasure(core::intrinsics::aggregate_raw_ptr::<*mut [T], *mut T, usize>)]
#[ensures(result as *mut T == ptr && metadata_logic(result) == len)]
pub fn aggregate_raw_ptr_mut_slice<T>(ptr: *mut T, len: usize) -> *mut [T] {
    core::intrinsics::aggregate_raw_ptr(ptr, len)
}

#[trusted]
#[erasure(core::intrinsics::copy::<T>)]
#[requires(false)] // TODO: source and destination may overlap. Sounds tricky.
/* pub const */
pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
    unsafe { core::intrinsics::copy(src, dst, count) }
}

#[trusted]
#[erasure(core::intrinsics::copy_nonoverlapping::<T>)]
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
    let _ = (src_perm, dst_perm);
    unsafe { core::intrinsics::copy_nonoverlapping(src, dst, count) }
}

#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains_range(dst, offset@))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn add_live<T>(dst: *const T, offset: usize, live: Ghost<PtrLive<T>>) -> *const T {
    let _ = live;
    unsafe { core::intrinsics::offset(dst, offset) }
}

#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains_range(dst, offset@))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn offset_live<T>(dst: *const T, offset: isize, live: Ghost<PtrLive<T>>) -> *const T {
    let _ = live;
    unsafe { core::intrinsics::offset(dst, offset) }
}

#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains_range(dst, offset@))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn add_live_mut<T>(dst: *mut T, offset: usize, live: Ghost<PtrLive<T>>) -> *mut T {
    let _ = live;
    unsafe { core::intrinsics::offset(dst, offset) }
}

#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains_range(dst, offset@))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn offset_live_mut<T>(dst: *mut T, offset: isize, live: Ghost<PtrLive<T>>) -> *mut T {
    let _ = live;
    unsafe { core::intrinsics::offset(dst, offset) }
}

pub(crate) macro const_eval_select {
    (
        @capture$([$($binders:tt)*])? { $($arg:ident : $ty:ty = $val:expr),* $(,)? } $( -> $ret:ty )? :
        if const
            $(#[$compiletime_attr:meta])* $compiletime:block
        else
            $(#[$runtime_attr:meta])* $runtime:block
    ) => {
        // Use the `noinline` arm, after adding explicit `inline` attributes
        $crate::intrinsics::const_eval_select!(
            @capture$([$($binders)*])? { $($arg : $ty = $val),* } $(-> $ret)? :
            #[noinline]
            if const
                #[inline] // prevent codegen on this function
                $(#[$compiletime_attr])*
                $compiletime
            else
                #[inline] // avoid the overhead of an extra fn call
                $(#[$runtime_attr])*
                $runtime
        )
    },
    // With a leading #[noinline], we don't add inline attributes
    (
        @capture$([$($binders:tt)*])? { $($arg:ident : $ty:ty = $val:expr),* $(,)? } $( -> $ret:ty )? :
        #[noinline]
        if const
            $(#[$compiletime_attr:meta])* $compiletime:block
        else
            $(#[$runtime_attr:meta])* $runtime:block
    ) => {{
        $(#[$runtime_attr])*
        fn runtime$(<$($binders)*>)?($($arg: $ty),*) $( -> $ret )? {
            $runtime
        }

        $(#[$compiletime_attr])*
        const fn compiletime$(<$($binders)*>)?($($arg: $ty),*) $( -> $ret )? {
            // Don't warn if one of the arguments is unused.
            $(let _ = $arg;)*

            $compiletime
        }

        const_eval_select(($($val,)*), compiletime, runtime)
    }},
    // We support leaving away the `val` expressions for *all* arguments
    // (but not for *some* arguments, that's too tricky).
    (
        @capture$([$($binders:tt)*])? { $($arg:ident : $ty:ty),* $(,)? } $( -> $ret:ty )? :
        if const
            $(#[$compiletime_attr:meta])* $compiletime:block
        else
            $(#[$runtime_attr:meta])* $runtime:block
    ) => {
        $crate::intrinsics::const_eval_select!(
            @capture$([$($binders)*])? { $($arg : $ty = $arg),* } $(-> $ret)? :
            if const
                $(#[$compiletime_attr])* $compiletime
            else
                $(#[$runtime_attr])* $runtime
        )
    },
}
