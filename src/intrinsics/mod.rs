#![allow(unused_variables)]
pub use ::core::intrinsics::const_eval_select;
use creusot_contracts::{ghost::PtrOwn, *};

pub const unsafe fn exact_div<T: Copy>(x: T, y: T) -> T {
    panic!("intrinsics")
}

pub const unsafe fn cttz_nonzero<T: Copy>(x: T) -> u32 {
    panic!("intrinsics")
}

pub const fn mul_with_overflow<T: Copy>(x: T, y: T) -> (T, bool) {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_rem<T: Copy>(x: T, y: T) -> T {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_shl<T: Copy, U: Copy>(x: T, y: U) -> T {
    panic!("intrinsics")
}

pub const unsafe fn unchecked_shr<T: Copy, U: Copy>(x: T, y: U) -> T {
    panic!("intrinsics")
}

#[trusted]
#[check(ghost_trusted)]
#[erasure(::core::intrinsics::unchecked_sub)]
#[requires(0 <= x@ - y@)]
#[ensures(result@ == x@ - y@)]
pub const unsafe fn unchecked_sub(x: usize, y: usize) -> usize {
    unsafe { ::core::intrinsics::unchecked_sub(x, y) }
}

pub const fn wrapping_add<T: Copy>(a: T, b: T) -> T {
    panic!("intrinsics")
}

pub const fn wrapping_mul<T: Copy>(a: T, b: T) -> T {
    panic!("intrinsics")
}

pub const fn wrapping_sub<T: Copy>(a: T, b: T) -> T {
    panic!("intrinsics")
}

#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(own.ptr().as_ptr_logic() == dst)]
#[requires(own.len() <= offset@)]
#[ensures(own.ptr().as_ptr_logic().offset_logic(offset@) == result)]
pub unsafe fn offset_own<T>(dst: *const T, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> *const T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(own.ptr().as_ptr_logic() == dst as *const T)]
#[requires(own.len() <= offset@)]
#[ensures(own.ptr().as_ptr_logic().offset_logic(offset@) == result as *const T)]
pub unsafe fn offset_own_mut<T>(dst: *mut T, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> *mut T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

// TODO: can Creusot read the MIR of these intrinsics?
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
#[requires(own.ptr() == ptr)]
#[requires(index@ < ptr.len_logic())]
#[ensures(result == (ptr as *const T).offset_logic(index@))]
pub unsafe fn slice_get_unchecked_raw<T>(
    ptr: *const [T],
    index: usize,
    own: Ghost<&PtrOwn<[T]>>,
) -> *const T {
    unsafe { core::intrinsics::slice_get_unchecked(ptr, index) }
}

/// This only needs a `&PtrOwn` instead of `&mut PtrOwn` because it doesn't mutate anything.
#[trusted]
#[erasure(core::intrinsics::slice_get_unchecked::<*mut T, *mut [T], T>)]
#[requires(own.ptr() == ptr as *const [T])]
#[requires(index@ < ptr.len_logic())]
#[ensures(result == (ptr as *const T).offset_logic(index@) as *mut T)]
pub unsafe fn slice_get_unchecked_raw_mut<T>(
    ptr: *mut [T],
    index: usize,
    own: Ghost<&PtrOwn<[T]>>,
) -> *mut T {
    unsafe { core::intrinsics::slice_get_unchecked(ptr, index) }
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
