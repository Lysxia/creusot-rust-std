#![allow(unused_variables)]
pub use ::core::intrinsics::const_eval_select;
use creusot_contracts::*;

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

pub const unsafe fn unchecked_sub<T: Copy>(x: T, y: T) -> T {
    panic!("intrinsics")
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
