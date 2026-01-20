use creusot_std::prelude::*;

pub macro const_panic {
    ($const_msg:literal, $runtime_msg:literal, $($arg:ident : $ty:ty = $val:expr),* $(,)?) => {{
        #[trusted] // TODO: const_eval_select
        #[check(ghost_trusted)]
        #[requires(false)]
        const fn do_panic($($arg: $ty),*) -> ! {
            $crate::intrinsics::const_eval_select!(
                @capture { $($arg: $ty = $arg),* } -> !:
                #[noinline]
                if const #[track_caller] #[inline] { // Inline this, to prevent codegen
                    core::panic!($const_msg)
                } else #[track_caller] { // Do not inline this, it makes perf worse
                    core::panic!($runtime_msg)
                }
            )
        }

        do_panic($($val),*)
    }},
    // We support leaving away the `val` expressions for *all* arguments
    // (but not for *some* arguments, that's too tricky).
    ($const_msg:literal, $runtime_msg:literal, $($arg:ident : $ty:ty),* $(,)?) => {
        $crate::panic::const_panic!(
            $const_msg,
            $runtime_msg,
            $($arg: $ty = $arg),*
        )
    },
}
