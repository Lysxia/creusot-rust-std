use crate::intrinsics::const_eval_select;
use creusot_contracts::prelude::*;

#[macro_export]
macro_rules! assert_unsafe_precondition {
    ($kind:ident, $message:expr, $pre:expr, ($($name:ident:$ty:ty = $arg:expr),*$(,)?) => $e:expr $(,)?) => {
        {
            // This check is inlineable, but not by the MIR inliner.
            // The reason for this is that the MIR inliner is in an exceptionally bad position
            // to think about whether or not to inline this. In MIR, this call is gated behind `debug_assertions`,
            // which will codegen to `false` in release builds. Inlining the check would be wasted work in that case and
            // would be bad for compile times.
            //
            // LLVM on the other hand sees the constant branch, so if it's `false`, it can immediately delete it without
            // inlining the check. If it's `true`, it can inline it and get significantly better performance.
            #[rustc_no_mir_inline]
            #[inline]
            #[rustc_nounwind]
            #[requires($pre)]
            const fn precondition_check($($name:$ty),*) {
                // Add parentheses because this gets re-parsed by syn (via `requires`),
                // which interprets the expansion of `!$e` differently from the original `assert_unsafe_precondition`.
                if !($e) {
                    let msg = concat!("unsafe precondition(s) violated: ", $message,
                        "\n\nThis indicates a bug in the program. \
                        This Undefined Behavior check is optional, and cannot be relied on for safety.");
                    ::core::panicking::panic_nounwind_fmt(::core::fmt::Arguments::new_const(&[msg]), false);
                }
            }

            if ::verif_slice::ub_checks::$kind() {
                precondition_check($($arg,)*);
            }
        }
    };
}
pub use assert_unsafe_precondition;
pub use core::intrinsics::ub_checks as check_library_ub;

#[trusted]
#[erasure(private core::ub_checks::check_language_ub)]
pub(crate) fn check_language_ub() -> bool {
    // Only used for UB checks so we may const_eval_select.
    core::intrinsics::ub_checks()
        && const_eval_select!(
            @capture { } -> bool:
            if const {
                // Always disable UB checks.
                false
            } else {
                // Disable UB checks in Miri.
                !cfg!(miri)
            }
        )
}

#[erasure(private core::ub_checks::maybe_is_aligned_and_not_null)]
#[ensures(ptr.is_aligned_to_logic(align) && (is_zst || !ptr.is_null_logic()) ==> result)]
pub(crate) const fn maybe_is_aligned_and_not_null(
    ptr: *const (),
    align: usize,
    is_zst: bool,
) -> bool {
    // This is just for safety checks so we can const_eval_select.
    maybe_is_aligned(ptr, align) && (is_zst || !ptr.is_null())
}

#[trusted] // TODO: const_eval_select
#[erasure(private core::ub_checks::maybe_is_aligned)]
#[ensures(ptr.is_aligned_to_logic(align) ==> result)]
pub(crate) const fn maybe_is_aligned(ptr: *const (), align: usize) -> bool {
    // This is just for safety checks so we can const_eval_select.
    const_eval_select!(
        @capture { ptr: *const (), align: usize } -> bool:
        if const {
            true
        } else {
            ptr.is_aligned_to(align)
        }
    )
}

#[erasure(private core::ub_checks::is_valid_allocation_size)]
#[ensures((size@ > 0 ==> len@ <= isize::MAX@ / size@) == result)]
pub(crate) const fn is_valid_allocation_size(size: usize, len: usize) -> bool {
    let max_len = if size == 0 {
        usize::MAX
    } else {
        isize::MAX as usize / size
    };
    len <= max_len
}
