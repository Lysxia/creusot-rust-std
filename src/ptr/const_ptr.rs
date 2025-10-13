use super::PtrAddExt;
use crate::intrinsics::const_eval_select;
use crate::ub_checks;
use creusot_contracts::{ghost::PtrOwn, *};

impl<T> PtrAddExt<T> for *const T {
    #[requires(self == own.ptr() as *const T)]
    #[requires(count@ <= own.len())]
    #[ensures(result == (own.ptr() as *const T).offset_logic(count@))]
    #[erasure(<*const T>::add)]
    unsafe fn add_own(self, count: usize, own: Ghost<&PtrOwn<[T]>>) -> Self {
        #[trusted]
        // #[cfg(debug_assertions)]
        // #[inline]
        // #[rustc_allow_const_fn_unstable(const_eval_select)]
        #[ensures(result == (count@ * size@ <= isize::MAX@ && this.addr_logic()@ + count@ * size@ <= usize::MAX@))]
        const fn runtime_add_nowrap(this: *const (), count: usize, size: usize) -> bool {
            const_eval_select!(
                @capture { this: *const (), count: usize, size: usize } -> bool:
                if const {
                    true
                } else {
                    let Some(byte_offset) = count.checked_mul(size) else {
                        return false;
                    };
                    let (_, overflow) = this.addr().overflowing_add(byte_offset);
                    byte_offset <= (isize::MAX as usize) && !overflow
                }
            )
        }

        #[cfg(debug_assertions)] // Expensive, and doesn't catch much in the wild.
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "ptr::add requires that the address calculation does not overflow",
            pearlite! { count@ * size@ <= isize::MAX@ && this.addr_logic()@ + count@ * size@ <= usize::MAX@ },
            (
                this: *const () = self as *const (),
                count: usize = count,
                size: usize = size_of::<T>(),
            ) => runtime_add_nowrap(this, count, size)
        );

        // SAFETY: the caller must uphold the safety contract for `offset`.
        unsafe { std::intrinsics::add_own(self, count, own) }
    }
}
