use super::PtrAddExt;
use crate::intrinsics::const_eval_select;
use crate::ub_checks;
use core::mem::SizedTypeProperties;
use creusot_std::{prelude::*, std::ptr::PtrLive};

impl<T> PtrAddExt<T> for *const T {
    #[requires(live.contains_range(self, count@))]
    #[ensures(result == self.offset_logic(count@))]
    #[erasure(<*const T>::add)]
    unsafe fn add_live(self, count: usize, live: Ghost<PtrLive<T>>) -> Self {
        #[trusted]
        // TODO
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
        unsafe { crate::intrinsics::add_live(self, count, live) }
    }

    #[requires(live.contains_range(self, - count@))]
    #[ensures(result == self.offset_logic(count@))]
    #[erasure(<*const T>::sub)]
    /* pub const */
    unsafe fn sub_live(self, count: usize, live: Ghost<PtrLive<T>>) -> *const T
    where
        T: Sized,
    {
        #[trusted]
        // #[cfg(debug_assertions)]
        #[inline]
        //#[rustc_allow_const_fn_unstable(const_eval_select)]
        #[ensures(result == (count@ * size@ <= isize::MAX@ && this.addr_logic()@ >= count@ * size@))]
        const fn runtime_sub_nowrap(this: *const (), count: usize, size: usize) -> bool {
            const_eval_select!(
                @capture { this: *const (), count: usize, size: usize } -> bool:
                if const {
                    true
                } else {
                    let Some(byte_offset) = count.checked_mul(size) else {
                        return false;
                    };
                    byte_offset <= (isize::MAX as usize) && this.addr() >= byte_offset
                }
            )
        }

        #[cfg(debug_assertions)] // Expensive, and doesn't catch much in the wild.
        ub_checks::assert_unsafe_precondition!(
            check_language_ub,
            "ptr::sub requires that the address calculation does not overflow",
            pearlite! { count@ * size@ <= isize::MAX@ && this.addr_logic()@ >= count@ * size@ },
            (
                this: *const () = self as *const (),
                count: usize = count,
                size: usize = size_of::<T>(),
            ) => runtime_sub_nowrap(this, count, size)
        );

        if T::IS_ZST {
            // Pointer arithmetic does nothing when the pointee is a ZST.
            self
        } else {
            // SAFETY: the caller must uphold the safety contract for `offset`.
            // Because the pointee is *not* a ZST, that means that `count` is
            // at most `isize::MAX`, and thus the negation cannot overflow.
            unsafe {
                crate::intrinsics::offset_live(
                    self,
                    crate::intrinsics::unchecked_sub_isize(0, count as isize),
                    live,
                )
            }
        }
    }
}
