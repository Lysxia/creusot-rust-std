#![feature(new_range_api)]
#![feature(sized_type_properties)]
#![feature(portable_simd)]
#![feature(
    slice_ptr_get,
    ub_checks,
    fmt_internals,
    panic_internals,
    pointer_is_aligned_to,
    core_intrinsics,
    decl_macro,
    const_eval_select
)]
pub mod intrinsics;
pub mod ops;
pub mod ptr;
pub mod slice;
pub mod ub_checks;

// For `ub_checks::assert_unsafe_precondition`
extern crate self as verif_slice;
