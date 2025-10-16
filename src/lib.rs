#![allow(internal_features)]
#![feature(
    new_range_api,
    sized_type_properties,
    portable_simd,
    slice_ptr_get,
    ub_checks,
    fmt_internals,
    panic_internals,
    pointer_is_aligned_to,
    core_intrinsics,
    decl_macro,
    const_eval_select,
    slice_swap_unchecked,
    slice_index_methods,
    rustc_allow_const_fn_unstable,
    slice_range,
    get_disjoint_mut_helpers
)]
pub mod intrinsics;
pub mod ops;
pub mod panic;
pub mod ptr;
pub mod slice;
pub mod ub_checks;

// For `ub_checks::assert_unsafe_precondition`
extern crate self as verif_slice;
