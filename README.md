# Verifying `std` with Creusot

Work in progress

Goal: verify slice functions ([Verify Rust Std Challenge 17](https://model-checking.github.io/verify-rust-std/challenges/0017-slice.html))

### Verified unsafe functions

| Function | Proof status | Notable trusted primitives and comments |
|-|-|-|
| get_unchecked | ✅ | Slice indexing with `usize` is an intrinsic, but this also includes indexing with ranges |
| get_unchecked_mut | ✅ | idem |
| swap_unchecked | ✅ | `::core::ptr::swap` (`swap_disjoint`) |
| as_chunks_unchecked | ✅ | `cast_array_perm` (ad hoc axiomatization of pointer cast) |
| as_chunks_unchecked_mut | ✅ | `cast_array_perm_mut` |
| split_at_unchecked | ✅ | |
| split_at_mut_unchecked | ✅ | |
| align_to | ❌ | Needs spec for pointer cast |
| align_to_mut | ❌ | Needs spec for pointer cast |
| get_disjoint_unchecked_mut | ❌ | |

### Verified safe functions

| Function | Proof status | Comments |
|-|-|-|
| first_chunk | ❌ | |
| first_chunk_mut | ❌ | |
| split_first_chunk | ❌ | |
| split_first_chunk_mut | ❌ | |
| split_last_chunk | ❌ | |
| split_last_chunk_mut | ❌ | |
| last_chunk | ❌ | |
| last_chunk_mut | ❌ | |
| reverse | ✅ | |
| as_chunks | ✅ | |
| as_chunks_mut | ✅ | |
| as_rchunks | ✅ | |
| split_at_checked | ✅ | |
| split_at_mut_checked | ✅ | |
| binary_search_by | ❌ | |
| partition_dedup_by | ❌ | |
| rotate_left | ❌ | |
| rotate_right | ❌ | |
| copy_from_slice | ❌ | |
| copy_within | ❌ | |
| swap_with_slice | ❌ | |
| as_simd | ❌ | Needs spec for pointer cast |
| as_simd_mut | ❌ | Needs spec for pointer cast |
| get_disjoint_mut | ❌ | |
| get_disjoint_check_valid | ❌ | |
| as_flattened | ❌ | |
| as_flattened_mut | ❌ | |
