# Verifying `std` with Creusot

Work in progress

Goal: verify slice functions ([Verify Rust Std Challenge 17](https://model-checking.github.io/verify-rust-std/challenges/0017-slice.html))

### Verified unsafe functions

| Function | Safety | Erasure | Fun. correct | Notable trusted primitives and comments |
|-|-|-|-|-|
| get_unchecked           | ✅ | 🔧[^er-traits] | ✅ | Main challenge: general spec for indexing with both `usize` and ranges (subslicing) |
| get_unchecked_mut       | ✅ | 🔧[^er-traits] | ✅ | idem |
| swap_unchecked          | ✅ | ✅ | ✅ | `::core::ptr::swap` (`swap_disjoint`) |
| as_chunks_unchecked     | ✅ | ✅ | ✅ | `cast_chunks_perm` (ad hoc axiomatization of pointer cast) |
| as_chunks_unchecked_mut | ✅ | ✅ | ✅ | `cast_chunks_perm_mut` |
| split_at_unchecked      | ✅ | ✅ | ✅ | |
| split_at_mut_unchecked  | ✅ | ✅ | ✅ | |
| align_to                | ❌ | ❌ | ❌ | TODO: spec for pointer cast |
| align_to_mut            | ❌ | ❌ | ❌ | TODO: spec for pointer cast |
| get_disjoint_unchecked_mut | ❌ | ❌ | ❌ | TODO: MaybeUninit |

### Verified safe functions

| Function | Safety | Erasure | Fun. correct | Comments |
|-|-|-|-|-|
| first_chunk           | ✅ | ✅ | ✅ | `cast_array_perm` |
| first_chunk_mut       | ✅ | ✅ | ✅ | `cast_array_perm_mut` |
| split_first_chunk     | ✅ | ✅ | ✅ | idem |
| split_first_chunk_mut | ✅ | ✅ | ✅ | idem |
| split_last_chunk      | ✅ | ✅ | ✅ | idem |
| split_last_chunk_mut  | ✅ | ✅ | ✅ | idem |
| last_chunk            | ✅ | ✅ | ✅ | idem |
| last_chunk_mut        | ✅ | ✅ | ✅ | idem |
| reverse               | ✅ | 🔧[^reorder] | ✅ | |
| as_chunks             | ✅ | ✅ | ✅ | |
| as_chunks_mut         | ✅ | ✅ | ✅ | |
| as_rchunks            | ✅ | ✅ | ✅ | |
| split_at_checked      | ✅ | ✅ | ✅ | |
| split_at_mut_checked  | ✅ | ✅ | ✅ | |
| binary_search_by      | 🔧 | ✅ | 🚫 | TODO: Safety of function arguments |
| partition_dedup_by    | 🔧 | ✅ | 🚫 | idem |
| rotate_left           | ✅ | 🔧 | 🚫 | `copy`, `copy_nonoverlapping`, `read`, `write` |
| rotate_right          | ✅ | 🔧 | 🚫 | idem |
| copy_from_slice       | ✅ | 🔧[^reorder] | ✅ | `copy_nonoverlapping` |
| copy_within           | ✅ | 🔧[^er-traits] | ✅ | |
| swap_with_slice       | ✅ | 🔧[^reorder] | ✅ | |
| as_simd               | ❌ | ❌ | ❌ | TODO: spec for pointer cast |
| as_simd_mut           | ❌ | ❌ | ❌ | TODO: spec for pointer cast |
| get_disjoint_mut      | ❌ | ❌ | ❌ | |
| get_disjoint_check_valid | ❌ | ❌ | ❌ | |
| as_flattened          | ✅ | ✅ | ✅ | `cast_from_chunks_perm` |
| as_flattened_mut      | ✅ | ✅ | ✅ | `cast_from_chunks_perm_mut` |

🔧: work in progress
❌: to do
🚫: not planned (cases where functional correctness seems much harder than just safety)

[^reorder]: Some calls to `self.len()` were reordered due to additional lifetime constraints with permissions.
[^er-traits]: Erasure missing feature related to traits
