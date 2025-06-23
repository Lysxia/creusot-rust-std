TARGETS="\
  verif/verif_slice_rlib/verif_slice/slice/M_block_get_2_ghost.coma \
  verif/verif_slice_rlib/verif_slice/slice/qyi2982588549540753363/M_split_at_unchecked.coma \
  verif/verif_slice_rlib/verif_slice/slice/qyi2982588549540753363/M_split_at_mut_unchecked.coma \
  verif/verif_slice_rlib/verif_slice/slice/qyi2982588549540753363/M_swap_unchecked.coma \
  verif/verif_slice_rlib/verif_slice/slice/qyi2982588549540753363/M_get_unchecked.coma \
  verif/verif_slice_rlib/verif_slice/slice/qyi2982588549540753363/M_get_unchecked_mut.coma \
  verif/verif_slice_rlib/verif_slice/slice/index/qyi16595746356105837460/M_get_unchecked_own.coma \
  verif/verif_slice_rlib/verif_slice/slice/index/qyi16595746356105837460/M_get_unchecked_mut_own.coma \
  verif/verif_slice_rlib/verif_slice/slice/raw/M_from_raw_parts_own.coma \
  verif/verif_slice_rlib/verif_slice/slice/raw/M_from_raw_parts_mut_own.coma \
  verif/verif_slice_rlib/verif_slice/ptr/qyi15487223444898855985/M_left_mut_ghost.coma \
  verif/verif_slice_rlib/verif_slice/ptr/qyi15487223444898855985/M_right_mut_ghost.coma \
  verif/verif_slice_rlib/verif_slice/ptr/qyi15487223444898855985/M_left_ghost.coma \
  verif/verif_slice_rlib/verif_slice/ptr/qyi15487223444898855985/M_right_ghost.coma"
cargo creusot prove $TARGETS
