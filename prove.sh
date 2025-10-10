TARGETS="\
  block_get_2_ghost \
  split_at_unchecked \
  split_at_mut_unchecked \
  swap_unchecked \
  get_unchecked \
  get_unchecked_mut \
  get_unchecked_own \
  get_unchecked_mut_own \
  from_raw_parts_own \
  from_raw_parts_mut_own \
  left_mut_ghost \
  right_mut_ghost \
  left_ghost \
  right_ghost \
  div_mono_lemma \
  get \
  get_mut \
  index \
  index_mut \
  as_chunks_unchecked \
  as_chunks_unchecked_mut"
cargo creusot prove $TARGETS
