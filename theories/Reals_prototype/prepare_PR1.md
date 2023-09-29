## Rdefinitions.v
- added the definition of the `pow` function (see the `Rpow.v` entry)

## RIneq.v
Many new lemmas. In general these offer:
- results about subtraction and division: these were not present and one had to
  unfold `Rdiv` or `Rminus` and use results about `Rinv` or `Ropp`
- finer control over the goal or hypotheses with common mathematical operations
  such as "move this term from left to right"
- more results about sign of operations and more common inequalities
Added lemmas :
- `Rgt_le_trans`
- `Rmult_neq_0_neq_0` as a shorter name for the very useful
  `Rmult_integral_contrapositive_currified`
- new families `Rmult_3_perm_???` and `Rplus_3_perm_???`
- `Rmult_4shift_r`, `Rmult_4shift_l`, `Rplus_4shift_l` and `Rplus_4shift_r`
- `Rminus_def_comm`
- `Rminus_opp_r`
- `Rminus_minus_distr`
- `Rminus_plus_r`
- `Rminus_plus_l`
- `Rminus_minus_opp_m`
- `Rminus_minus_opp_r`
- new families `R<pred>_<opp>_chsd_[lr][lr]` to "change the side of a term" in
  an equality or inequality.
  `<pred>` is one of `eq`, `le`, `lt`, `ge`, `gt`
  `<opp>` is one of `plus`, `minus`, `mult`, `div`
  first `l` or `r` is the place of the term we want to move in the left operand
  second `l` or `r` is the place were we want it in the second operand
- `Rmult_inv_l_id_m`
- `Rplus_le_gt_compat`
- `Rplus_gt_le_compat`
- `Rle_plus_nneg`
- `Rle_plus_npos`
- `Ropp_npos`
- `Ropp_nneg`
- `Rminus_le_swap`
- `Rminus_le_compat_r`
- `Rminus_le_reg_r`
- `Rminus_lt_compat_r`
- `Rminus_lt_reg_r`
- `Rminus_le_lt_mono`
- `Rminus_lt_le_mono`
- `Rminus_lt_lt_mono`
- `Rminus_le_le_mono`
- `Rle_minus_le`
- `Rmult_le_compat_reg_r`
- `Rmult_le_contravar_npos`
- `Rmult_lt_compat_neg_r` and `Rmult_lt_compat_neg_l`
- `Rmult_lt_contravar_neg`
- `Rmult_npos_lt_contravar`
- `Rmult_nneg_nneg` and `Rmult_npos_npos`
- `Rinv_nneg` and `Rinv_npos`
- `Rmult_ge_reg_l` and `Rmult_ge_reg_r`
- `Rmult_lt_reg_neg_l` and `Rmult_lt_reg_neg_r`
- `Rmult_le_reg_neg_l` and `Rmult_le_reg_neg_r`
- `Rmult_ge_reg_neg_l` and `Rmult_ge_reg_neg_r`
- `Rinv_pos_lt_cancel` and `Rinv_neg_lt_cancel`
- `Rinv_pos_le_cancel` and `Rinv_neg_le_cancel`
- `Rdiv_def_comm`
- `Rmult_div`
- `Rdiv_mult_id_l` and `Rdiv_mult_id_r`
- `Rdiv_opp_opp`
- `Rdiv_minus_minus_sym`
- `Rdiv_div_inv_m` and `Rdiv_div_inv_r`
- `Rdiv_lt_compat_r` and `Rdiv_lt_reg_r`
- `Rdiv_lt_reg_neg_r` and `Rdiv_lt_contravar_r`
- `Rdiv_gt_compat_r` and `Rdiv_gt_reg_r`
- `Rdiv_gt_reg_neg_r` and `Rdiv_gt_contravar_r`
- `Rdiv_le_compat_r` and `Rdiv_le_reg_r`
- `Rdiv_ge_compat_r` and `Rdiv_ge_reg_r`
- `Rdiv_le_reg_neg_r` and `Rdiv_ge_reg_neg_r`
- `Rdiv_le_contravar_r`
- `Rdiv_nneg_le_contravar_l`
- `Rdiv_pos_lt_compat_l`
- `Rdiv_neg_lt_contravar_l`
- `Rdiv_neg_lt_compat_l`
- `Rdiv_pos_pos_lt_cancel`
- `Rdiv_neg_neg_lt_cancel`
- `Rdiv_pos_lt_swap`
- `Rdiv_pos_nneg_le_swap`
- `Rdiv_nneg_nneg` and `Rdiv_npos_npos`
- `Rmult_m1_l` and `Rmult_m1_r`

## Rpow.v
- The file `Rpow.v` is removed. The definition of `pow` is now a part of
  `Rdefinitions.v` (this is to reduce the number of files in order to ease
  documentation)

## Raxioms.v
- `is_lower_bound` and `is_glb` added for symmetry
- the `bound` predicate has been renamed `bounded_from_above` (hidden notation
  `bounded` added for backwards compatibility)
