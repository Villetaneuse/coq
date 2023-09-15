(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i Some properties about pow and sum have been made with John Harrison i*)
(*i Some Lemmas (about pow and powerRZ) have been done by Laurent Thery i*)

Require Export ArithRing. (* TODO: why? why Export? *)
From Coq Require Import Rdefinitions_prototype Raxioms_prototype RIneq_prototype.
Require Import Zpower Ztac.
Local Open Scope R_scope.

(* TODO: In general, harmonize names with english terms?
   This would mean (for instance)
   - nincr instead of decr
   - ndecr instead of incr
   - incr instead of incrstr
   - decr instead of decrstr
   - npos instead of neg
   - nneg instead of pos
   - pos instead of ???
   - neg instead of ???

   NEVER use neg instead of opp!!
*)

(*********************************************************)
(** **    Fractional and integer part                    *)
(*********************************************************)

Definition Int_part (r:R) : Z := (up r - 1)%Z.

Definition frac_part (r:R) : R := r - IZR (Int_part r).

(* TODO: rename this, state equivalence? *)
Lemma tech_up : forall (r:R) (z:Z), r < IZR z -> IZR z <= r + 1 -> z = up r.
Proof.
  intros r z Hlt Hle.
  destruct (archimed r) as [Hlt'%Rgt_lt Hle'%Rle_minus_chsd_rr].
  rewrite Rplus_comm in Hle'.
  apply Z.sub_move_0_r, one_IZR_lt1; rewrite minus_IZR; split;
    [rewrite IZR_NEG, <-Ropp_minus_distr; apply Ropp_lt_contravar |];
    now rewrite <-(Rplus_minus_l r 1); apply Rminus_le_lt_mono.
Qed.

(* NEW: name? *)
Lemma up_bounds : forall r, r < IZR (up r) <= r + 1.
Proof.
  intros r; destruct (archimed r) as [I J%Rle_minus_chsd_rr].
  now rewrite Rplus_comm.
Qed.

(* TODO: deprecate? *)
Lemma up_tech :
  forall (r:R) (z:Z), IZR z <= r -> r < IZR (z + 1) -> (z + 1)%Z = up r.
Proof.
  intros r z I J; apply tech_up with (1 := J).
  now rewrite plus_IZR; apply Rplus_le_compat_r.
Qed.

(* NEW *)
Lemma Ip_fp_charac : forall r z f,
    0 <= f < 1 /\ r = IZR z + f <-> Int_part r = z /\ frac_part r = f.
Proof.
  intros r z f; unfold frac_part, Int_part; split; intros [Hf Hz].
  - assert ((up r - 1)%Z = z) as ->. {
      apply Z.sub_move_r, eq_sym, tech_up; rewrite plus_IZR, Hz.
      + now apply Rplus_lt_compat_l.
      + now apply Rplus_le_compat_r, Rplus_0_le_ge.
    }
  now split; [| apply Req_minus_chsd_rr; rewrite Rplus_comm].
  - split; cycle 1.
    + now rewrite Hf in Hz; rewrite <-Hz, Rplus_minus.
    + rewrite <-Hz, minus_IZR, Rminus_minus_distr, <-Rplus_minus_swap; split.
      * now apply Rle_minus_le, up_bounds.
      * now apply Rminus_lt_swap; rewrite Rplus_minus_r; apply up_bounds.
Qed.

(* CHANGED since PR 17036: order of concl equalities, name, maybe throw away? *)
Lemma Int_part_frac_part_spec :
  forall r z f, 0 <= f < 1 -> r = (IZR z) + f ->
    Int_part r = z /\ frac_part r = f.
Proof. now intros r z f Hf Hz; apply Ip_fp_charac. Qed.

(* CHANGED since PR 17036: name, order of concl equalities, changed to equivalence *)
Lemma Ip_charac : forall r z, r - 1 < IZR z <= r <-> Int_part r = z.
Proof.
  intros r z; split; intros H.
  - apply (Ip_fp_charac _ _ (r - IZR z)).
    split; [| now rewrite Rplus_minus]; split; [now apply Rle_minus_le |].
    now apply Rminus_lt_swap.
  - destruct (Ip_fp_charac r z (r - IZR z)) as [_ [[H1 H2] _]].
      now unfold frac_part; rewrite <-H; easy.
    now split; [apply Rminus_lt_swap | apply Rle_minus_le].
Qed.

(* TODO: deprecate? *)
Lemma for_base_fp : forall r:R, IZR (up r) - r > 0 /\ IZR (up r) - r <= 1.
Proof.
  now intros r; destruct (archimed r) as [I J]; split; [apply Rgt_minus |].
Qed.

(* TODO: rename? change? *)
Lemma base_fp : forall r:R, frac_part r >= 0 /\ frac_part r < 1.
Proof.
  intros r; destruct (Ip_fp_charac r (Int_part r) (frac_part r)) as [_ H].
  now split; [apply Rle_ge |]; apply H.
Qed.

(* NEW *)
Lemma fp_bounds : forall r, 0 <= frac_part r < 1.
Proof.
  intros r; destruct (Ip_fp_charac r (Int_part r) (frac_part r)) as [_ H].
  now split; apply H.
Qed.

(* TODO: rename? change? deprecate? *)
Lemma base_Int_part :
  forall r:R, IZR (Int_part r) <= r /\ IZR (Int_part r) - r > -1.
Proof.
  intros r.
  destruct (Ip_charac r (Int_part r)) as [_ [H1 H2]]; [reflexivity |].
  split; [assumption |].
  apply (Rplus_lt_reg_r r).
  now rewrite Rplus_comm, Rminus_plus_r, <-(Rminus_def _ 1).
Qed.

(* NEW *)
Lemma Ip_bounds : forall r, r - 1 < IZR (Int_part r) <= r.
Proof. now intros r; destruct (Ip_charac r (Int_part r)) as [_ H]; apply H. Qed.

Lemma Int_part_INR : forall n:nat, Int_part (INR n) = Z.of_nat n.
Proof.
  intros n; apply Ip_charac; split; rewrite <-INR_IZR_INZ.
  - now apply Rlt_minus_chsd_rr, Rplus_pos_gt, Rlt_0_1.
  - now apply Rle_refl.
Qed.

(* CHANGED: name *)
Lemma Rplus_Ip_fp : forall r, r = IZR (Int_part r) + frac_part r.
Proof. now unfold frac_part; intros r; rewrite Rplus_minus. Qed.

(* TODO: name? change to  equivalence? *)
Lemma fp_nat : forall r:R, frac_part r = 0 ->  exists c : Z, r = IZR c.
Proof.
  intros r H; exists (Int_part r); rewrite (Rplus_Ip_fp r) at 1.
  now rewrite H, Rplus_0_r.
Qed.

(* TODO: name *)
Lemma fp_R0 : frac_part 0 = 0.
Proof.
  apply (Ip_fp_charac _ 0); split.
  - now split; [apply Rle_refl | apply Rlt_0_1].
  - now rewrite Rplus_0_r.
Qed.

(* TODO: name *)
Lemma R0_fp_O : forall r:R, 0 <> frac_part r -> 0 <> r.
Proof. now intros r H r_0; rewrite <-r_0, fp_R0 in H. Qed.

(* NEW: name? *)
Lemma Rminus_Ip_fp_r_le_l :
  forall r1 r2:R, frac_part r2 <= frac_part r1 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z /\
    frac_part (r1 - r2) = (frac_part r1 - frac_part r2).
Proof.
  intros r1 r2 H.
  apply (Int_part_frac_part_spec _ _ (frac_part r1 - frac_part r2)).
  - split; [now apply Rle_minus_le |].
    now rewrite <-Rminus_0_r; apply Rminus_lt_le_mono; apply fp_bounds.
  - rewrite (Rplus_Ip_fp r1) at 1; rewrite (Rplus_Ip_fp r2) at 1.
    rewrite Rplus_minus_swap, Rminus_plus_distr, <-minus_IZR.
    now rewrite <-Rplus_minus_swap, Rplus_minus_assoc.
Qed.

(* TODO: What's to do with this? *)
Lemma Rminus_Int_part1 :
  forall r1 r2:R, frac_part r1 >= frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2)%Z.
Proof. now intros r1 r2 H%Rge_le; apply Rminus_Ip_fp_r_le_l. Qed.

(* NEW : name? *)
Lemma Rminus_Ip_fp_l_lt_r :
  forall r1 r2:R, frac_part r1 < frac_part r2 ->
  Int_part (r1 - r2) = (Int_part r1 - Int_part r2 - 1)%Z /\
    frac_part (r1 - r2) = (frac_part r1 - frac_part r2 + 1).
Proof.
  intros r1 r2 H.
  apply (Int_part_frac_part_spec _ _ (frac_part r1 - frac_part r2 + 1)).
  - split.
    + rewrite <-Rplus_minus_swap; apply Rle_minus_le, (Rle_trans _ 1).
      * now left; apply fp_bounds.
      * now rewrite Rplus_comm; apply Rplus_0_le_ge, fp_bounds.
    + now rewrite <-(Rplus_0_l 1) at 2; apply Rplus_lt_compat_r, Rlt_minus.
  - rewrite (Rplus_Ip_fp r1) at 1; rewrite (Rplus_Ip_fp r2) at 1.
    rewrite !minus_IZR, Rplus_minus_swap, Rminus_plus_distr, <-Rplus_minus_swap.
    rewrite <-(Rplus_minus_swap _ _ 1), <-(Rplus_minus_assoc _ _ 1).
    now rewrite Rplus_minus_r, Rplus_minus_assoc.
Qed.

(* TODO: What's to do with this? *)
Lemma Rminus_Int_part2 :
  forall r1 r2:R, frac_part r1 < frac_part r2 ->
    Int_part (r1 - r2) = (Int_part r1 - Int_part r2 - 1)%Z.
Proof. now intros r1 r2 H; apply Rminus_Ip_fp_l_lt_r. Qed.

(* TODO: What's to do with this? *)
Lemma Rminus_fp1 :
  forall r1 r2:R, frac_part r1 >= frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2.
Proof. now intros r1 r2 H%Rge_le; apply Rminus_Ip_fp_r_le_l. Qed.

(* TODO: What's to do with this? *)
Lemma Rminus_fp2 :
  forall r1 r2:R, frac_part r1 < frac_part r2 ->
    frac_part (r1 - r2) = frac_part r1 - frac_part r2 + 1.
Proof. now intros r1 r2 H; apply Rminus_Ip_fp_l_lt_r. Qed.

(* NEW: name? *)
Lemma Rplus_fp_ge_1_plus :
  forall r1 r2, frac_part r1 + frac_part r2 >= 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2 + 1)%Z /\
    frac_part (r1 + r2) = frac_part r1 + frac_part r2 - 1.
Proof.
  intros r1 r2 H%Rge_le%(Rminus_le_compat_r 1); rewrite Rminus_diag in H.
  apply Int_part_frac_part_spec.
  - split; [exact H| ]; rewrite <-(Rplus_minus_r 1 1) at 2.
    now apply Rminus_lt_compat_r, Rplus_lt_compat; apply fp_bounds.
  - rewrite (Rplus_Ip_fp r1), (Rplus_Ip_fp r2) at 1.
    rewrite Rplus_minus_assoc, Rplus_minus_swap, 2plus_IZR, Rplus_minus_r.
    now rewrite <-Rplus_assoc, (Rplus_3perm_lrm (IZR _)), Rplus_assoc.
Qed.

(* NEW: name? *)
Lemma Rplus_fp_lt_1_plus :
  forall r1 r2, frac_part r1 + frac_part r2 < 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2)%Z /\
    frac_part (r1 + r2) = frac_part r1 + frac_part r2.
Proof.
  intros r1 r2 H; apply Int_part_frac_part_spec.
  - now split; [| exact H]; apply Rplus_nneg_nneg; apply fp_bounds.
  - rewrite (Rplus_Ip_fp r1), (Rplus_Ip_fp r2) at 1; rewrite <-2Rplus_assoc.
    now rewrite (Rplus_3perm_lrm (IZR _)), plus_IZR.
Qed.

(* TODO: What's to do with this? *)
Lemma plus_Int_part1 :
  forall r1 r2:R, frac_part r1 + frac_part r2 >= 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2 + 1)%Z.
Proof. now apply Rplus_fp_ge_1_plus. Qed.

(* TODO: What's to do with this? *)
Lemma plus_Int_part2 :
  forall r1 r2:R, frac_part r1 + frac_part r2 < 1 ->
    Int_part (r1 + r2) = (Int_part r1 + Int_part r2)%Z.
Proof. now apply Rplus_fp_lt_1_plus. Qed.

(* TODO: What's to do with this? *)
Lemma plus_frac_part1 :
  forall r1 r2:R, frac_part r1 + frac_part r2 >= 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2 - 1.
Proof. now apply Rplus_fp_ge_1_plus. Qed.

(* TODO: What's to do with this? *)
Lemma plus_frac_part2 :
  forall r1 r2:R, frac_part r1 + frac_part r2 < 1 ->
    frac_part (r1 + r2) = frac_part r1 + frac_part r2.
Proof. now apply Rplus_fp_lt_1_plus. Qed.

(****************************************************)
(** ** Rsqr : some results                          *)
(****************************************************)

(*************************************************)
(** ***   Rsqr : Purely algebraic properties     *)
(*************************************************)

(* TODO: TERRIBLE name! change to Rsqr_opp and change side *)
Lemma Rsqr_neg : forall x, x² = (- x)².
Proof. now intros x; unfold Rsqr; rewrite Rmult_opp_opp. Qed.

Lemma Rsqr_mult : forall x y, (x * y)² = x² * y².
Proof.
  intros x y; unfold Rsqr.
  now rewrite Rmult_assoc, <-(Rmult_assoc y x), (Rmult_comm y x), !Rmult_assoc.
Qed.

Lemma Rsqr_plus : forall x y, (x + y)² = x² + y² + 2 * x * y.
Proof.
  intros x y; unfold Rsqr; rewrite Rmult_plus_distr_l, 2Rmult_plus_distr_r.
  rewrite Rplus_assoc, <-(Rplus_assoc (y * x)), (Rmult_comm y x).
  now rewrite Rplus_diag, (Rplus_comm _ (y * y)), Rmult_assoc, !Rplus_assoc.
Qed.

Lemma Rsqr_minus : forall x y, (x - y)² = x² + y² - 2 * x * y.
Proof.
  intros x y.
  now rewrite !Rminus_def, Rsqr_plus, <-Rsqr_neg, <-Ropp_mult_distr_r.
Qed.

(* TODO: TERRIBLE name! change to Rsqr_minus_sym? *)
Lemma Rsqr_neg_minus : forall x y:R, (x - y)² = (y - x)².
Proof. now intros x y; rewrite <-Ropp_minus_distr, <-Rsqr_neg. Qed.

Lemma Rsqr_1 : 1² = 1.
Proof. now unfold Rsqr; rewrite Rmult_1_r. Qed.

(* TODO: find better name? maybe not possible? *)
Lemma Rsqr_div' : forall x y, (x / y)² = x² / y².
Proof. now unfold Rsqr; intros x y; rewrite Rmult_div. Qed.

(* TODO: move to compat part *)
Lemma Rsqr_div_depr : forall x y, y <> 0 -> (x / y)² = x² / y².
Proof. now intros x y _; apply Rsqr_div'. Qed.

#[deprecated(since="8.16",note="Use Rsqr_div'.")]
Notation Rsqr_div := Rsqr_div_depr.

(* TODO: rename? variable names? *)
Lemma Rsqr_minus_plus : forall a b, (a - b) * (a + b) = a² - b².
Proof.
  unfold Rsqr; intros a b; rewrite Rmult_plus_distr_l, 2Rmult_minus_distr_r.
  now rewrite (Rmult_comm b a), Rplus_minus_assoc, Rminus_plus_r.
Qed.

(* TODO: rename? variable names? *)
Lemma Rsqr_plus_minus : forall a b, (a + b) * (a - b) = a² - b².
Proof. now intros a b; rewrite Rmult_comm, Rsqr_minus_plus. Qed.

(* TODO: deprecate? this is already Rsqr_0_uniq in RIneq. *)
Lemma Rsqr_eq_0 : forall x, x² = 0 -> x = 0.
Proof. now apply Rsqr_0_uniq. Qed.

(* NEW *)
Lemma Rsqr_neq_0 : forall x, x <> 0 <-> x² <> 0.
Proof.
  unfold Rsqr; intros x; split; intros H.
  - now apply Rmult_integral_contrapositive.
  - now intros x_eq_0; rewrite x_eq_0, Rmult_0_l in H.
Qed.

Lemma Rsqr_inv' x : (/ x)² = / x².
Proof. now unfold Rsqr; now rewrite Rinv_mult.  Qed.

Lemma Rsqr_inv_depr : forall x, x <> 0 -> (/ x)² = / x².
Proof. now intros x _; apply Rsqr_inv'. Qed.

#[deprecated(since="8.16",note="Use Rsqr_inv'.")]
Notation Rsqr_inv := Rsqr_inv_depr.

Lemma Rsqr_canonical : forall a b c x, a <> 0 ->
    a * x² + b * x + c =
    a * (x + b / (2 * a))² + (4 * a * c - b²) / (4 * a).
Proof. (* This is a good test for our lemmas *)
  intros a b c x Ha.
  (* Usual developments *)
  rewrite Rsqr_plus, Rdiv_minus_distr, !Rmult_plus_distr_l, Rsqr_div', Rsqr_mult.
  (* 2² = 4 *)
  rewrite (Rsqr_def 2), <-mult_IZR; simpl Z.mul.
  (* "simplify" 4 * a * c / (4 * a) = c *)
  rewrite Rmult_div_r by
    (* 4 * a <> 0 *)
    (* TODO: partially revert 17036, or find shorter name *)
    now apply Rmult_neq_0_neq_0; [apply eq_IZR_contrapositive |].
  (* "simplify" the fraction in the 3rd summand *)
  rewrite <-!Rmult_assoc, !Rmult_div_assoc, (Rmult_comm a 2), Rmult_assoc.
  rewrite Rmult_div_r by
    now apply Rmult_neq_0_neq_0; [apply eq_IZR_contrapositive |].
  (* "simplify" by a in second summand *)
  rewrite (Rsqr_def a), <-(Rmult_assoc 4 a), Rdiv_mult_l_r by assumption.
  (* finally cancel second summand *)
  rewrite Rplus_minus_assoc, (Rplus_3perm_lrm _ _ (x * b)).
  now rewrite Rplus_minus_swap, Rplus_minus_r, (Rmult_comm b).
Qed.

(* TODO: deprecate? It seems nobody actually uses nonzeroreal *)
Lemma canonical_Rsqr :
  forall (a:nonzeroreal) (b c x:R),
    a * x² + b * x + c =
    a * (x + b / (2 * a))² + (4 * a * c - b²) / (4 * a).
Proof. now intros [a Ha] b c x; unfold Rsqr; field.  Qed.

(*************************************************)
(** ***   Sign                                   *)
(*************************************************)

(* TODO: deprecate? *)
Lemma Rsqr_gt_0_0 : forall x, 0 < x² -> x <> 0.
Proof. now intros x H%Rgt_not_eq; apply Rsqr_neq_0. Qed.

(* TODO: deprecate? There is already Rlt_0_sqr in RIneq. *)
Lemma Rsqr_pos_lt : forall x, x <> 0 -> 0 < x².
Proof. now apply Rlt_0_sqr. Qed.

(*************************************************)
(** ***   Variations on [0, \infty)              *)
(*************************************************)

(* TODO: think about name *)
Lemma Rsqr_incr : forall x y, 0 <= x -> x <= y -> x² <= y².
Proof. now intros x y Hx Hy; apply Rmult_le_compat. Qed.

(* TODO: think about name *)
Lemma Rsqr_incr_rev : forall x y, 0 <= y -> x² <= y² -> x <= y.
Proof.
  intros x y Hy H%Rle_not_lt; apply Rnot_lt_le; intros Hxy; apply H.
  now apply Rmult_le_0_lt_compat.
Qed.

(* TODO: think about name *)
(* NEW *)
Lemma Rsqr_le_nneg :
  forall x y, 0 <= x -> 0 <= y -> (x <= y <-> x² <= y²).
Proof.
  (* 0 <= x is useful for ->, 0 <= y is useful for <- *)
  intros x y Hx Hy; split; intros H.
  - now apply Rsqr_incr.
  - now apply Rsqr_incr_rev.
Qed.

(* TODO: think about name *)
(* NEW *)
Lemma Rsqr_incrst : forall x y, 0 <= x -> x < y -> x² < y².
Proof. now intros x y Hx Hy; apply Rmult_le_0_lt_compat. Qed.

(* TODO: think about name *)
(* NEW *)
Lemma Rsqr_incrst_rev : forall x y, 0 <= y -> x² < y² -> x < y.
Proof.
  intros x y Hy H%Rlt_not_le; apply Rnot_le_lt; intros Hxy; apply H.
  now apply Rmult_le_compat.
Qed.

(* TODO: think about name *)
(* NEW *)
Lemma Rsqr_lt_nneg :
  forall x y, 0 <= x -> 0 <= y -> (x < y <-> x² < y²).
Proof.
  (* 0 <= x is useful for ->, 0 <= y is useful for <- *)
  intros x y Hx Hy; split; intros H.
  - now apply Rsqr_incrst.
  - now apply Rsqr_incrst_rev.
Qed.

Lemma Rsqr_inj : forall x y:R, 0 <= x -> 0 <= y -> x² = y² -> x = y.
Proof.
  intros x y Hx Hy H; apply Rle_antisym.
  - now apply Req_le in H; apply Rsqr_le_nneg.
  - now apply eq_sym, Req_le in H; apply Rsqr_le_nneg.
Qed.

(* TODO: deprecate *)
Lemma Rsqr_incr_0 :
  forall x y:R, x² <= y² -> 0 <= x -> 0 <= y -> x <= y.
Proof.
  intros x y Hsq Hx Hy; apply Rnot_lt_le; intros Hyx.
  apply (Rle_not_lt (y²) (x²)); [assumption |].
  now apply Rmult_le_0_lt_compat.
Qed.

(* TODO: deprecate, order of hyps is bad... *)
Lemma Rsqr_incr_0_var : forall x y:R, x² <= y² -> 0 <= y -> x <= y.
Proof.
  intros x y Hsqr Hy; destruct (Rle_or_lt 0 x) as [I | I].
  - now apply Rsqr_incr_0.
  - now left; apply (Rlt_le_trans _ 0).
Qed.

(* TODO: deprecate *)
Lemma Rsqr_incr_1 :
  forall x y:R, x <= y -> 0 <= x -> 0 <= y -> x² <= y².
Proof. now intros x y Hxy Hx _; apply Rsqr_incr. Qed.

(* TODO: deprecate *)
Lemma Rsqr_incrst_0 :
  forall x y:R, x² < y² -> 0 <= x -> 0 <= y -> x < y.
Proof. now intros x y H _ Hy; apply Rsqr_incrst_rev. Qed.

(* TODO: deprecate *)
Lemma Rsqr_incrst_1 :
  forall x y:R, x < y -> 0 <= x -> 0 <= y -> x² < y².
Proof. now intros x y H H' _; apply Rsqr_incrst. Qed.

(*************************************************)
(** ***   Variations on (-\infty, 0]             *)
(*************************************************)

(* NEW *)
Lemma Rsqr_decr : forall x y, y <= 0 -> x <= y -> y² <= x².
Proof.
  intros x y Hy Hx.
  apply Rmult_le_contravar_npos; try assumption.
  now apply (Rle_trans _ y).
Qed.

(* NEW *)
Lemma Rsqr_decr_rev : forall x y, x <= 0 -> y² <= x² -> x <= y.
Proof.
  intros x y Hx H%Rle_not_lt; apply Rnot_lt_le; intros H'; apply H.
  now apply Rmult_npos_lt_contravar.
Qed.

(* NEW *)
Lemma Rsqr_decrst : forall x y, y <= 0 -> x < y -> y² < x².
Proof. now intros x y Hy H; apply Rmult_npos_lt_contravar. Qed.

(* NEW *)
Lemma Rsqr_decrst_rev : forall x y, x <= 0 -> y² < x² -> x < y.
Proof.
  intros x y Hx H%Rlt_not_le; apply Rnot_le_lt; intros H'; apply H.
  assert (I : y <= 0) by now apply (Rle_trans _ x).
  now apply Rmult_le_contravar_npos.
Qed.

(* NEW *)
Lemma Rsqr_le_npos :
  forall x y, x <= 0 -> y <= 0 -> (x <= y <-> y² <= x²).
Proof.
  intros x y Hx Hy; split; intros H.
  - now apply Rsqr_decr.
  - now apply Rsqr_decr_rev.
Qed.

(* NEW *)
Lemma Rsqr_lt_npos :
  forall x y, x <= 0 -> y <= 0 -> (x < y <-> y² < x²).
Proof.
  intros x y Hx Hy; split; intros H.
  - now apply Rsqr_decrst.
  - now apply Rsqr_decrst_rev.
Qed.

(* NEW *)
Lemma Rsqr_inj_npos :
  forall x y, x <= 0 -> y <= 0 -> x² = y² -> x = y.
Proof.
  intros x y Hx Hy H; apply Rle_antisym.
  - now apply eq_sym, Req_le in H; apply Rsqr_le_npos.
  - now apply Req_le in H; apply Rsqr_le_npos.
Qed.

(***************************************)
(** **        Rmin and Rmax            *)
(***************************************)

Definition Rmin (x y:R) : R :=
  match Rle_dec x y with
    | left _ => x
    | right _ => y
  end.

Definition Rmax (x y:R) : R :=
  match Rle_dec x y with
    | left _ => y
    | right _ => x
  end.

(* Encapsulation lemmas *)
(* Variable names... *)
Lemma Rmin_left : forall x y, x <= y -> Rmin x y = x.
Proof.
  unfold Rmin; intros x y H; destruct (Rle_dec x y) as [Hle | Hnle].
  - reflexivity.
  - now exfalso; apply Hnle.
Qed.

(* NEW *)
Lemma Rmin_right_lt : forall x y, y < x -> Rmin x y = y.
Proof.
  unfold Rmin; intros x y H; destruct (Rle_dec x y) as [Hle | Hnle].
  - now exfalso; apply Rlt_not_le with (1 := H).
  - reflexivity.
Qed.

(* Variable names... *)
Lemma Rmax_left : forall x y, y <= x -> Rmax x y = x.
Proof.
  unfold Rmax; intros x y H; destruct (Rle_dec x y) as [Hle | Hnle].
  - now apply Rle_antisym.
  - reflexivity.
Qed.

(* NEW *)
Lemma Rmax_right_lt : forall x y, x < y -> Rmax x y = y.
Proof.
  unfold Rmax; intros x y H; destruct (Rle_dec x y) as [Hle | Hnle].
  - reflexivity.
  - now exfalso; apply Hnle; left.
Qed.
(* End of encapsulation lemmas, no more unfold after these lines. *)

(* NEW *)
Lemma Rmax_left_lt : forall x y, y < x -> Rmax x y = x.
Proof. now intros x y H%Rlt_le; apply Rmax_left. Qed.

Lemma Rmax_right : forall x y, x <= y -> Rmax x y = y.
Proof.
  intros x y [I%Rmax_right_lt | ->]; [ assumption |].
  now apply Rmax_left, Rle_refl.
Qed.

Lemma Rmin_right : forall x y, y <= x -> Rmin x y = y.
Proof.
  intros x y [I | ->].
  - now rewrite Rmin_right_lt.
  - now rewrite Rmin_left by apply Rle_refl.
Qed.

(* NEW *)
Lemma Rmin_left_lt : forall x y, x < y -> Rmin x y = x.
Proof. now intros x y H%Rlt_le; apply Rmin_left. Qed.

Inductive Rmin_max_spec_le (x y : R) : R -> R -> Type :=
    Rmin_max_spec_le_l (H : x <= y) : Rmin_max_spec_le x y x y
  | Rmin_max_spec_le_r (H : y <= x) : Rmin_max_spec_le x y y x.

Lemma Rmin_max_leP : forall x y, Rmin_max_spec_le x y (Rmin x y) (Rmax x y).
Proof.
  intros x y; destruct (Rle_gt_dec x y) as [I | I%Rlt_le].
  - now rewrite Rmin_left, Rmax_right by assumption; apply Rmin_max_spec_le_l.
  - now rewrite Rmin_right, Rmax_left by assumption; apply Rmin_max_spec_le_r.
Qed.

(* NEW *)
Lemma Rmin_left_or_right : forall x y, Rmin x y = x \/ Rmin x y = y.
Proof.
  now intros x y; destruct (Rmin_max_leP x y) as [I | J];  [left | right].
Qed.

Lemma Rmin_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmin r1 r2).
Proof.
  now intros r1 r2 P H1 H2; destruct (Rmin_max_leP r1 r2) as [I | I].
Qed.

Lemma Rmin_case_strong : forall r1 r2 (P:R -> Type),
  (r1 <= r2 -> P r1) -> (r2 <= r1 -> P r2) -> P (Rmin r1 r2).
Proof.
  now intros r1 r2 P H1 H2; destruct (Rmin_max_leP r1 r2) as [I%H1 | I%H2].
Qed.

(* Order of variables... I follow the other lemmas but it should be r first. *)
(* NEW *)
Lemma Rmin_Rle : forall r1 r2 r, r <= r1 /\ r <= r2 <-> r <= Rmin r1 r2.
Proof.
  intros r1 r2 r; split; destruct (Rmin_max_leP r1 r2) as [I | I]; try easy.
  - intros H; split; [assumption | now apply Rle_trans with (2 := I)].
  - intros H; split; [now apply Rle_trans with (2 := I) | assumption].
Qed.

(* TODO: name *)
(* NEW *)
Lemma Rmin_spec :
  forall r1 r2 m, (forall r, r <= m <-> r <= r1 /\ r <= r2) -> m = Rmin r1 r2.
Proof.
  intros r1 r2 m Hm; apply Rle_antisym.
  - apply Rmin_Rle, Hm, Rle_refl.
  - apply Hm, Rmin_Rle, Rle_refl.
Qed.

(* Name of variables... *)
Lemma Rmin_l : forall x y, Rmin x y <= x.
Proof. now intros x y; apply <-(Rmin_Rle x y); apply Rle_refl. Qed.

Lemma Rmin_r : forall x y:R, Rmin x y <= y.
Proof. now intros x y; apply <-(Rmin_Rle x y); apply Rle_refl. Qed.

Lemma Rmin_Rgt_l : forall r1 r2 r, Rmin r1 r2 > r -> r1 > r /\ r2 > r.
Proof.
  intros r1 r2 r; destruct (Rmin_max_leP r1 r2) as [I | I]; intros H; split;
    try easy; now apply Rlt_le_trans with (1 := H).
Qed.

Lemma Rmin_Rgt_r : forall r1 r2 r, r1 > r /\ r2 > r -> Rmin r1 r2 > r.
Proof.
  now intros r1 r2 r [H1 H2]; destruct (Rmin_max_leP r1 r2) as [I | I].
Qed.

Lemma Rmin_Rgt : forall r1 r2 r, Rmin r1 r2 > r <-> r1 > r /\ r2 > r.
Proof. now intros r1 r2 r; split; [apply Rmin_Rgt_l | apply Rmin_Rgt_r]. Qed.

Lemma Rle_min_compat_r : forall x y z, x <= y -> Rmin x z <= Rmin y z.
Proof.
  intros x y z H; apply Rmin_Rle; split.
  - now apply Rle_trans with (2 := H); apply Rmin_l.
  - now apply Rmin_r.
Qed.

Lemma Rmin_comm : forall x y:R, Rmin x y = Rmin y x.
Proof.
  now intros x y; destruct (Rmin_max_leP x y) as [->%Rmin_right | ->%Rmin_left].
Qed.

Lemma Rle_min_compat_l : forall x y z, x <= y -> Rmin z x <= Rmin z y.
Proof.
  now intros x y z H; rewrite 2(Rmin_comm z _); apply Rle_min_compat_r.
Qed.

Lemma Rmin_stable_in_posreal : forall x y:posreal, 0 < Rmin x y.
Proof. now intros [x Hx] [y Hy]; apply Rmin_Rgt_r. Qed.

Lemma Rmin_pos : forall x y:R, 0 < x -> 0 < y -> 0 < Rmin x y.
Proof. now intros x y Hx Hy; apply Rmin_Rgt_r. Qed.

(* One direction of Rmin_Rle *)
Lemma Rmin_glb : forall x y z:R, z <= x -> z <= y -> z <= Rmin x y.
Proof. now intros x y z Hx Hy; apply Rmin_Rle; split. Qed.

(* Almost the same as Rmin_Rgt_r, one direction of Rmin_Rgt *)
Lemma Rmin_glb_lt : forall x y z:R, z < x -> z < y -> z < Rmin x y.
Proof. now intros x y z Hx Hy; apply Rmin_Rgt; split. Qed.

(* NEW *)
Lemma Rmax_left_or_right : forall x y, Rmax x y = x \/ Rmax x y = y.
Proof.
  now intros x y; destruct (Rmin_max_leP x y) as [I | I]; [right | left].
Qed.

Lemma Rmax_case : forall r1 r2 (P:R -> Type), P r1 -> P r2 -> P (Rmax r1 r2).
Proof. now intros x y H1 H2; destruct (Rmin_max_leP x y) as [I | I]. Qed.

Lemma Rmax_case_strong : forall r1 r2 (P:R -> Type),
  (r2 <= r1 -> P r1) -> (r1 <= r2 -> P r2) -> P (Rmax r1 r2).
Proof.
  now intros x y P H1 H2; destruct (Rmin_max_leP x y) as [I%H2 | I%H1].
Qed.

(* TODO : same for Rmin *)
Lemma Rmax_Rle : forall r1 r2 r, r <= Rmax r1 r2 <-> r <= r1 \/ r <= r2.
Proof.
  intros r1 r2 r; split.
  - now intros H; destruct (Rmax_left_or_right r1 r2) as [<- | <-]; [left | right].
  - now destruct (Rmin_max_leP r1 r2) as [I | I]; intros [J | J]; try easy;
      apply Rle_trans with (1 := J).
Qed.

Lemma Rmax_lub : forall x y z:R, x <= z -> y <= z -> Rmax x y <= z.
Proof.
  now intros x y z Hx Hy; destruct (Rmax_left_or_right x y) as [-> | ->].
Qed.

Lemma Rmax_lub_lt : forall x y z:R, x < z -> y < z -> Rmax x y < z.
Proof.
  now intros x y z Hx Hy; destruct (Rmax_left_or_right x y) as [-> | ->].
Qed.

(* TODO: Rmax_Rlt and Rmax_Rle have almost the same name but for completely
 * different results... *)
Lemma Rmax_Rlt : forall x y z, Rmax x y < z <-> x < z /\ y < z.
Proof.
  now intros x y z; destruct (Rmin_max_leP x y) as [I | I]; split; try easy;
    intros H; split; try easy; apply Rle_lt_trans with (1 := I).
Qed.

(* NEW *)
Lemma Rmax_le : forall x y z, Rmax x y <= z <-> x <= z /\ y <= z.
Proof.
  now intros x y z; destruct (Rmin_max_leP x y) as [I | I]; split; try easy;
    intros H; split; try easy; apply Rle_trans with (1 := I).
Qed.

Lemma Rmax_l : forall x y:R, x <= Rmax x y.
Proof.
  now intros x y; destruct (Rmin_max_leP x y) as [I | I]; [| apply Rle_refl].
Qed.

Lemma Rmax_r : forall x y:R, y <= Rmax x y.
Proof.
  now intros x y; destruct (Rmin_max_leP x y) as [I | I]; [apply Rle_refl |].
Qed.

Lemma Rmax_comm : forall x y:R, Rmax x y = Rmax y x.
Proof.
  now intros x y; destruct (Rmin_max_leP x y) as [->%Rmax_left | ->%Rmax_right].
Qed.

(* begin hide *)
Notation RmaxSym := Rmax_comm (only parsing).
Notation RmaxLess1 := Rmax_l (only parsing).
Notation RmaxLess2 := Rmax_r (only parsing).
(* end hide *)

Lemma Rle_max_compat_r : forall x y z, x <= y -> Rmax x z <= Rmax y z.
Proof.
  intros x y z H; apply Rmax_lub.
  - now apply Rle_trans with (1 := H); apply Rmax_l.
  - now apply Rmax_r.
Qed.

Lemma Rle_max_compat_l : forall x y z, x <= y -> Rmax z x <= Rmax z y.
Proof.
  now intros x y z H; rewrite 2(Rmax_comm z _); apply Rle_max_compat_r.
Qed.

(* Variable names... *)
Lemma RmaxRmult :
  forall (p q:R) r, 0 <= r -> Rmax (r * p) (r * q) = r * Rmax p q.
Proof.
  intros p q r H; destruct (Rmin_max_leP p q) as [I | I].
  - now apply Rmax_right, Rmult_le_compat_l.
  - now apply Rmax_left, Rmult_le_compat_l.
Qed.

Lemma Rmax_neg : forall x y:R, x < 0 -> y < 0 -> Rmax x y < 0.
Proof. now intros x y Hx Hy; apply Rmax_Rlt; split. Qed.

Lemma Rmax_stable_in_negreal : forall x y:negreal, Rmax x y < 0.
Proof.  now intros [x Hx] [y Hy]; apply Rmax_neg.  Qed.

Lemma Ropp_Rmax : forall x y, - Rmax x y = Rmin (-x) (-y).
Proof.
  intros x y; destruct (Rmin_max_leP x y) as [I | I].
  - now rewrite Rmin_right; [| apply Ropp_le_contravar].
  - now rewrite Rmin_left; [| apply Ropp_le_contravar].
Qed.

Lemma Ropp_Rmin : forall x y, - Rmin x y = Rmax (-x) (-y).
Proof.
  intros x y; destruct (Rmin_max_leP x y) as [I | I].
  - now rewrite Rmax_left; [| apply Ropp_le_contravar].
  - now rewrite Rmax_right; [| apply Ropp_le_contravar].
Qed.

Lemma Rmax_assoc : forall a b c, Rmax a (Rmax b c) = Rmax (Rmax a b) c.
Proof.
  intros a b c; apply Rle_antisym; apply Rmax_lub.
  - now apply (Rle_trans _ (Rmax a b)); apply Rmax_l.
  - now apply Rle_max_compat_r, Rmax_r.
  - now apply Rle_max_compat_l, Rmax_l.
  - now apply (Rle_trans _ (Rmax b c)); apply Rmax_r.
Qed.

Lemma Rminmax : forall a b, Rmin a b <= Rmax a b.
Proof. now intros a b; apply Rmax_Rle; left; apply Rmin_l. Qed.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) =
  Rmin (Rmin x y) z.
Proof.
  intros a b c; apply Rle_antisym; apply Rmin_glb.
  - now apply Rle_min_compat_l, Rmin_l.
  - now apply (Rle_trans _ (Rmin b c)); apply Rmin_r.
  - now apply (Rle_trans _ (Rmin a b)); apply Rmin_l.
  - now apply Rle_min_compat_r, Rmin_r.
Qed.


(*******************************)
(** **     Absolute value      *)
(*******************************)

Lemma Rcase_abs : forall r, {r < 0} + {r >= 0}.
Proof.
  now intros r; destruct (Rle_lt_dec 0 r) as [I%Rle_ge | J]; [right | left].
Qed.

Definition Rabs r : R :=
  match Rcase_abs r with
    | left _ => - r
    | right _ => r
  end.

(* TODO: name *)
Lemma Rabs_left : forall r, r < 0 -> Rabs r = - r.
Proof.
  unfold Rabs; intros r; destruct (Rcase_abs r) as [_ | J]; [reflexivity |].
  now intros H%Rlt_not_ge.
Qed.

(* TODO: name *)
Lemma Rabs_right : forall r, r >= 0 -> Rabs r = r.
Proof.
  unfold Rabs; intros r; destruct (Rcase_abs r) as [I | _]; [| reflexivity].
  now intros H%Rge_not_lt.
Qed.
(* no more unfold Rabs after this line *)

(* NOTE: this is probably good for dev, less for teaching... *)
Inductive Rabs_spec_le (x : R) : R -> Prop :=
    Rabs_spec_le_l (h : x <= 0) : Rabs_spec_le x (- x)
  | Rabs_spec_le_r (h : 0 <= x) : Rabs_spec_le x x.

(* NOTE: this is probably good for dev, less for teaching... *)
Inductive Rabs_spec_lt (x : R) : R -> Prop :=
    Rabs_spec_lt_l (h : x < 0) : Rabs_spec_lt x (- x)
  | Rabs_spec_lt_m (h : x = 0) : Rabs_spec_lt x 0
  | Rabs_spec_lt_r (h : x > 0) : Rabs_spec_lt x x.

(* TODO: write manual *)
(* TODO: Prop or Type? *)
(* TODO: I want to hide the constructors from the rest of the world, how to do
 * so ? *)

(* NEW *)
Lemma Rabs_leP : forall x, Rabs_spec_le x (Rabs x).
Proof.
  intros x; destruct (Rlt_or_ge x 0) as [I | J].
  - now rewrite Rabs_left by assumption; apply Rabs_spec_le_l; left.
  - now rewrite Rabs_right by assumption; apply Rabs_spec_le_r, Rge_le.
Qed.

(* NEW *)
Lemma Rabs_ltP : forall x, Rabs_spec_lt x (Rabs x).
Proof.
  intros x; destruct (Rtotal_order x 0) as [I | [E | I]].
  - now rewrite Rabs_left by assumption; apply Rabs_spec_lt_l.
  - now rewrite E; rewrite Rabs_right by (apply Rge_refl); apply Rabs_spec_lt_m.
  - now rewrite Rabs_right by (now left); apply Rabs_spec_lt_r.
Qed.

(* TODO: at least create an alias Rabs_0 *)
Lemma Rabs_R0 : Rabs 0 = 0.
Proof. now rewrite Rabs_right; [reflexivity |]; apply Rge_refl. Qed.

(* TODO deprecate Rabs_R0 ? *)
Definition Rabs_0 := Rabs_R0.

(* TODO: name and variable names *)
Lemma Rabs_left1 : forall a:R, a <= 0 -> Rabs a = - a.
Proof. now intros a [I%Rabs_left | ->]; [| rewrite Ropp_0, Rabs_0]. Qed.

(* NEW: better names *)
Definition Rabs_neg_opp := Rabs_left.
Definition Rabs_npos_opp := Rabs_left1.

(* NEW *)
Lemma Rabs_nneg_id : forall r, 0 <= r -> Rabs r = r.
Proof. now intros r H%Rle_ge; apply Rabs_right. Qed.

(* NEW *)
Lemma Rabs_pos_id : forall r, r > 0 -> Rabs r = r.
Proof. now intros r H%Rgt_ge; apply Rabs_right. Qed.

Lemma Rabs_id_or_opp : forall r, Rabs r = r \/ Rabs r = -r.
Proof. now intros r; destruct (Rabs_leP r); [right | left]. Qed.

(* TODO: at least create an alias Rabs_1 *)
Lemma Rabs_R1 : Rabs 1 = 1.
Proof. now apply Rabs_right, Rle_ge, Rle_0_1. Qed.

(* TODO deprecate Rabs_R1 ? *)
Definition Rabs_1 := Rabs_R1.

(* TODO: deprecate or rename or alias *)
Lemma Rabs_no_R0 : forall r, r <> 0 -> Rabs r <> 0.
Proof.
  intros r; destruct (Rabs_ltP r) as [I | I | I]; try easy.
  now apply Ropp_neq_0_compat.
Qed.

(* TODO deprecate Rabs_R0? NOTE: neq_0 is present in the library *)
Lemma Rabs_neq_0 : forall r, r <> 0 <-> Rabs r <> 0.
Proof.
  intros r; split; destruct (Rabs_ltP r) as [I | I | I]; try easy;
    [ now apply Ropp_neq_0_compat | now intros H H'; rewrite H', Ropp_0 in H].
Qed.

(* TODO: deprecate or rename or alias *)
Lemma Rabs_pos : forall x, 0 <= Rabs x.
Proof. now intros x; destruct (Rabs_leP x) as [I%Ropp_npos | I]. Qed.

(* NEW *)
Lemma Rabs_nneg : forall x, 0 <= Rabs x.
Proof. now intros x; destruct (Rabs_leP x) as [I%Ropp_npos | I]. Qed.

Lemma Rle_abs : forall x, x <= Rabs x.
Proof.
  intros x; destruct (Rabs_leP x) as [I | I]; [| now apply Rle_refl].
  now apply Rle_trans with (1 := I), Ropp_npos.
Qed.

Definition RRle_abs := Rle_abs.

(* TODO: name *)
(* NEW *)
Lemma Rabs_le_iff : forall x y, Rabs x <= y <-> - y <= x <= y.
Proof.
  intros x y; split.
  - intros H; assert (Ic : - y <= Rabs x <= y). {
      split; [| assumption]; apply Rle_trans with (2 := (Rabs_pos x)).
      now apply Ropp_nneg, Rle_trans with (1 := (Rabs_nneg x)).
    }
    destruct (Rabs_id_or_opp x) as [Hx | Hx]; rewrite Hx in Ic; [assumption |].
    destruct Ic as [I%Ropp_le_cancel J].
    now rewrite <-(Ropp_involutive y) in J; apply Ropp_le_cancel in J.
  - destruct (Rabs_id_or_opp x) as [-> | ->]; intros H; [easy |].
    now rewrite <-(Ropp_involutive y); apply Ropp_le_contravar.
Qed.

(* TODO: name *)
(* NEW *)
Lemma Rabs_lt_iff : forall x y, Rabs x < y <-> - y < x < y.
Proof.
  intros x y; split.
  - intros H; assert (Ic : - y < Rabs x < y). {
      split; [| assumption]; apply Rlt_le_trans with (2 := (Rabs_pos x)).
      now apply Ropp_pos, Rgt_le_trans with (2 := Rabs_nneg x).
    }
    destruct (Rabs_id_or_opp x) as [Hx | Hx]; rewrite Hx in Ic; [assumption |].
    destruct Ic as [I%Ropp_lt_cancel J].
    now rewrite <-(Ropp_involutive y) in J; apply Ropp_lt_cancel in J.
  - destruct (Rabs_id_or_opp x) as [-> | ->]; intros H; [easy |].
    now rewrite <-(Ropp_involutive y); apply Ropp_lt_contravar.
Qed.

(* TODO: not very informative name, variable names *)
Lemma Rabs_le : forall a b, - b <= a <= b -> Rabs a <= b.
Proof. now apply Rabs_le_iff. Qed.

(* TODO: deprecate or rename or alias, almost the same as Rabs_right, same as
   (imho better-named) Rabs_nneg_id *)
Lemma Rabs_pos_eq : forall x:R, 0 <= x -> Rabs x = x.
Proof. exact Rabs_nneg_id. Qed.

(* TODO: rename *)
Lemma Rabs_Rabsolu : forall x:R, Rabs (Rabs x) = Rabs x.
Proof. now intro x; rewrite Rabs_nneg_id; [easy |]; apply Rabs_pos. Qed.

(* TODO: rename *)
Lemma Rabs_pos_lt : forall x:R, x <> 0 -> 0 < Rabs x.
Proof.
  intros x; destruct (Rabs_pos x) as [| E]; [intros _; assumption |].
  now intros H%Rabs_no_R0%not_eq_sym; exfalso.
Qed.

(* TODO: name *)
Lemma Rabs_Ropp : forall x:R, Rabs (- x) = Rabs x.
Proof.
  intros x; destruct (Rabs_leP x) as [I | I].
  - now rewrite Rabs_nneg_id by (now apply Ropp_npos).
  - now rewrite Rabs_npos_opp by (now apply Ropp_nneg); rewrite Ropp_involutive.
Qed.

(* NEW *)
Lemma Rabs_eq_abs : forall r1 r2, Rabs r1 = Rabs r2 <-> r1 = r2 \/ r1 = - r2.
Proof.
  intros r1 r2; split.
  - destruct (Rabs_id_or_opp r1) as [-> | ->];
    destruct (Rabs_id_or_opp r2) as [-> | ->]; intros H.
    + now left.
    + now right.
    + now right; rewrite <-H, Ropp_involutive.
    + now left; apply Ropp_eq_reg.
  - now intros [-> | ->]; [| rewrite Rabs_Ropp].
Qed.

Lemma Rabs_minus_sym : forall x y:R, Rabs (x - y) = Rabs (y - x).
Proof. now intros x y; rewrite <-Ropp_minus_distr; apply Rabs_Ropp. Qed.

(* NEW *)
Lemma Rabs_minus_lt :
  forall x y eps, Rabs (x - y) < eps <-> y - eps < x < y + eps.
Proof.
  intros x y eps; rewrite Rabs_lt_iff; split; intros [H H']; split.
  - now apply Rlt_minus_chsd_lr.
  - now apply Rlt_minus_chsd_rl.
  - now apply Rlt_minus_chsd_lr.
  - now apply Rlt_minus_chsd_rl.
Qed.

(* NEW *)
Lemma Rabs_minus_le :
  forall x y eps, Rabs (x - y) <= eps <-> y - eps <= x <= y + eps.
Proof.
  intros x y eps; rewrite Rabs_le_iff; split; intros [H H']; split.
  - now apply Rle_minus_chsd_lr.
  - now apply Rle_minus_chsd_rl.
  - now apply Rle_minus_chsd_lr.
  - now apply Rle_minus_chsd_rl.
Qed.

(*************************************************)
(** **   Rabs and Rsqr are close friends         *)
(*************************************************)

(* TODO: with this name, it should be the reversed equality *)
Lemma Rsqr_abs : forall x, x² = (Rabs x)².
Proof.
  intros x; destruct (Rabs_id_or_opp x) as [-> | ->]; [reflexivity |].
  now rewrite Rsqr_neg.
Qed.

Lemma Rsqr_eq_abs : forall x y, x² = y² <-> Rabs x = Rabs y.
Proof.
  intros x y; rewrite (Rsqr_abs x), (Rsqr_abs y); split.
  - now intros H%Rsqr_inj; [| apply Rabs_pos | apply Rabs_pos].
  - now intros H; f_equal.
Qed.

(* TODO: bad name, deprecate *)
Lemma Rsqr_eq_abs_0 : forall x y, x² = y² -> Rabs x = Rabs y.
Proof. now apply Rsqr_eq_abs. Qed.

(* TODO: bad name, deprecate *)
Lemma Rsqr_eq_asb_1 : forall x y, Rabs x = Rabs y -> x² = y².
Proof. now apply Rsqr_eq_abs. Qed.

(* TODO: equivalence? *)
Lemma Rsqr_eq : forall x y, x² = y² -> x = y \/ x = - y.
Proof. now intros x y H%Rsqr_eq_abs; apply Rabs_eq_abs. Qed.

(* NEW *)
Lemma Rsqr_le_abs : forall x y, x² <= y² <-> Rabs x <= Rabs y.
Proof.
  intros x y; rewrite (Rsqr_abs x), (Rsqr_abs y); symmetry.
  now apply Rsqr_le_nneg; apply Rabs_pos.
Qed.

(* TODO: bad name *)
Lemma Rsqr_le_abs_0 : forall x y, x² <= y² -> Rabs x <= Rabs y.
Proof. now apply Rsqr_le_abs. Qed.

(* TODO: bad name *)
Lemma Rsqr_le_abs_1 : forall x y:R, Rabs x <= Rabs y -> x² <= y².
Proof. now apply Rsqr_le_abs. Qed.

(* NEW *)
Lemma Rsqr_lt_abs : forall x y:R, x² < y² <-> Rabs x < Rabs y.
Proof.
  intros x y; rewrite (Rsqr_abs x), (Rsqr_abs y); symmetry.
  now apply Rsqr_lt_nneg; apply Rabs_pos.
Qed.

(* TODO: bad name *)
Lemma Rsqr_lt_abs_0 : forall x y:R, x² < y² -> Rabs x < Rabs y.
Proof. now apply Rsqr_lt_abs. Qed.

(* TODO: bad name *)
Lemma Rsqr_lt_abs_1 : forall x y:R, Rabs x < Rabs y -> x² < y².
Proof. now apply Rsqr_lt_abs. Qed.

(* TODO: think about name *)
(* NEW: this contains a lot of other lemmas *)
Lemma Rsqr_le_bounds : forall x y, x² <= y² <-> - Rabs y <= x <= Rabs y.
Proof.
  intros x y; split.
  - now intros H%Rsqr_le_abs%Rabs_le_iff.
  - now intros H%Rabs_le_iff%Rsqr_le_abs.
Qed.

(* TODO: think about name *)
(* NEW: this contains a lot of other lemmas *)
Lemma Rsqr_lt_bounds : forall x y, x² < y² <-> - Rabs y < x < Rabs y.
Proof.
  intros x y; split.
  - now intros H%Rsqr_lt_abs%Rabs_lt_iff.
  - now intros H%Rabs_lt_iff%Rsqr_lt_abs.
Qed.

(* TODO: is it used? *)
Lemma Rsqr_neg_pos_le_0 :
  forall x y:R, x² <= y² -> 0 <= y -> - y <= x.
Proof. now intros x y H%Rsqr_le_bounds Hy%Rle_ge; rewrite Rabs_right in H. Qed.

(* TODO: decide about adding or keeping private. *)
Lemma Private_Rnneg_cond : forall x, - x <= x -> x >= 0.
Proof.
  intros x Hx%Rle_not_lt; apply Rnot_lt_ge; intros H; apply Hx.
  now apply (Rlt_trans _ 0); [| apply Ropp_neg].
Qed.

(* TODO: terrible name, deprecate *)
Lemma neg_pos_Rsqr_le : forall x y:R, - y <= x -> x <= y -> x² <= y².
Proof.
  intros x y H H'; apply Rsqr_le_bounds; rewrite Rabs_right; [easy |].
  now apply Private_Rnneg_cond; apply (Rle_trans _ x).
Qed.

(* TODO: deprecate *)
Lemma Rsqr_neg_pos_le_1 :
  forall x y:R, - y <= x -> x <= y -> 0 <= y -> x² <= y².
Proof. now intros x y H H0 _; apply neg_pos_Rsqr_le. Qed.

(* TODO: terrible name, deprecate *)
Lemma neg_pos_Rsqr_lt : forall x y : R, - y < x -> x < y -> x² < y².
Proof.
  intros x y H H'; apply Rsqr_lt_bounds; rewrite Rabs_right; [easy |].
  now apply Private_Rnneg_cond, Rlt_le, (Rlt_trans _ x).
Qed.

(* TODO: variable names, keep 0 <= in concl? *)
Lemma Rsqr_bounds_le : forall a b:R, -a <= b <= a -> 0 <= b² <= a².
Proof.
  intros a b [I J]; split.
  - now apply Rle_0_sqr.
  - now apply neg_pos_Rsqr_le.
Qed.

(* TODO: variable names, keep 0 <= in concl? *)
Lemma Rsqr_bounds_lt : forall a b:R, -a < b < a -> 0 <= b² < a².
Proof.
  intros a b [I J]; split.
  - now apply Rle_0_sqr.
  - now apply neg_pos_Rsqr_lt.
Qed.

(* TODO: french name (in english: right triangle) *)
Lemma triangle_rectangle :
  forall x y z:R,
    0 <= z -> x² + y² <= z² -> - z <= x <= z /\ - z <= y <= z.
Proof.
  intros x y z Hz%Rle_ge H; split; apply Rabs_le_iff;
    rewrite <-(Rabs_right z) by easy; apply Rsqr_le_abs;
    apply (Rle_trans _ (x² + y²)); try easy; [| rewrite Rplus_comm];
    now apply Rge_le, Rplus_nneg_ge, Rle_ge, Rle_0_sqr.
Qed.

(* TODO: french name (in english: right triangle), possible deprecation. *)
Lemma triangle_rectangle_lt :
  forall x y z:R,
    x² + y² < z² -> Rabs x < Rabs z /\ Rabs y < Rabs z.
Proof.
  intros x y z H; split; apply Rsqr_lt_abs, Rle_lt_trans with (2 := H);
    [| rewrite Rplus_comm]; now apply Rge_le, Rplus_nneg_ge, Rle_ge, Rle_0_sqr.
Qed.

(* TODO: french name (in english: right triangle), possible deprecation. *)
Lemma triangle_rectangle_le :
  forall x y z:R,
    x² + y² <= z² -> Rabs x <= Rabs z /\ Rabs y <= Rabs z.
Proof.
  intros x y z H; split; apply Rsqr_le_abs, Rle_trans with (2 := H);
    [| rewrite Rplus_comm]; now apply Rge_le, Rplus_nneg_ge, Rle_ge, Rle_0_sqr.
Qed.

(* NEW *)
Lemma Rabs_sqr : forall x, Rabs (x²) = (Rabs x)².
Proof.
  intros x; rewrite (Rabs_right (x²)) by now (apply Rle_ge, Rle_0_sqr).
  destruct (Rabs_id_or_opp x) as [-> | ->]; [reflexivity |].
  now unfold Rsqr; rewrite Rmult_opp_opp.
Qed.

Lemma Rabs_mult : forall x y:R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  intros x y; apply Rsqr_inj.
    now apply Rabs_nneg.
    now apply Rmult_le_pos; apply Rabs_nneg.
  rewrite <-(Rabs_sqr (x * y)), 2Rsqr_mult, <-2Rabs_sqr, 3Rabs_right.
  - reflexivity.
  - apply Rle_ge, Rle_0_sqr.
  - apply Rle_ge, Rle_0_sqr.
  - apply Rle_ge, Rmult_le_pos; apply Rle_0_sqr.
Qed.

Lemma Rabs_inv : forall r, Rabs (/ r) = / Rabs r.
Proof.
  intros r; apply Rsqr_inj; [now apply Rabs_nneg | |].
    now apply Rinv_nneg, Rabs_nneg.
  now rewrite <-Rsqr_abs, 2Rsqr_inv', <-Rsqr_abs.
Qed.

Lemma Rabs_Rinv_depr : forall r, r <> 0 -> Rabs (/ r) = / Rabs r.
Proof. now intros r _; apply Rabs_inv. Qed.

#[deprecated(since="8.16",note="Use Rabs_inv.")]
Notation Rabs_Rinv := Rabs_Rinv_depr.

(* NEW *)
Lemma Rabs_div : forall x y:R, Rabs (x / y) = Rabs x / Rabs y.
Proof. now intros x y; rewrite 2Rdiv_def, Rabs_mult, Rabs_inv. Qed.

(* CHANGED name, variable names *)
Lemma Rabs_triangle : forall r1 r2, Rabs (r1 + r2) <= Rabs r1 + Rabs r2.
Proof.
  intros r1 r2; apply Rsqr_incr_0_var; cycle 1.
    now apply Rplus_le_le_0_compat; apply Rabs_pos.
  rewrite Rsqr_plus, <-3Rabs_sqr.
  rewrite 3Rabs_right by (now apply Rle_ge, Rle_0_sqr).
  rewrite Rsqr_plus; apply Rplus_le_compat_l.
  rewrite 2Rmult_assoc; apply Rmult_le_compat_l.
    now left; apply Rlt_0_2.
  rewrite <-Rabs_mult.
  now apply Rle_abs.
Qed.

Notation Rabs_triang := (fun a b => (Rabs_triangle a b)).

(* TODO: shorter name *)
Lemma Rminus_abs_le_abs_minus :
  forall r1 r2, Rabs r1 - Rabs r2 <= Rabs (r1 - r2).
Proof.
  intros r1 r2; apply (Rplus_le_reg_r (Rabs r2)).
  rewrite Rminus_plus_r, <-(Rminus_plus_r r1 r2) at 1.
  now apply Rabs_triangle.
Qed.

Notation Rabs_triang_inv := (fun a b => (Rminus_abs_le_abs_minus a b)).

Lemma Rabs_1_lipchitz : forall r1 r2, Rabs (Rabs r1 - Rabs r2) <= Rabs (r1 - r2).
Proof.
  intros r1 r2; apply Rabs_le; split; [| now apply Rminus_abs_le_abs_minus].
  rewrite <-(Ropp_minus_distr (Rabs r2)); apply Ropp_le_contravar.
  now rewrite Rabs_minus_sym; apply Rminus_abs_le_abs_minus.
Qed.

(* ||a|-|b||<=|a-b| *)
Notation Rabs_triang_inv2 := (fun a b => (Rabs_1_lipchitz a b)).

(* TODO: rename, variable names *)
Lemma Rabs_def1 : forall x a:R, x < a -> - a < x -> Rabs x < a.
Proof.
  intros x a H H'; destruct (Rabs_id_or_opp x) as [-> | ->]; [assumption |].
  now rewrite <-(Ropp_involutive a); apply Ropp_lt_contravar.
Qed.

(* TODO: rename, variable names *)
Lemma Rabs_def2 : forall x a:R, Rabs x < a -> x < a /\ - a < x.
Proof.
  intros x a H; assert (I : a > 0)
    by (apply (Rle_lt_trans _ (Rabs x)); [apply Rabs_pos | assumption]).
  destruct (Rlt_or_le x 0) as [x_neg | x_nneg].
  - split.
    + now apply (Rlt_trans _ 0).
    + rewrite Rabs_left in H by assumption.
      (* TODO: this should be simpler *)
      now rewrite <-(Ropp_involutive x); apply Ropp_lt_contravar.
  - split.
    + now rewrite Rabs_right in H by (now apply Rle_ge).
    + now apply (Rlt_le_trans _ 0); [| assumption]; apply Ropp_pos.
Qed.

(* TODO: name, variable names, is it useful? *)
Lemma RmaxAbs :
  forall p q r, p <= q -> q <= r -> Rabs q <= Rmax (Rabs p) (Rabs r).
Proof.
  intros p q r Hpq Hqr; apply Rmax_Rle; destruct (Rlt_or_le q 0) as [I | I].
  - left; rewrite (Rabs_left q) by assumption.
    rewrite Rabs_left by (now apply (Rle_lt_trans _ q)).
    now apply Ropp_le_contravar.
  - right; rewrite (Rabs_right q) by (now apply Rle_ge).
    now rewrite Rabs_right by (now apply Rle_ge, (Rle_trans _ q)).
Qed.

Lemma Rabs_Zabs : forall z:Z, Rabs (IZR z) = IZR (Z.abs z).
Proof.
  intros z; destruct (Z.nonpos_pos_cases z) as [I | I].
  - rewrite Z.abs_neq by assumption; rewrite opp_IZR.
    now apply IZR_le in I; rewrite Rabs_left1.
  - rewrite Z.abs_eq by now apply Z.lt_le_incl.
    now apply IZR_lt, Rlt_le, Rle_ge in I; rewrite Rabs_right.
Qed.

(* TODO: deprecate ? *)
Lemma abs_IZR : forall z, IZR (Z.abs z) = Rabs (IZR z).
Proof. now intros z; rewrite Rabs_Zabs. Qed.

(* TODO: rename? euclidEan maybe Reuclidean ? *)
(** Here, we have the euclidian division *)
(** This lemma is used in the proof of sin_eq_0 : (sin x)=0<->x=kPI *)
Lemma euclidian_division :
  forall x y:R, y <> 0 ->
    exists k : Z, (exists r : R, x = IZR k * y + r /\ 0 <= r < Rabs y).
Proof.
  intros x.
  assert (forall y, y > 0 -> exists k r, x = IZR k * y + r /\ 0 <= r < y) as suf.
  {
    intros y y_pos; assert (y <> 0) as y_n0 by now apply Rgt_not_eq.
    exists (Int_part (x / y)); exists (x - IZR (Int_part (x / y)) * y); split.
      now rewrite Rplus_minus_assoc, Rplus_minus_l.
    destruct (Ip_bounds (x / y)) as [J J']; split.
    - now apply Rle_minus_le, Rle_mult_chsd_rr.
    - apply Rlt_minus_chsd_rr, Rlt_minus_chsd_rl, (Rdiv_lt_reg_r y); [easy |].
      now rewrite Rdiv_minus_distr, Rmult_div_l, Rdiv_diag.
  }
  intros y Hy.
  destruct (Rabs_leP y) as [[J | E] | [J | E]];
    [| now exfalso; apply Hy | now apply suf | now exfalso; apply Hy].
  destruct (suf (- y)) as [k [r [E I]]]; [now apply Ropp_neg |].
  exists (- k)%Z; exists r; split; [| exact I].
  now rewrite opp_IZR, <-Ropp_mult_distr_l, Ropp_mult_distr_r.
Qed.

(*******************************)
(** * Lemmas about factorial   *)
(*******************************)

(* TODO: deprecate? *)
Lemma INR_fact_neq_0 : forall n, INR (fact n) <> 0.
Proof. now intros n; apply not_0_INR, fact_neq_0. Qed.

(* TODO: deprecate? *)
Lemma fact_simpl : forall n, fact (S n) = (S n * fact n)%nat.
Proof. reflexivity. Qed.

(* TODO: deprecate? *)
Lemma simpl_fact :
  forall n, / INR (fact (S n)) * / / INR (fact n) = / INR (S n).
Proof.
  intro n; rewrite Rinv_inv, fact_simpl, mult_INR, Rinv_mult.
  now rewrite Rmult_assoc, Rinv_l, Rmult_1_r
    by (now apply not_0_INR, fact_neq_0).
Qed.

(* NEW TODO: add to Arith.factorial: *)
Lemma fact_succ : forall n, fact (S n) = (S n * fact n)%nat.
Proof. reflexivity. Qed.

(* NEW TODO: add to Arith.factorial: *)
Lemma fact_0 : fact 0 = 1%nat.
Proof. reflexivity. Qed.

(*******************************)
(** *       Power              *)
(*******************************)
(*********)

Infix "^" := pow : R_scope.

(* NEW: O -> 0_r *)
Lemma pow_0_r : forall x, x ^ 0 = 1.
Proof. reflexivity. Qed.

Notation pow_O := pow_0_r.

Lemma pow_succ : forall x n, x ^ (S n) = x * x ^ n.
Proof. now intros x n; simpl. Qed.

(* TODO: This should be pow_1_r *)
Lemma pow_1 : forall x:R, x ^ 1 = x.
Proof. now intros x; rewrite pow_succ, pow_0_r, Rmult_1_r. Qed.

Lemma pow_add : forall x n m, x ^ (n + m) = x ^ n * x ^ m.
Proof.
  intros x n; induction m as [| m IHm].
  - now rewrite Nat.add_0_r, pow_0_r, Rmult_1_r.
  - now rewrite Nat.add_succ_r, 2pow_succ, IHm, <-!Rmult_assoc, (Rmult_comm x _).
Qed.

Lemma Rpow_mult_distr : forall x y n, (x * y) ^ n = x ^ n * y ^ n.
Proof.
  intros x y; induction n as [| n IHn].
  - now rewrite !pow_0_r, Rmult_1_r.
  - rewrite !pow_succ, IHn, <-!Rmult_assoc; f_equal.
    now rewrite !Rmult_assoc; f_equal; rewrite Rmult_comm.
Qed.

Lemma pow_nonzero : forall (x:R) (n:nat), x <> 0 -> x ^ n <> 0.
Proof.
  intros x; induction n as [| n IHn]; intros H.
  - now rewrite pow_0_r; apply R1_neq_R0.
  - now rewrite pow_succ; apply Rmult_neq_0_neq_0 with (2 := (IHn H)).
Qed.

#[global]
Hint Resolve pow_0_r pow_1 pow_add pow_nonzero: real.

(* TODO: name, replace by theorem with division? *)
Lemma pow_RN_plus :
  forall x n m, x <> 0 -> x ^ n = x ^ (n + m) * / x ^ m.
Proof.
  intros x n m H.
  apply (Rmult_eq_reg_r (x ^ m)); [| now apply pow_nonzero].
  now rewrite Rmult_inv_m_id_l, pow_add by now apply pow_nonzero.
Qed.

Lemma pow_lt : forall (x:R) (n:nat), 0 < x -> 0 < x ^ n.
Proof.
  intros x; induction n as [| n IHn]; intros H.
  - now rewrite pow_0_r; apply Rlt_0_1.
  - now rewrite pow_succ; apply Rmult_pos_pos with (2:= (IHn H)).
Qed.
#[global]
Hint Resolve pow_lt: real.

Lemma Rlt_pow_R1 : forall (x:R) (n:nat), 1 < x -> (0 < n)%nat -> 1 < x ^ n.
Proof.
  intros x n Hx; induction n as [| n IHn]; intros Hn.
  - now exfalso; apply (Rlt_irrefl 0).
  - rewrite pow_succ; destruct n as [| n].
    + now rewrite pow_0_r, Rmult_1_r.
    + now rewrite <-(Rmult_1_r 1); apply Rmult_le_0_lt_compat;
        try apply Rle_0_1; [| apply IHn, Nat.lt_0_succ].
Qed.
#[global]
Hint Resolve Rlt_pow_R1: real.

Lemma Rlt_pow : forall (x:R) (n m:nat), 1 < x -> (n < m)%nat -> x ^ n < x ^ m.
Proof.
  intros x n m H' H'0; replace m with (m - n + n)%nat
    by (now apply Nat.sub_add, Nat.lt_le_incl).
  rewrite pow_add, <-(Rmult_1_l (x ^ n)) at 1.
  apply Rmult_lt_compat_r.
  - apply pow_lt, Rlt_trans with (2 := H'); apply Rlt_0_1.
  - now apply Rlt_pow_R1; [| apply Nat.neq_0_lt_0, Nat.sub_gt].
Qed.
#[global]
Hint Resolve Rlt_pow: real.

(* TODO: rename *)
Lemma tech_pow_Rmult : forall x n, x * x ^ n = x ^ S n.
Proof. now intros x; induction n as [| n IH]; simpl. Qed.

(* TODO: rename *)
Lemma tech_pow_Rplus :
  forall x a n, x ^ a + INR n * x ^ a = INR (S n) * x ^ a.
Proof.
  now intros x a n; rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l, Rplus_comm.
Qed.

(* TODO: rename *)
Lemma poly : forall n x, 0 < x -> 1 + INR n * x <= (1 + x) ^ n.
Proof.
  intros n x Hx; induction n as [|n IH].
  - now rewrite INR_0, Rmult_0_l, Rplus_0_r, pow_0_r; apply Rle_refl.
  - rewrite S_INR, Rmult_plus_distr_r, <-Rplus_assoc, Rmult_1_l.
    rewrite pow_succ, Rmult_plus_distr_r, Rmult_1_l; apply Rplus_le_compat;
      [exact IH |].
    rewrite <-(Rmult_1_r x) at 1; apply Rmult_le_compat_l; [now left |].
    destruct n as [| n]; [rewrite pow_0_r; apply Rle_refl |].
    now left; apply Rlt_pow_R1; [apply Rplus_pos_gt | apply Nat.lt_0_succ].
Qed.

(* TODO: rename *)
Lemma Power_monotonic :
  forall x m n, Rabs x > 1 -> (m <= n)%nat -> Rabs (x ^ m) <= Rabs (x ^ n).
Proof.
  intros x m n H; induction n as [|n IH]; intros Hm.
  - now apply Nat.le_0_r in Hm as ->; apply Rle_refl.
  - apply Nat.le_succ_r in Hm as [I | ->]; [| now apply Rle_refl].
    now rewrite pow_succ, Rabs_mult, <-Rmult_1_l at 1; apply Rmult_le_compat;
      [apply Rle_0_1 | apply Rabs_pos | left | apply IH].
Qed.

(* TODO: rename? *)
Lemma RPow_abs : forall x n, Rabs x ^ n = Rabs (x ^ n).
Proof.
  intros x; induction n as [| n IH].
  - now rewrite 2pow_0_r, Rabs_1.
  - now rewrite 2pow_succ, Rabs_mult, IH.
Qed.

(* NEW *)
(* TODO: replace >= with > ? *)
Lemma pow_gt_1_infinity :
  forall x, x > 1 -> forall b, exists N, forall n, (n >= N)%nat -> x ^ n >= b.
Proof.
  intros x Hx b; destruct (Rle_or_gt b 0) as [I | I].
  - exists 0%nat; intros n _; apply Rle_ge, Rle_trans with (1 := I).
    now left; apply pow_lt, Rlt_trans with (1 := Rlt_0_1).
  - remember (x - 1) as y eqn:Ey.
    apply eq_sym, Req_minus_chsd_rl in Ey; subst x.
    apply Rgt_plus_chsd_lr in Hx; rewrite Rminus_diag in Hx.
    destruct (INR_archimed y (b - 1) Hx) as [N IN]; exists N.
    intros n Hn; apply (Rge_trans _ (1 + (INR n) * y)).
      now apply Rle_ge, poly.
    apply Rge_plus_chsd_lr, Rgt_ge, Rlt_le_trans with (1 := IN).
    now apply Rmult_le_compat_r; [left | apply le_INR].
Qed.

(* TODO: name? replace >= with >? *)
Lemma Pow_x_infinity : forall x, Rabs x > 1 ->
  forall b, exists N, (forall n, (n >= N)%nat -> Rabs (x ^ n) >= b).
Proof.
  intros x Hx b.
  destruct (pow_gt_1_infinity (Rabs x) Hx b) as [N IN]; exists N.
  now intros Hn; rewrite <-RPow_abs; apply IN.
Qed.

Lemma pow_ne_zero : forall n, n <> 0%nat -> 0 ^ n = 0.
Proof.
  induction n as [| n IH].
  - intros H; now exfalso.
  - now intros _; rewrite pow_succ, Rmult_0_l.
Qed.

Lemma pow_inv x n : (/ x) ^ n = / (x ^ n).
Proof.
  induction n as [|n IH].
  - now rewrite 2pow_0_r, Rinv_1.
  - now rewrite 2pow_succ, Rinv_mult, IH.
Qed.

Lemma Rinv_pow_depr : forall (x:R) (n:nat), x <> 0 -> / x ^ n = (/ x) ^ n.
Proof. now intros x n _; symmetry; apply pow_inv. Qed.
#[deprecated(since="8.16",note="Use pow_inv.")]
Notation Rinv_pow := Rinv_pow_depr.

(* NEW, name? *)
Lemma Rpow_div_distr : forall x y n, (x / y) ^ n = x ^ n / y ^ n.
Proof. now intros x y n; rewrite 2Rdiv_def, Rpow_mult_distr, pow_inv. Qed.

Lemma pow_lt_1_zero :
  forall x:R, Rabs x < 1 -> forall y:R, 0 < y ->
    exists N : nat, (forall n:nat, (n >= N)%nat -> Rabs (x ^ n) < y).
Proof.
  intros x Hx y Hy; destruct (Req_dec x 0) as [-> | Hxn0].
  - exists 1%nat; intros n Hn; rewrite pow_ne_zero, Rabs_0; [exact Hy |].
    now apply not_eq_sym, Nat.lt_neq.
  - (* TODO: this is still too long *)
    apply Rinv_0_lt_contravar in Hx; [| now apply Rabs_pos_lt].
    rewrite Rinv_1, <-Rabs_inv in Hx.
    destruct (Pow_x_infinity (/ x) Hx ((/ y) + 1)) as [N IN]; exists N.
    intros n Hn; rewrite <-Rinv_inv, <-(Rinv_inv (Rabs _)).
    apply Rinv_0_lt_contravar; [now apply Rinv_0_lt_compat |].
    apply (Rlt_le_trans _ (/ y + 1)); [now apply Rlt_plus_1 |].
    rewrite <-Rabs_inv, <-pow_inv.
    now apply Rge_le, IN.
Qed.

(* NEW *)
Lemma pow_lt_1_compat :
  forall x n, Rabs x < 1 -> (n <> 0)%nat -> Rabs (x ^ n) < 1.
Proof.
  intros x; induction n as [|n IH].
  - now intros _ Hn; exfalso.
  - intros Hx _; rewrite pow_succ, Rabs_mult.
    destruct n as [| n]; [now rewrite pow_0_r, Rabs_1, Rmult_1_r |].
    now rewrite <-(Rmult_1_r 1); apply Rmult_le_0_lt_compat;
      [apply Rabs_pos | apply Rabs_pos | | apply IH].
Qed.

(* NEW *)
Lemma pow_gt_1_compat :
  forall x n, Rabs x > 1 -> (n <> 0)%nat -> Rabs (x ^ n) > 1.
Proof.
  intros x; induction n as [|n IH].
  - now intros _ Hn; exfalso.
  - intros Hx _; rewrite pow_succ, Rabs_mult.
    destruct n as [| n]; [now rewrite pow_0_r, Rabs_1, Rmult_1_r |].
    now rewrite <-(Rmult_1_r 1); apply Rmult_le_0_lt_compat;
      [apply Rle_0_1 | apply Rle_0_1 | | apply IH].
Qed.

(* TODO: name, variable names *)
Lemma pow_R1 : forall (r:R) (n:nat), r ^ n = 1 -> Rabs r = 1 \/ n = 0%nat.
Proof.
  intros r [| n]; [now right |]; intros H.
  destruct (Rtotal_order (Rabs r) 1) as [I | [-> | I]]; [| now left |]; exfalso.
  - apply (Rlt_irrefl (Rabs (r ^ (S n)))); rewrite H at 2; rewrite Rabs_1.
    now apply pow_lt_1_compat.
  - apply (Rlt_irrefl (Rabs (r ^ (S n)))); rewrite H at 1; rewrite Rabs_1.
    now apply pow_gt_1_compat.
Qed.

Lemma Rsqr_pow2 : forall x, x² = x ^ 2.
Proof. now intros x; rewrite Rsqr_def, 2pow_succ, pow_0_r, Rmult_1_r. Qed.

(* TODO: name? *)
Lemma pow_Rsqr : forall (x:R) (n:nat), x ^ (2 * n) = Rsqr x ^ n.
Proof.
  intros x n; induction n as [| n IH].
  - now rewrite Nat.mul_0_r, 2pow_0_r.
  - rewrite Nat.mul_succ_r, pow_add, IH, Rsqr_pow2, (pow_succ (x ^ 2)).
    now rewrite Rmult_comm.
Qed.

(* TODO: variable names, name! *)
Lemma pow_le : forall (a:R) (n:nat), 0 <= a -> 0 <= a ^ n.
Proof.
  intros a n Ha; induction n as [| n IH].
  - now rewrite pow_0_r; apply Rle_0_1.
  - now rewrite pow_succ; apply Rmult_le_pos.
Qed.

(* NEW *)
Lemma pow_1_l : forall n, 1 ^ n = 1.
Proof.
  induction n as [| n IH].
  - now rewrite pow_0_r.
  - now rewrite pow_succ, IH, Rmult_1_l.
Qed.

Lemma pow_1_even : forall n:nat, (-1) ^ (2 * n) = 1.
Proof.
  (* TODO: IZR_NEG is ugly *)
  now intros n; rewrite pow_Rsqr, IZR_NEG, <-Rsqr_neg, Rsqr_1, pow_1_l.
Qed.

Lemma pow_1_odd : forall n:nat, (-1) ^ S (2 * n) = -1.
Proof. now intros n; rewrite pow_succ, pow_1_even, Rmult_1_r. Qed.

(* TODO: Is it useful? *)
Lemma pow_1_abs : forall n:nat, Rabs ((-1) ^ n) = 1.
Proof.
  (* TODO: IZR_NEG is ugly *)
  now intros n; rewrite <-RPow_abs, IZR_NEG, Rabs_Ropp, Rabs_1, pow_1_l.
Qed.

(* TODO: pow_mul? *)
Lemma pow_mult : forall (x:R) (n1 n2:nat), x ^ (n1 * n2) = (x ^ n1) ^ n2.
Proof.
  intros x n1 n2; induction n1 as [| n1 IH].
  - now rewrite Nat.mul_0_l, pow_0_r, pow_1_l.
  - now rewrite Nat.mul_succ_l, pow_add, IH, pow_succ, Rpow_mult_distr,
      Rmult_comm.
Qed.

(* TODO: name? *)
Lemma pow_incr : forall (x y:R) (n:nat), 0 <= x <= y -> x ^ n <= y ^ n.
Proof.
  intros x y n [Hx Hy]; induction n as [| n IH].
  - now rewrite pow_0_r; apply Rle_refl.
  - now rewrite 2pow_succ; apply Rmult_le_compat; try assumption; apply pow_le.
Qed.

(* TODO: name? variable name? *)
Lemma pow_R1_Rle : forall (x:R) (k:nat), 1 <= x -> 1 <= x ^ k.
Proof.
  intros x k Hx; induction k as [| k IH].
  - now rewrite pow_0_r; apply Rle_refl.
  - now rewrite pow_succ, <-(Rmult_1_l 1); apply Rmult_le_compat;
      try assumption; apply Rle_0_1.
Qed.

Lemma Rdiv_pow :
  forall x m n, x <> 0 -> (m <= n)%nat -> (x ^ n) / (x ^ m) = x ^ (n - m).
Proof.
  intros x m n Hx H; assert (N : x ^ m <> 0) by now apply pow_nonzero.
  apply (Rmult_eq_reg_r (x ^ m)); [| assumption].
  rewrite <-Rmult_div_swap, <-Rmult_div_assoc, Rdiv_diag by assumption.
  now rewrite Rmult_1_r, <-pow_add, Nat.sub_add.
Qed.

Lemma Rle_pow :
  forall (x:R) (m n:nat), 1 <= x -> (m <= n)%nat -> x ^ m <= x ^ n.
Proof.
  intros x m n Hx H.
  assert (N : x <> 0) by now apply Rgt_not_eq, Rlt_le_trans with (1 := Rlt_0_1).
  apply (Rdiv_le_reg_r (x ^ m)).
    now apply pow_lt, Rlt_le_trans with (1 := Rlt_0_1).
  rewrite Rdiv_diag, Rdiv_pow; try easy; [| now apply pow_nonzero].
  now apply pow_R1_Rle.
Qed.

Notation pow1 := pow_1_l.

Lemma pow_Rabs : forall (x:R) (n:nat), x ^ n <= Rabs x ^ n.
Proof. now intros x n; rewrite RPow_abs; apply Rle_abs. Qed.

(* TODO: name? maybe it is too cryptic? *)
Lemma pow_maj_Rabs : forall (x y:R) (n:nat), Rabs y <= x -> y ^ n <= x ^ n.
Proof.
  intros x y n H.
  assert (I : 0 <= x) by now apply Rle_trans with (1 := Rabs_pos y).
  apply Rle_trans with (1 := (pow_Rabs y n)).
  now apply pow_incr; split; [apply Rabs_pos |].
Qed.

(*******************************)
(** *       PowerRZ            *)
(*******************************)
(*i Due to L.Thery i*)

Section PowerRZ.

Local Coercion Z_of_nat : nat >-> Z.

(* the following section should probably be somewhere else, but not sure where *)
Section Z_compl.

Local Open Scope Z_scope.

(* Provides a way to reason directly on Z in terms of nats instead of positive *)
Inductive Z_spec (x : Z) : Z -> Type :=
| ZintNull : x = 0 -> Z_spec x 0
| ZintPos (n : nat) : x = n -> Z_spec x n
| ZintNeg (n : nat) : x = - n -> Z_spec x (- n).

(* TODO: doc, provide how-to-use manual. *)
Lemma intP (x : Z) : Z_spec x x.
Proof.
  destruct x as [|p|p].
  - now apply ZintNull.
  - rewrite <-positive_nat_Z at 2.
    apply ZintPos.
    now rewrite positive_nat_Z.
  - rewrite <-Pos2Z.opp_pos.
    rewrite <-positive_nat_Z at 2.
    apply ZintNeg.
    now rewrite positive_nat_Z.
Qed.

End Z_compl.

Definition powerRZ (x:R) (n:Z) :=
  match n with
    | Z0 => 1
    | Zpos p => x ^ Pos.to_nat p
    | Zneg p => / x ^ Pos.to_nat p
  end.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

(* NEW name *)
Lemma powerRZ_0_r : forall x:R, x ^Z 0 = 1.
Proof. reflexivity. Qed.

(* NEW *)
Lemma powerRZ_Zpos : forall x p, x ^Z (Zpos p) = x ^ Pos.to_nat p.
Proof. reflexivity. Qed.

(* NEW *)
Lemma powerRZ_Zneg : forall x p, x ^Z (Zneg p) = / x ^ Pos.to_nat p.
Proof. reflexivity. Qed.

(* TODO: useful? belongs here? *)
Lemma Zpower_NR0 :
  forall (x:Z) (n:nat), (0 <= x)%Z -> (0 <= Zpower_nat x n)%Z.
Proof.
  induction n; unfold Zpower_nat; simpl; auto with zarith.
Qed.

(* TODO: notation? deprecate? *)
Lemma powerRZ_O : forall x:R, x ^Z 0 = 1.
Proof.
  reflexivity.
Qed.

(* TODO: notation? deprecate? *)
Lemma powerRZ_1 : forall x:R, x ^Z Z.succ 0 = x.
Proof.
  simpl; auto with real.
Qed.

(* NEW *)
Lemma powerRZ_1_r : forall x, x ^Z 1 = x.
Proof. now intros x; rewrite powerRZ_Zpos, Pos2Nat.inj_1, pow_1. Qed.

(* NEW *)
Lemma powerRZ_minus_1_r : forall x, x ^Z (- 1) = / x.
Proof. now intros x; rewrite powerRZ_Zneg, Pos2Nat.inj_1, pow_1. Qed.

(* TODO: name? *)
Lemma powerRZ_NOR : forall (x:R) (z:Z), x <> 0 -> x ^Z z <> 0.
Proof.
  destruct z; simpl; auto with real.
Qed.

Lemma powerRZ_pos_sub (x:R) (n m:positive) : x <> 0 ->
   x ^Z (Z.pos_sub n m) = x ^ Pos.to_nat n * / x ^ Pos.to_nat m.
Proof.
 intro Hx.
 rewrite Z.pos_sub_spec.
 case Pos.compare_spec; intro H; simpl.
 - subst; symmetry; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat n)) by auto with real.
   rewrite Nat.sub_add; [ | apply Nat.lt_le_incl; assumption ].
   rewrite Rinv_mult, Rinv_inv; auto with real.
 - rewrite Pos2Nat.inj_sub by trivial.
   rewrite Pos2Nat.inj_lt in H.
   rewrite (pow_RN_plus x _ (Pos.to_nat m)) by auto with real.
   rewrite Nat.sub_add; [ reflexivity | apply Nat.lt_le_incl; assumption ].
Qed.

Lemma powerRZ_add :
  forall (x:R) (n m:Z), x <> 0 -> x ^Z (n + m) = x ^Z n * x ^Z m.
Proof.
  intros x [|n|n] [|m|m]; simpl; intros; auto with real.
  - (* + + *)
    rewrite Pos2Nat.inj_add; auto with real.
  - (* + - *)
    now apply powerRZ_pos_sub.
  - (* - + *)
    rewrite Rmult_comm. now apply powerRZ_pos_sub.
  - (* - - *)
    rewrite Pos2Nat.inj_add; auto with real.
    rewrite pow_add; auto with real.
    apply Rinv_mult.
Qed.
#[local]
Hint Resolve powerRZ_O powerRZ_1 powerRZ_NOR powerRZ_add: real.

Lemma Zpower_nat_powerRZ :
  forall n m:nat, IZR (Zpower_nat (Z.of_nat n) m) = INR n ^Z Z.of_nat m.
Proof.
  intros n m; elim m; simpl; auto with real.
  intros m1 H'; rewrite SuccNat2Pos.id_succ; simpl.
  replace (Zpower_nat (Z.of_nat n) (S m1)) with
  (Z.of_nat n * Zpower_nat (Z.of_nat n) m1)%Z.
  - rewrite mult_IZR; auto with real.
    repeat rewrite <- INR_IZR_INZ; simpl.
    rewrite H'; simpl.
    case m1; simpl; auto with real.
    intros m2; rewrite SuccNat2Pos.id_succ; auto.
  - unfold Zpower_nat; auto.
Qed.

Lemma Zpower_pos_powerRZ :
  forall n m, IZR (Z.pow_pos n m) = IZR n ^Z Zpos m.
Proof.
  intros.
  rewrite Zpower_pos_nat; simpl.
  induction (Pos.to_nat m).
  - easy.
  - unfold Zpower_nat; simpl.
    rewrite mult_IZR.
    now rewrite <- IHn0.
Qed.

Lemma powerRZ_lt : forall (x:R) (z:Z), 0 < x -> 0 < x ^Z z.
Proof.
  intros x z; case z; simpl; auto with real.
Qed.
#[local]
Hint Resolve powerRZ_lt: real.

Lemma powerRZ_le : forall (x:R) (z:Z), 0 < x -> 0 <= x ^Z z.
Proof.
  intros x z H'; apply Rlt_le; auto with real.
Qed.
#[local]
Hint Resolve powerRZ_le: real.

Lemma Zpower_nat_powerRZ_absolu :
  forall n m:Z, (0 <= m)%Z -> IZR (Zpower_nat n (Z.abs_nat m)) = IZR n ^Z m.
Proof.
  intros n m; case m; simpl; auto with zarith.
  - intros p H'; elim (Pos.to_nat p); simpl; auto with zarith.
    intros n0 H'0; rewrite <- H'0; simpl; auto with zarith.
    rewrite <- mult_IZR; auto.
  - intros p H'; absurd (0 <= Zneg p)%Z; auto with zarith.
Qed.

Lemma powerRZ_R1 : forall n:Z, 1 ^Z n = 1.
Proof.
  intros n; case n; simpl; auto.
  - intros p; elim (Pos.to_nat p); simpl; auto; intros n0 H'; rewrite H';
      ring.
  - intros p; elim (Pos.to_nat p); simpl.
    + exact Rinv_1.
    + intros n1 H'; rewrite Rinv_mult; try rewrite Rinv_1; try rewrite H';
        auto with real.
Qed.

Local Open Scope Z_scope.

Lemma pow_powerRZ (r : R) (n : nat) :
  (r ^ n)%R = powerRZ r (Z_of_nat n).
Proof.
  induction n; [easy|simpl].
  now rewrite SuccNat2Pos.id_succ.
Qed.

Lemma powerRZ_ind (P : Z -> R -> R -> Prop) :
  (forall x, P 0 x 1%R) ->
  (forall x n, P (Z.of_nat n) x (x ^ n)%R) ->
  (forall x n, P ((-(Z.of_nat n))%Z) x (Rinv (x ^ n))) ->
  forall x (m : Z), P m x (powerRZ x m)%R.
Proof.
  intros ? ? ? x m.
  destruct (intP m) as [Hm|n Hm|n Hm].
  - easy.
  - now rewrite <- pow_powerRZ.
  - unfold powerRZ.
    destruct n as [|n]; [ easy |].
    rewrite Nat2Z.inj_succ, <- Zpos_P_of_succ_nat, Pos2Z.opp_pos.
    now rewrite <- Pos2Z.opp_pos, <- positive_nat_Z.
Qed.

Lemma powerRZ_inv' x alpha : powerRZ (/ x) alpha = Rinv (powerRZ x alpha).
Proof.
  destruct (intP alpha).
  - now simpl; rewrite Rinv_1.
  - now rewrite <-!pow_powerRZ, ?pow_inv, ?pow_powerRZ.
  - unfold powerRZ.
    destruct (- n).
    + now rewrite Rinv_1.
    + apply pow_inv.
    + now rewrite pow_inv.
Qed.

Lemma powerRZ_inv_depr x alpha : (x <> 0)%R -> powerRZ (/ x) alpha = Rinv (powerRZ x alpha).
Proof.
  intros _.
  apply powerRZ_inv'.
Qed.

Lemma powerRZ_neg' x : forall alpha, powerRZ x (- alpha) = Rinv (powerRZ x alpha).
Proof.
  intros [|n|n] ; simpl.
  - apply eq_sym, Rinv_1.
  - easy.
  - now rewrite Rinv_inv.
Qed.

Lemma powerRZ_neg_depr x : forall alpha, x <> R0 -> powerRZ x (- alpha) = powerRZ (/ x) alpha.
Proof.
  intros alpha _.
  rewrite powerRZ_neg'.
  apply eq_sym, powerRZ_inv'.
Qed.

Lemma powerRZ_mult m x y : (powerRZ (x*y) m = powerRZ x m * powerRZ y m)%R.
Proof.
  destruct (intP m) as [ | | n Hm ].
  - now simpl; rewrite Rmult_1_l.
  - now rewrite <- !pow_powerRZ, Rpow_mult_distr.
  - rewrite !powerRZ_neg', <- Rinv_mult.
    now rewrite <- !pow_powerRZ, Rpow_mult_distr.
Qed.

Lemma powerRZ_mult_distr_depr :
  forall m x y, ((0 <= m)%Z \/ (x * y <> 0)%R) ->
           (powerRZ (x*y) m = powerRZ x m * powerRZ y m)%R.
Proof.
  intros m x y _.
  apply powerRZ_mult.
Qed.

End PowerRZ.

#[deprecated(since="8.16",note="Use powerRZ_inv'.")]
Notation powerRZ_inv := powerRZ_inv_depr.

#[deprecated(since="8.16",note="Use powerRZ_neg' and powerRZ_inv'.")]
Notation powerRZ_neg := powerRZ_neg_depr.

#[deprecated(since="8.16",note="Use powerRZ_mult.")]
Notation powerRZ_mult_distr := powerRZ_mult_distr_depr.

Local Infix "^Z" := powerRZ (at level 30, right associativity) : R_scope.

(* TODO: I don't understand this title *)
(*******************************)
(* For easy interface          *)
(*******************************)
(* decimal_exp r z is defined as r 10^z *)

Definition decimal_exp (r:R) (z:Z) : R := (r * 10 ^Z z).

(*******************************)
(** * Sum of n first naturals  *)
(*******************************)

Fixpoint sum_nat_f_O (f:nat -> nat) (n:nat) : nat :=
  match n with
    | O => f 0%nat
    | S n' => (sum_nat_f_O f n' + f (S n'))%nat
  end.

Definition sum_nat_f (s n:nat) (f:nat -> nat) : nat :=
  sum_nat_f_O (fun x:nat => f (x + s)%nat) (n - s).

Definition sum_nat_O (n:nat) : nat := sum_nat_f_O (fun x:nat => x) n.

Definition sum_nat (s n:nat) : nat := sum_nat_f s n (fun x:nat => x).

(*******************************)
(** *          Sum             *)
(*******************************)

(* TODO: name, doc, notation? The choice of sum_f_R0 0 is not good. *)
Fixpoint sum_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f 0%nat
    | S i => sum_f_R0 f i + f (S i)
  end.

(* NEW, TODO name *)
Lemma sum_f_R0_0 : forall (f : nat -> R), sum_f_R0 f 0 = (f 0%nat).
Proof. reflexivity. Qed.

(* NEW, TODO name *)
Lemma sum_f_R0_succ :
  forall (f : nat -> R) N, sum_f_R0 f (S N) = sum_f_R0 f N + (f (S N)).
Proof. reflexivity. Qed.

(* TODO: name, doc *)
Definition sum_f (s n:nat) (f:nat -> R) : R :=
  sum_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

(* TODO: What does GP means? *)
Lemma GP_finite :
  forall (x:R) (n:nat),
    sum_f_R0 (fun n:nat => x ^ n) n * (x - 1) = x ^ (n + 1) - 1.
Proof.
  intros x; induction n as [| n IH].
  - now rewrite sum_f_R0_0, pow_0_r, Nat.add_0_l, pow_1, Rmult_1_l.
  - rewrite sum_f_R0_succ, Rmult_plus_distr_r, IH, Rmult_minus_distr_l.
    rewrite (Rmult_comm _ x), <-pow_succ, 2Nat.add_1_r, Rmult_1_r.
    now rewrite Rplus_comm, Rplus_minus_assoc, Rminus_plus_r.
Qed.

(* TODO: variable name? *)
Lemma sum_f_R0_triangle :
  forall (x:nat -> R) (n:nat),
    Rabs (sum_f_R0 x n) <= sum_f_R0 (fun i:nat => Rabs (x i)) n.
Proof.
  intros x; induction n as [| n IH].
  - now rewrite 2sum_f_R0_0; apply Rle_refl.
  - rewrite 2sum_f_R0_succ; apply Rle_trans with (1 := Rabs_triangle _ _).
    now apply Rplus_le_compat_r.
Qed.

(*******************************)
(** *     Distance  in R       *)
(*******************************)

Definition Rdist (x y:R) : R := Rabs (x - y).

(* NEW *)
Lemma Rdist_def : forall x y, Rdist x y = Rabs (x - y).
Proof. now unfold Rdist; intros x y. Qed.

Lemma Rdist_pos : forall x y:R, Rdist x y >= 0.
Proof. now intros x y; rewrite Rdist_def; apply Rle_ge, Rabs_pos. Qed.

Lemma Rdist_sym : forall x y:R, Rdist x y = Rdist y x.
Proof.  now intros x y; rewrite 2Rdist_def; apply Rabs_minus_sym. Qed.

Lemma Rdist_refl : forall x y:R, Rdist x y = 0 <-> x = y.
Proof.
  intros x y; rewrite Rdist_def; split; cycle 1.
    now intros ->; rewrite Rminus_diag, Rabs_0.
  destruct (Rabs_id_or_opp (x - y)) as [-> | ->].
  - now apply Rminus_diag_uniq.
  (* TODO: lemma - x = 0 -> x = 0 *)
  (* TODO: lemma x = y <-> - x = - y *)
  - now rewrite Ropp_minus_distr; intros H; symmetry; apply Rminus_diag_uniq.
Qed.

Lemma Rdist_eq : forall x:R, Rdist x x = 0.
Proof. now intros x; rewrite Rdist_def, Rminus_diag, Rabs_0. Qed.

Lemma Rdist_triangle : forall x y z:R, Rdist x y <= Rdist x z + Rdist z y.
Proof.
  intros x y z; rewrite 3Rdist_def, <-(Rminus_plus_r x z) at 1.
  now rewrite <-Rplus_minus_assoc; apply Rabs_triangle.
Qed.

Notation Rdist_tri := Rdist_triangle (only parsing).

(* TODO: variable names? *)
Lemma Rdist_plus :
  forall a b c d:R, Rdist (a + c) (b + d) <= Rdist a b + Rdist c d.
Proof.
  intros a b c d.
  rewrite 3Rdist_def, Rminus_plus_distr, Rplus_minus_swap.
  now rewrite <-Rplus_minus_assoc; apply Rabs_triangle.
Qed.

(* TODO: variable names? *)
Lemma Rdist_mult_l : forall a b c,
  Rdist (a * b) (a * c) = Rabs a * Rdist b c.
Proof.
  now intros a b c; rewrite 2Rdist_def, <-Rmult_minus_distr_l, Rabs_mult.
Qed.

(* NEW *)
Lemma Rdist_mult_r : forall a b c,
  Rdist (b * a) (c * a) = Rdist b c * Rabs a.
Proof.
  now intros a b c; rewrite 2Rdist_def, <-Rmult_minus_distr_r, Rabs_mult.
Qed.

(* NEW *)
Lemma Rdist_0_l : forall x, Rdist 0 x = Rabs x.
Proof. now intros x; rewrite Rdist_def, Rminus_0_l, Rabs_Ropp. Qed.

(* NEW *)
Lemma Rdist_0_r : forall x, Rdist x 0 = Rabs x.
Proof. now intros x; rewrite Rdist_def, Rminus_0_r. Qed.

(* NEW *)
Lemma Rdist_lt : forall x y eps, Rdist x y < eps <-> y - eps < x < y + eps.
Proof. now intros x y eps; rewrite Rdist_def; apply Rabs_minus_lt. Qed.

(* NEW *)
Lemma Rdist_le : forall x y eps, Rdist x y <= eps <-> y - eps <= x <= y + eps.
Proof. now intros x y eps; rewrite Rdist_def; apply Rabs_minus_le. Qed.

Notation R_dist := Rdist (only parsing).
Notation R_dist_pos := Rdist_pos (only parsing).
Notation R_dist_sym := Rdist_sym (only parsing).
Notation R_dist_refl := Rdist_refl (only parsing).
Notation R_dist_eq := Rdist_eq (only parsing).
Notation R_dist_tri := Rdist_tri (only parsing).
Notation R_dist_plus := Rdist_plus (only parsing).
Notation R_dist_mult_l := Rdist_mult_l (only parsing).

(*******************************)
(** *     Infinite Sum          *)
(*******************************)

Definition infinite_sum (s:nat -> R) (l:R) : Prop :=
  forall eps:R,
    eps > 0 ->
    exists N : nat,
      (forall n:nat, (n >= N)%nat -> Rdist (sum_f_R0 s n) l < eps).

(*******************************)
(** *     split tactics        *)
(*******************************)

Ltac split_case_Rabs :=
  match goal with
    |  |- context [(Rcase_abs ?X1)] =>
      destruct (Rcase_abs X1) as [?Hlt|?Hge]; try split_case_Rabs
  end.

Ltac split_Rabs :=
  match goal with
    | id:context [(Rabs _)] |- _ => generalize id; clear id; try split_Rabs
    |  |- context [(Rabs ?X1)] =>
      unfold Rabs; try split_case_Rabs; intros
  end.

Ltac split_Rmult :=
  match goal with
    |  |- ((?X1 * ?X2)%R <> 0%R) =>
      apply Rmult_integral_contrapositive; split; try split_Rmult
  end.
(** Compatibility with previous versions *)
Notation infinit_sum := infinite_sum (only parsing).
