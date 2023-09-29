(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*//   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(* *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Coq.Reals_prototype Require Import Rbase_prototype.
From Coq.Reals_prototype Require Import Rfunctions_prototype.

(* NOTE: Rlogic shows that :
- the limited principle of omniscience (sig_forall_dec)
   - the strong excluded middle for negations (sig_not_dec)
   can be derived from the 16 (+ 1) "axioms", so there is no reason not to
   use them, they will hold even if the construction of reals change *)
From Coq.Reals Require Import Rlogic.

(* QUESTION: now the big question is, can we use functional extensionality ? *)
Local Open Scope R_scope.
(* Preliminary results or definitions
   that should probably go somewhere else or be deprecated *)

(* TODO : move or deprecate *)
Lemma INR_fact_lt_0 : forall n:nat, 0 < INR (fact n).
Proof. now intros n; apply lt_0_INR, lt_O_fact. Qed.

(* TODO : move or deprecate *)
Lemma le_n_2n : forall n:nat, (n <= 2 * n)%nat.
Proof. now intros n; rewrite <-Nat.double_twice; apply Nat.le_add_r. Qed.

(* NEW *)
Lemma Private_sub_pred_l :
  forall n m, (m <= n -> Nat.pred n - m = Nat.pred (n - m))%nat.
Proof.
  intros [| n] m H; [now rewrite 2Nat.sub_0_l |].
  inversion H as [E | m' I].
  - now rewrite Nat.sub_diag, Nat.sub_succ_r, Nat.pred_succ, Nat.sub_diag,
      Nat.pred_0.
  - now rewrite Nat.sub_succ_l, 2?Nat.pred_succ.
Qed.

(* NEW *)
Lemma Private_twice_succ : forall n, (2 * S n)%nat = (S (S (2 * n))).
Proof.
  now intros n; rewrite <-Nat.double_twice, Nat.double_S, Nat.double_twice.
Qed.

(* NEW *)
Lemma Private_sub_sub_id_r : forall n m, (m <= n -> n - (n - m) = m)%nat.
Proof.
  intros n m I; induction I as [| n Hn IH].
  - now rewrite Nat.sub_diag, Nat.sub_0_r.
  - now rewrite (Nat.sub_succ_l m), Nat.sub_succ, IH.
Qed.

Lemma cond_eq :
  forall x y:R, (forall eps:R, 0 < eps -> Rabs (x - y) < eps) -> x = y.
Proof.
  intros x y H; apply Rminus_diag_uniq; generalize dependent (x - y).
  clear x y; intros r H.
  destruct (Req_dec r 0) as [-> | H'%Rabs_pos_lt]; [reflexivity | exfalso].
  now apply (Rlt_irrefl (Rabs r)), H, H'.
Qed.

(* TODO: strengthen, rename and move to RIneq *)
Lemma tech7 : forall r1 r2:R, r1 <> 0 -> r2 <> 0 -> r1 <> r2 -> / r1 <> / r2.
Proof. now intros r1 r2 _ _ H contra%Rinv_eq_reg. Qed.

(** ** Real sequences *)

(** A real sequence is simply a function from nat to R,
    the simplest example is INR *)

(* NEW *)
Lemma Un_eq_dec : forall (Un Vn : nat -> R),
  {n | Un n <> Vn n} + {forall n, Un n = Vn n}.
Proof. now intros Un Vn; apply sig_forall_dec; intros n; apply Req_dec_T. Qed.

(** *** Variations of sequences *)

Definition Un_growing (Un : nat -> R) := forall n:nat, Un n <= Un (S n).
Definition Un_decreasing (Un : nat -> R) := forall n:nat, Un (S n) <= Un n.

(* NEW *)
Lemma Un_growing_le_compat : forall Un,
  Un_growing Un -> (forall n m, (n <= m)%nat -> Un n <= Un m).
Proof.
  intros Un n m HU Hle; induction Hle as [| p Hm HUp].
  - now apply Rle_refl.
  - now apply Rle_trans with (1 := HUp).
Qed.

(* Compatibility *)
Notation tech9 := Un_growing_le_compat.

(* NEW *)
Lemma Un_decreasing_le_contravar : forall Un,
  Un_decreasing Un -> (forall n m, (n <= m)%nat -> Un m <= Un n).
Proof.
  intros Un n m HU Hle; induction Hle as [| p Hm HUp].
  - now apply Rle_refl.
  - now apply Rle_trans with (2 := HUp).
Qed.

(* Monotony is preserved after shifting the indices (one way only) *)
Lemma Un_growing_shift :
   forall k un, Un_growing un -> Un_growing (fun n => un (n + k)%nat).
Proof. now intros k un P n; apply P. Qed.

Definition opp_seq (Un:nat -> R) (n:nat) : R := - Un n.

Lemma decreasing_growing :
  forall Un:nat -> R, Un_decreasing Un -> Un_growing (opp_seq Un).
Proof. now intros Un Udec n; apply Ropp_le_contravar, Udec. Qed.

(* The following two lemmas are not very convenient, kept for compatibility. *)
Lemma growing_prop : forall Un n m,
  Un_growing Un -> (n >= m)%nat -> Un n >= Un m.
Proof. now intros Un n m HU H; apply Rle_ge, Un_growing_le_compat. Qed.

Lemma decreasing_prop : forall Un n m,
  Un_decreasing Un -> (m <= n)%nat -> Un n <= Un m.
Proof. now intros Un n m HU H; apply Un_decreasing_le_contravar. Qed.

(** *** Image and Boundedness of sequences *)

(* TODO: add comments on historical choices *)
(** EUn Un is the image of Un *)
Definition EUn (Un : nat -> R) r : Prop :=  exists i : nat, r = Un i.

Lemma EUn_noempty : forall Un, exists r, EUn Un r.
Proof. now intros Un; exists (Un 0%nat); exists 0%nat. Qed.

Lemma Un_in_EUn : forall Un n, EUn Un (Un n).
Proof. now intros Un n; exists n. Qed.

Lemma Un_bound_imp :
  forall Un x, (forall n, Un n <= x) -> is_upper_bound (EUn Un) x.
Proof. now intros Un x Hx y [n ->]. Qed.

(* NEW *)
Lemma Un_ub_charac :
  forall Un x, (is_upper_bound (EUn Un) x <-> (forall n:nat, Un n <= x)).
Proof.
  intros x; split; [| now apply Un_bound_imp]; intros Hx.
  now intros n; apply Hx; exists n.
Qed.

(* NEW *)
Lemma Un_ub_dec : forall (Un : nat -> R) x,
  {n | Un n > x} + {forall n, Un n <= x}.
Proof.
  intros Un x.
  destruct (sig_forall_dec (fun n => Un n <= x)) as [[n Hn]| Fa];
    [now intros n; apply Rle_dec | | now right].
  now left; exists n; apply Rnot_le_lt.
Qed.

(* TODO: what more can be decided? I think having an upper bound can be decided
   but I'm not sure yet *)

(* EXPERIMENT *)
(* If satisfactory, this will be moved to Rlogic *)
(* Basic lemmas about set-decidable propositions *)
Notation "'dec_S' X" := ({X} + {~ X}) (at level 50).

Lemma imp_dec (A B : Prop) :
  dec_S A -> dec_S B -> dec_S (A -> B).
Proof.
  intros [HA | HA] [HB | HB].
  - now left.
  - now right; intros H; apply HB, H, HA.
  - now left; intros _.
  - now left; intros H; exfalso; apply HA.
Qed.

Lemma or_dec (A B : Prop) :
  dec_S A -> dec_S B -> dec_S (A \/ B).
Proof.
  intros [HA | HA] [HB | HB].
  - now left; left.
  - now left; left.
  - now left; right.
  - now right; intros [H | H]; [apply HA | apply HB].
Qed.

Lemma and_dec (A B : Prop) :
  dec_S A -> dec_S B -> dec_S (A /\ B).
Proof.
  intros [HA | HA] [HB | HB].
  - now left.
  - now right; intros [HA' HB'].
  - now right; intros [HA' HB'].
  - now right; intros [HA' HB'].
Qed.

(* Note that sig_not_dec gives {~ A} + {~~ A} for _any_ A, not only for
   decidable A so not_dec is not useful in our case but let us state it for
   completeness. *)
Lemma not_dec (A : Prop) : dec_S A -> dec_S (~ A).
Proof. now intros [H | H]; [right; intros H' | left]. Qed.

(* set-decidability is preserved by equivalence *)
Lemma dec_iff_dec (A B : Prop) : dec_S A -> (B <-> A) -> dec_S B.
Proof. now intros [HA | HA] H; [left; apply H | right; intros H'%H]. Qed.

Lemma dec_dne (A : Prop) : dec_S A -> (~~ A <-> A).
Proof.
  intros H; split; intros H'.
  - now destruct H as [H | H]; [assumption | now exfalso; apply H', H].
  - now intros contra; exfalso; apply contra, H'.
Qed.

(* Consequences of sig_not_eq (also know as Weak Excluded Middle *)
(* sig_not_eq implies deMorgan *)
Lemma de_Morgan (A B : Prop) : ~ (A /\ B) -> ~ A \/ ~ B.
Proof.
  intros H.
  destruct (sig_not_dec A) as [HA | HA]; [| now left].
  destruct (sig_not_dec B) as [HB | HB]; [| now right].
  now left; intros H'; apply HB; intros HB'; apply H.
Qed.

(* sig_not_eq implies that Prop-decidable -> Set-decidable *)
Lemma prop_dec_set_dec (A : Prop) : A \/ ~ A -> {A} + {~ A}.
Proof.
  intros HA; destruct (sig_not_dec A) as [HA' | HA']; [| now right].
  now left; destruct HA as [HA | HA]; [| exfalso; apply HA'].
Qed.

(* Consequences of sig_forall_dec *)

Notation "'seq_dec_S' P" := (forall n, {P n} + {~ P n}) (at level 50).

Lemma sig_forall_dec_forall (P : nat -> Prop) :
  seq_dec_S P -> dec_S (forall n, P n).
Proof.
  intros [[n Hn] | fa]%sig_forall_dec.
  - now right; intros H; exfalso; apply Hn.
  - now left.
Qed.

Lemma sig_forall_dec_not_forall (P : nat -> Prop) :
  seq_dec_S P -> ~(forall n, P n) -> exists n, ~ P n.
Proof.
  intros H H'; destruct (sig_forall_dec P) as [[n Hn] | A];
    [easy | now exists n | now exfalso].
Qed.

(* negation of exists as forall does not need sig_forall_dec *)
Lemma not_ex_forall (P : nat -> Prop) : ~(exists n, P n) -> forall n, ~ P n.
Proof. now intros H n Hn; apply H; exists n. Qed.

Lemma sig_forall_dec_exists (P : nat -> Prop) :
  seq_dec_S P -> dec_S (exists n, P n).
Proof.
  intros HP.
  assert (forall n, {~ P n} + {~~ P n}) as HP' by now intros n; apply not_dec.
  apply sig_forall_dec in HP' as [[n Hn] | H]; [left | right].
  - now exists n; apply dec_dne.
  - now intros [n Hn]; apply (H n).
Qed.

Lemma sig_forall_dec_iter_fa_ex : forall P : nat -> nat -> Prop,
  (forall n m : nat, {P n m} + {~ P n m}) ->
  {forall n, exists m, P n m} + {~ forall n, exists m, P n m}.
Proof.
  intros P HP.
  apply sig_forall_dec_forall; intros n.
  now apply sig_forall_dec_exists.
Qed.

Lemma sig_forall_dec_iter_fa_ex' : forall P : nat -> nat -> Prop,
  (forall n m : nat, {P n m} + {~ P n m}) ->
  {n | forall m, ~P n m} + {forall n, exists m, P n m}.
Proof.
  intros P HP.
  destruct (sig_forall_dec (fun n => exists m, P n m)) as [[n Hn] | H].
  - now intros n; apply sig_forall_dec_exists.
  - now left; exists n; apply not_ex_forall.
  - now right.
Qed.

(* END OF EXPERIMENT *)

(* TODO: add better name *)
Lemma finite_greater :
  forall Un N, exists M : R, (forall n:nat, (n <= N)%nat -> Un n <= M).
Proof.
  intros Un N; induction N as [|N [M1 H1]].
  - now exists (Un 0%nat); intros n ->%Nat.le_0_r; apply Rle_refl.
  - exists (Rmax M1 (Un (S N))); intros n [Hn | ->]%Nat.le_succ_r.
    + now apply Rmax_Rle; left; apply H1.
    + now apply Rmax_r.
Qed.

(* TODO: these are a lot less practical to use than, say
         exists M, forall n, Un <= M (resp. m <= Un), state alternative
         definitions *)
Definition has_ub (Un:nat -> R) : Prop := bounded_from_above (EUn Un).
Definition has_lb (Un:nat -> R) : Prop := bounded_from_above (EUn (opp_seq Un)).

(* NEW *)
Lemma Un_lb_set_seq :
  forall Un m, (is_lower_bound (EUn Un) m <-> (forall n:nat, m <= Un n)).
Proof.
  intros Un m; split; intros H.
  - now intros n; apply H; exists n.
  - now intros y [n ->].
Qed.

(* NEW *)
Lemma Un_ub_set_seq :
  forall Un M, (is_upper_bound (EUn Un) M <-> (forall n:nat, Un n <= M)).
Proof.
  intros Un M; split; intros H.
  - now intros n; apply H; exists n.
  - now intros y [n ->].
Qed.

(* NEW *)
Lemma has_lb_lb : forall Un, has_lb Un <-> exists m, is_lower_bound (EUn Un) m.
Proof.
  intros Un; setoid_rewrite Un_lb_set_seq; split; intros [m Hm]; exists (- m).
  - now intros n; apply Ropp_le_cancel; rewrite Ropp_involutive; apply Hm;
      exists n.
  - now unfold opp_seq; intros x [i ->]; apply Ropp_le_contravar.
Qed.

(* NEW *)
Lemma has_lb_set_seq : forall Un, has_lb Un <-> exists m, forall n, m <= Un n.
Proof.
  now intros Un; split; setoid_rewrite has_lb_lb; setoid_rewrite Un_lb_set_seq.
Qed.

(* NEW *)
Lemma has_ub_set_seq : forall Un, has_ub Un <-> exists M, forall n, Un n <= M.
Proof.
  now intros Un; split; unfold has_ub, bounded_from_above; setoid_rewrite Un_ub_set_seq.
Qed.

(** *** Least upper bounds and greatest lower bounds of sequences *)
(* TODO: historical notes and how to move around bad initial choices *)

Lemma ub_to_lub :
  forall Un:nat -> R, has_ub Un -> { l:R | is_lub (EUn Un) l }.
Proof.
  intros Un H; apply completeness.
  - exact H.
  - now exists (Un 0%nat); exists 0%nat.
Qed.

Lemma lb_to_glb :
  forall Un:nat -> R, has_lb Un -> { l:R | is_lub (EUn (opp_seq Un)) l }.
Proof.
  intros Un H; apply completeness.
  - exact H.
  - now exists (- Un 0%nat); exists 0%nat.
Qed.

Definition lub (Un:nat -> R) (pr:has_ub Un) : R :=
  let (a,_) := ub_to_lub Un pr in a.

Definition glb (Un:nat -> R) (pr:has_lb Un) : R :=
  let (a,_) := lb_to_glb Un pr in - a.

(* NEW *)
Inductive lub_spec (Un : nat -> R) (pr : has_ub Un) : R -> Type :=
  lub_spec_constr (l : R) (is_ub : forall n, Un n <= l)
                  (is_lub : forall m, (forall n, Un n <= m) -> l <= m) :
                  lub_spec Un pr l.

(* NEW *)
Lemma Un_lubP : forall Un (pr : has_ub Un), lub_spec Un pr (lub Un pr).
Proof.
  intros Un pr; constructor.
  - unfold lub; destruct ub_to_lub as [l [is_lb _]]; intros n.
    now apply is_lb; exists n.
  - intros m H; unfold lub; destruct ub_to_lub as [l [_ is_lub]]; apply is_lub.
    now intros x [i ->].
Qed.

(* NEW *)
Inductive glb_spec (Un : nat -> R) (pr : has_lb Un) : R -> Type :=
  glb_spec_constr (l : R) (is_lb : forall n, l <= Un n)
                  (is_glb : forall m, (forall n, m <= Un n) -> m <= l) :
                  glb_spec Un pr l.

(* NEW *)
Lemma Un_glbP : forall Un (pr : has_lb Un), glb_spec Un pr (glb Un pr).
Proof.
  intros Un pr; constructor.
  - unfold glb; destruct lb_to_glb as [l [is_gb _]]; intros n.
    now apply Ropp_le_cancel; rewrite Ropp_involutive; apply is_gb; exists n.
  - intros m H; unfold glb; destruct lb_to_glb as [l [_ is_glb]].
    apply Ropp_le_cancel; rewrite Ropp_involutive; apply is_glb.
    now intros x [i ->]; apply Ropp_le_contravar.
Qed.

(* NEW *)
Lemma Un_lub_le : forall Un (pr : has_ub Un) m,
  (lub Un pr) <= m <-> (forall n, Un n <= m).
Proof.
  intros Un pr; destruct (Un_lubP Un pr) as [l is_ub is_lub]; split; intros H.
  - now intros n; apply Rle_trans with (2 := H).
  - now apply is_lub.
Qed.

(* NEW *)
Lemma Un_lub_ub : forall Un (pr : has_ub Un), forall n, Un n <= (lub Un pr).
Proof. now intros Un pr n; destruct (Un_lubP Un pr) as [l is_ub _]. Qed.

(* NEW *)
Lemma Un_glb_lb : forall Un (pr : has_lb Un), forall n, (glb Un pr) <= Un n.
Proof. now intros Un pr n; destruct (Un_glbP Un pr) as [l is_lb _]. Qed.

(* NEW *)
Lemma Un_glb_le : forall Un (pr : has_lb Un) m,
  m <= (glb Un pr) <-> (forall n, m <= Un n).
Proof.
  intros Un pr; destruct (Un_glbP Un pr) as [l is_lb is_glb]; split; intros H.
  - now intros n; apply Rle_trans with (1 := H).
  - now apply is_glb.
Qed.

(* NEW *)
Lemma Un_lub_charac :
  forall Un M, is_lub (EUn Un) M <->
    (forall n, Un n <= M) /\ forall eps, eps > 0 -> exists n, Un n > M - eps.
Proof.
  intros Un M; split; intros [BU LB]; split.
  - now intros n; apply (BU (Un n)); exists n.
  - intros eps Heps.
    destruct (Un_ub_dec Un (M - eps)) as [[l H] | H]; [exists l; exact H| ].
    exfalso; apply (Rlt_irrefl M); apply (Rle_lt_trans _ (M - eps)); cycle 1.
      now apply Rlt_minus_chsd_rr, Rplus_pos_gt.
    apply LB; intros x [n ->]; apply H.
  - intros x [n ->]; apply BU.
  - intros b Hb; apply Rnot_lt_le; intros Hb_contra.
    destruct (LB (M - b)) as [N HN]; [now apply Rgt_minus |].
    rewrite Rminus_minus_distr, Rminus_plus_l in HN.
    apply (Rgt_not_le (Un N) b); [now apply HN | now apply Hb; exists N].
Qed.

Lemma approx_maj :
  forall (Un:nat -> R) (pr:has_ub Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (lub Un pr - Un k) < eps.
Proof.
  intros Un pr eps Heps.
  unfold lub.
  destruct (ub_to_lub Un pr) as [M HM].
  apply Un_lub_charac in HM as [HM1 HM2].
  specialize (HM2 eps Heps) as [N HN]; exists N.
  apply Rabs_lt_iff; split.
  - apply Rlt_minus_chsd_lr, Rlt_minus_chsd_rl, Rle_lt_trans with (1 := (HM1 N)).
    now rewrite Rplus_comm; apply Rplus_pos_gt.
  - now apply Rlt_minus_chsd_rl, Rlt_minus_chsd_rr.
Qed.

Lemma approx_min :
  forall (Un:nat -> R) (pr:has_lb Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (glb Un pr - Un k) < eps.
Proof.
  intros Un pr; unfold glb; destruct lb_to_glb as (lb, Hlb).
  intros eps Heps.
  destruct (approx_maj _ pr eps Heps) as (n, Hn).
  exists n; rewrite Rminus_def, <-Ropp_plus_distr, Rabs_Ropp.
  replace lb with (lub (opp_seq Un) pr).
  - now rewrite <-(Ropp_involutive (Un n)).
  - unfold lub.
    destruct ub_to_lub as (ub, Hub).
    now apply Rle_antisym; [apply Hub, Hlb | apply Hlb, Hub].
Qed.

Lemma maj_ss :
  forall (Un:nat -> R) (k:nat),
    has_ub Un -> has_ub (fun i:nat => Un (k + i)%nat).
Proof. now intros Un k; rewrite !has_ub_set_seq; intros [M HM]; exists M. Qed.

Lemma min_ss :
  forall (Un:nat -> R) (k:nat),
    has_lb Un -> has_lb (fun i:nat => Un (k + i)%nat).
Proof. now intros Un k; rewrite !has_lb_set_seq; intros [M HM]; exists M. Qed.

(** **** Sequences of upper and lower bounds *)

Definition sequence_ub (Un:nat -> R) (pr:has_ub Un)
  (i:nat) : R := lub (fun k:nat => Un (i + k)%nat) (maj_ss Un i pr).

Definition sequence_lb (Un:nat -> R) (pr:has_lb Un)
  (i:nat) : R := glb (fun k:nat => Un (i + k)%nat) (min_ss Un i pr).

Lemma Wn_decreasing :
  forall (Un:nat -> R) (pr:has_ub Un), Un_decreasing (sequence_ub Un pr).
Proof.
  intros Un pr n; unfold sequence_ub; apply Un_lub_le.
  destruct (Un_lubP (fun k : nat => Un (n + k)%nat) (maj_ss Un n pr))
    as [l' is_ub' _].
  now intros m; rewrite Nat.add_succ_comm.
Qed.

Lemma Vn_growing :
  forall (Un:nat -> R) (pr:has_lb Un), Un_growing (sequence_lb Un pr).
Proof.
  intros Un pr n; unfold sequence_lb; apply Un_glb_le.
  destruct (Un_glbP (fun k : nat => Un (n + k)%nat) (min_ss Un n pr))
    as [l' is_gb' _].
  now intros m; rewrite Nat.add_succ_comm.
Qed.

Lemma Vn_Un_Wn_order :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un)
    (n:nat), sequence_lb Un pr2 n <= Un n <= sequence_ub Un pr1 n.
Proof.
  intros Un pr1 pr2 n; unfold sequence_lb, sequence_ub.
  destruct (Un_glbP _ (min_ss Un n pr2)) as [l Hl _].
  destruct (Un_lubP _ (maj_ss Un n pr1)) as [m Hm _].
  now rewrite <-(Nat.add_0_r n).
Qed.

Lemma min_maj :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_ub (sequence_lb Un pr2).
Proof.
  intros Un pr1 pr2.
  pose proof (Vn_Un_Wn_order Un pr1 pr2) as H.
  destruct pr1 as [m Hm]; exists m; intros x [n ->].
  apply Rle_trans with (1 := proj1 (H n)).
  now apply Hm; exists n.
Qed.

Lemma maj_min :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_lb (sequence_ub Un pr1).
Proof.
  intros Un pr1 pr2.
  pose proof (Vn_Un_Wn_order Un pr1 pr2) as H.
  destruct pr2 as [m Hm]; exists m; intros x [n ->].
  unfold opp_seq; apply Ropp_le_cancel; rewrite Ropp_involutive.
  apply Rle_trans with (2 := proj2 (H n)).
  apply Ropp_le_cancel; rewrite Ropp_involutive.
  now apply Hm; exists n.
Qed.

(** *** Convergence of sequences *)

Definition Un_cv (Un : nat -> R) (l : R) : Prop :=
  forall eps:R, eps > 0 ->
    exists N : nat, (forall n:nat, (n >= N)%nat -> Rdist (Un n) l < eps).

(* NEW *)
Lemma Un_cv_evtly_eq_compat :
  forall Un Vn l, (exists N, forall n, (n >= N)%nat -> Vn n = Un n)
    -> Un_cv Un l -> Un_cv Vn l.
Proof.
  intros Un Vn l [N HN] HU; intros eps Heps; destruct (HU eps Heps) as [N' HN'].
  exists (Nat.max N N'); intros n [Hn Hn']%Nat.max_lub_iff.
  now rewrite HN by exact Hn; apply HN'.
Qed.

(* NEW *)
Lemma Un_cv_eq_compat :
  forall Un Vn l, (forall n, Vn n = Un n) -> Un_cv Un l -> Un_cv Vn l.
Proof.
  now intros Un Vn l H Ucv%(Un_cv_evtly_eq_compat _ Vn); [| exists 0%nat].
Qed.

Lemma UL_sequence :
  forall (Un:nat -> R) (l1 l2:R), Un_cv Un l1 -> Un_cv Un l2 -> l1 = l2.
Proof.
  intros Un l1 l2 H1 H2; apply cond_eq; intros eps Heps.
  assert (fact : eps / 2 > 0) by now apply Rdiv_pos_pos; [| exact Rlt_0_2].
  specialize (H1 (eps / 2) fact) as [N1 HN1].
  specialize (H2 (eps / 2) fact) as [N2 HN2].
  rewrite <-Rdist_def, <-(Rplus_half_diag eps).
  apply Rle_lt_trans with (1 := Rdist_triangle _ _ (Un (Nat.max N1 N2))).
  now apply Rplus_lt_compat; [rewrite Rdist_sym; apply HN1 | apply HN2];
    [apply Nat.le_max_l | apply Nat.le_max_r].
Qed.

(* NEW *)
Lemma const_seq_cv : forall l, Un_cv (fun _ => l) l.
Proof. now intros l eps Heps; exists 0%nat; intros n _; rewrite Rdist_eq. Qed.

Lemma Un_cv_crit_lub : forall Un,
  Un_growing Un -> forall l, is_lub (EUn Un) l -> Un_cv Un l.
Proof.
  intros Un Hg l [Hub Hgt]%Un_lub_charac eps Heps.
  destruct (Hgt eps Heps) as [N HN]; exists N; intros n Hn.
  rewrite Rdist_def; apply Rabs_lt_iff; split.
  - apply Rgt_minus_chsd_rl; rewrite <-Rminus_def.
    apply (Rge_gt_trans _ (Un N)); [now apply growing_prop | now apply HN].
  - apply Rlt_minus_chsd_rl, (Rle_lt_trans _ l); [now apply Hub |].
    now apply Rplus_pos_gt.
Qed.

Lemma Un_cv_crit : forall Un,
  Un_growing Un -> bounded_from_above (EUn Un) -> exists l : R, Un_cv Un l.
Proof.
  intros Un Hug Heub.
  destruct (completeness (EUn Un) Heub (EUn_noempty Un)) as (l, H).
  now exists l; apply Un_cv_crit_lub.
Qed.

Lemma CV_shift :
  forall f k l, Un_cv (fun n => f (n + k)%nat) l -> Un_cv f l.
Proof.
  intros f' k l cvfk eps ep; destruct (cvfk eps ep) as [N Pn].
  exists (N + k)%nat; intros n nN.
  rewrite <-(Nat.sub_add k n) by
    now apply Nat.le_trans with (2 := nN); apply Nat.le_add_l.
  now apply Pn, Nat.le_add_le_sub_r.
Qed.

Lemma CV_shift' :
  forall f k l, Un_cv f l -> Un_cv (fun n => f (n + k)%nat) l.
Proof.
  intros f' k l cvf eps ep; destruct (cvf eps ep) as [N Pn].
  now exists N; intros n nN; apply Pn, Nat.le_trans with (1 := nN), Nat.le_add_r.
Qed.

(* NEW *)
Lemma CV_shift_succ :
  forall f l, Un_cv (fun n => f (S n)) l -> Un_cv f l.
Proof.
  intros f l H; apply (CV_shift _ 1), Un_cv_eq_compat with (2 := H).
  now intros n; rewrite Nat.add_1_r.
Qed.

(* NEW *)
Lemma CV_shift_succ' :
  forall f l, Un_cv f l -> Un_cv (fun n => f (S n)) l.
Proof.
  intros f l H%(CV_shift' _ 1); apply Un_cv_eq_compat with (2 := H).
  now intros n; rewrite Nat.add_1_r.
Qed.

Lemma growing_cv :
  forall Un:nat -> R, Un_growing Un -> has_ub Un -> { l:R | Un_cv Un l }.
Proof.
  intros Un Hug Heub.
  pose proof (completeness (EUn Un) Heub (EUn_noempty Un)) as [l Hl].
  now exists l; apply Un_cv_crit_lub.
Qed.

Lemma CV_opp :
  forall (An:nat -> R) (l:R), Un_cv An l -> Un_cv (opp_seq An) (- l).
Proof.
  intros An l HA eps Heps; destruct (HA eps Heps) as [N HN].
  exists N; intros n Hn; unfold opp_seq.
  rewrite <-(Rmult_1_l (An n)), <-(Rmult_1_l l), 2Ropp_mult_distr_l.
  now rewrite Rdist_mult_l, Rabs_Ropp, Rabs_1, Rmult_1_l; apply HN.
Qed.

Lemma decreasing_cv :
  forall Un:nat -> R, Un_decreasing Un -> has_lb Un -> { l:R | Un_cv Un l }.
Proof.
  intros Un Udec%decreasing_growing H.
  pose proof (growing_cv _ Udec) as [l Hl]; [assumption |].
  exists (- l); apply (Un_cv_eq_compat (fun n => - (opp_seq Un) n));
    [| now apply CV_opp].
  now intros n; unfold opp_seq; rewrite Ropp_involutive.
Qed.

Lemma growing_ineq :
  forall (Un:nat -> R) (l:R),
    Un_growing Un -> Un_cv Un l -> forall n:nat, Un n <= l.
Proof.
  intros Un l UG Utol n.
  apply Rle_plus_epsilon; intros eps Heps; destruct (Utol eps Heps) as [N HN].
  now destruct (Nat.le_ge_cases n N) as [I | I];
    [apply (Rle_trans _ (Un N)); [now apply tech9 |] |];
    apply Rle_minus_chsd_rl, Rle_trans with (1 := Rle_abs _);
    left; apply HN; [apply Nat.le_refl |].
Qed.

Lemma decreasing_ineq :
  forall (Un:nat -> R) (l:R),
    Un_decreasing Un -> Un_cv Un l -> forall n:nat, l <= Un n.
Proof.
  intros Un l H%decreasing_growing H'%CV_opp; intros n.
  apply Ropp_le_cancel; specialize (growing_ineq _ _ H H' n) as I.
  now apply I.
Qed.

Lemma CV_plus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i + Bn i) (l1 + l2).
Proof.
  intros An Bn l1 l2 H1 H2 eps Heps.
  assert (fact : eps / 2 > 0) by now apply Rdiv_pos_pos; [| exact Rlt_0_2].
  specialize (H1 (eps / 2) fact) as [N1 HN1].
  specialize (H2 (eps / 2) fact) as [N2 HN2].
  exists (Nat.max N1 N2); intros n Hn.
  rewrite <-(Rplus_half_diag eps).
  apply Rle_lt_trans with (1 := Rdist_plus _ _ _ _).
  now apply Rplus_lt_compat; [apply HN1 | apply HN2];
  apply Nat.le_trans with (2 := Hn); [apply Nat.le_max_l | apply Nat.le_max_r].
Qed.

Lemma cv_cvabs :
  forall (Un:nat -> R) (l:R),
    Un_cv Un l -> Un_cv (fun i:nat => Rabs (Un i)) (Rabs l).
Proof.
  intros Un l H eps Heps; destruct (H eps Heps) as [N HN]; exists N; intros n Hn.
  now apply Rle_lt_trans with (1 := Rabs_1_lipchitz _ _), HN.
Qed.

(* NEW, definition makes _proving_ "bounded" easier *)
Definition bounded (Un : nat -> R) := exists M, forall n, Rabs (Un n) <= M.

(* NEW, lemma makes _using_ "bounded" easier *)
Lemma bounded_pos_bound : forall (Un : nat -> R),
  (bounded Un) <-> (exists M, M > 0 /\ forall n, Rabs (Un n) < M).
Proof.
  intros Un; split; [| now intros [M [_ H]]; exists M; left; apply H].
  intros [M HM]; exists (M + 1); split.
  - apply Rplus_nneg_pos; [| apply Rlt_0_1].
    now apply Rle_trans with (2 := HM 0%nat); apply Rabs_pos.
  - intros n; apply Rle_lt_trans with (1 := HM _).
    apply Rplus_pos_gt, Rlt_0_1.
Qed.

(* NEW *)
Lemma CV_mult_0_bounded :
  forall An Bn, Un_cv An 0 -> bounded Bn -> Un_cv (fun n => An n * Bn n) 0.
Proof.
  intros An Bn HA [M [Mpos HM]]%bounded_pos_bound eps Heps.
  destruct (HA (eps / M)) as [N HN]; [now apply Rdiv_pos_pos |].
  exists N; intros n Hn.
  rewrite <-(Rmult_0_l (Bn n)), Rdist_mult_r, <-(Rdiv_mult_id_l eps M)
    by now apply Rgt_not_eq.
  now apply Rmult_le_0_lt_compat;
    [apply Rge_le, Rdist_pos | apply Rabs_pos | apply HN | apply HM].
Qed.

(* NEW *)
Lemma CV_scal_mult :
  forall Un K l, Un_cv Un l -> Un_cv (fun n => K * Un n) (K * l).
Proof.
  intros Un K l H eps Heps; destruct (Req_dec K 0) as [-> | H'%Rabs_pos_lt].
  - exists 0%nat; intros n Hn; rewrite 2Rmult_0_l, Rdist_def, Rminus_0_r.
    now rewrite Rabs_0.
  - destruct (H (eps / (Rabs K))) as [N HN]; [now apply Rdiv_pos_pos |].
    exists N; intros n Hn; rewrite Rdist_mult_l.
    now apply Rlt_mult_chsd_lr; [| apply HN].
Qed.

(* NEW *)
Lemma CV_minus_limit :
  forall Un l, Un_cv Un l <-> Un_cv (fun n => Un n - l) 0.
Proof.
  now intros Un l; split; intros H eps Heps; destruct (H eps Heps) as [N HN];
    exists N; intros n Hn; rewrite Rdist_def;
    [rewrite Rminus_0_r | rewrite <-(Rminus_0_r (Un n - l))]; apply HN.
Qed.

(* NEW *)
Lemma Un_cv_le_compat :
  forall Un Vn l1 l2, (forall n, Un n <= Vn n) -> Un_cv Un l1 -> Un_cv Vn l2
  -> l1 <= l2.
Proof.
  intros Un Vn l1 l2 I HU HV; apply Rle_plus_epsilon; intros eps Heps.
  assert (eps2 : eps / 2 > 0) by now apply Rdiv_pos_pos; [| apply Rlt_0_2].
  destruct (HU (eps / 2) eps2) as [N1 HN1]; clear HU.
  destruct (HV (eps / 2) eps2) as [N2 HN2]; clear HV.
  specialize (HN1 (Nat.max N1 N2) (Nat.le_max_l _ _)) as H1%Rabs_lt_iff.
  specialize (HN2 (Nat.max N1 N2) (Nat.le_max_r _ _)) as H2%Rabs_lt_iff.
  rewrite <-(Rplus_half_diag eps), <-Rplus_assoc; apply Rle_minus_chsd_rr.
  apply (Rle_trans _ (Un (Nat.max N1 N2))).
  - now apply Rle_minus_chsd_lr; left.
  - now apply Rle_trans with (1 := (I _)); apply Rle_minus_chsd_rl; left.
Qed.

(* NEW *)
Lemma Un_cv_bounded : forall Un, (exists l, Un_cv Un l) -> bounded Un.
Proof.
  intros Un [l Hl%cv_cvabs]; destruct (Hl 1 Rlt_0_1) as [N HN].
  destruct (finite_greater (fun n => Rabs (Un n)) N) as [M HM].
  exists ((Rmax M (Rabs l)) + 1); intros n.
  destruct (Nat.le_ge_cases n N) as [I | I].
  + apply Rle_trans with (2 := Rplus_0_le_ge _ _ Rle_0_1).
    apply Rle_trans with (2 := Rmax_l _ _).
    now apply HM.
  + rewrite <-(Rminus_plus_r (Rabs (Un n)) (Rabs l)); rewrite Rplus_comm.
    apply Rplus_le_compat; [apply Rmax_r |].
    apply Rle_trans with (1 := (Rle_abs _)).
    now left; apply HN.
Qed.

(* TODO: having sigma types as preconditions should be avoided. *)
Lemma maj_by_pos :
  forall Un:nat -> R,
    { l:R | Un_cv Un l } ->
    exists l : R, 0 < l /\ (forall n:nat, Rabs (Un n) <= l).
Proof.
  intros Un [l Hl].
  pose proof (Un_cv_bounded Un (ex_intro _ l Hl)) as [M HM]%bounded_pos_bound.
  now exists M; split; [| left].
Qed.

Lemma CV_minus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i - Bn i) (l1 - l2).
Proof.
  intros An Bn l1 l2 HA HB%CV_opp.
  apply (Un_cv_eq_compat (fun i => An i + opp_seq Bn i)).
  - now intros n; unfold opp_seq; rewrite Rminus_def.
  - now rewrite Rminus_def; apply CV_plus.
Qed.

Lemma CV_mult :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i * Bn i) (l1 * l2).
Proof.
  intros An Bn l1 l2 HA HB.
  apply (Un_cv_eq_compat (fun n => ((An n - l1) * (Bn n) + l1 * (Bn n)))).
    now intros n; rewrite Rmult_minus_distr_r, Rminus_plus_r.
  rewrite <-(Rplus_0_l (l1 * l2)); apply CV_plus.
  - apply CV_mult_0_bounded; [now apply ->CV_minus_limit |].
    now apply Un_cv_bounded; exists l2.
  - now apply CV_scal_mult.
Qed.

(* NEW *)
Lemma CV_inv :
  forall Un l, l <> 0 -> Un_cv Un l -> Un_cv (fun n => / Un n) (/ l).
Proof.
  intros Un l ln0 HU eps Heps.
  assert (abs_l_pos : Rabs l > 0) by now apply Rabs_pos_lt.
  assert (abs_l_2_pos : Rabs l / 2 > 0) by now apply Rdiv_pos_pos, Rlt_0_2.
  apply cv_cvabs in HU as Habs; destruct (Habs ((Rabs l) / 2)) as [N HN].
    now apply Rdiv_pos_pos, Rlt_0_2; apply Rabs_pos_lt.
  destruct (HU (eps * (Rabs l * ((Rabs l) / 2)))) as [N' HN'].
    now apply Rmult_pos_pos; [| apply Rmult_pos_pos].
  exists (Nat.max N N'); intros n [Hn1 Hn2]%Nat.max_lub_iff.
  specialize (HN n Hn1); specialize (HN' n Hn2); clear Hn1 Hn2 N N' HU Habs.
  rewrite Rdist_lt, <-(Rplus_half_diag (Rabs l)), Rplus_minus_l in HN at 1.
  assert (Un_n0 : Un n <> 0) by
    now apply Rabs_neq_0, Rgt_not_eq, Rgt_trans with (1 := (proj1 HN)).
  rewrite Rdist_def, <-2Rdiv_1_l, <-(Rdiv_mult_l_l l 1 (Un n)),
    <-(Rdiv_mult_l_r (Un n) 1 l), 2Rmult_1_r, <-Rdiv_minus_distr,
    Rabs_div, Rabs_mult by assumption.
  rewrite Rdist_sym, Rdist_def in HN'.
  apply Rlt_div_chsd_rr; [now apply Rmult_pos_pos; [| apply Rabs_pos_lt] |].
  apply Rlt_trans with (1 := HN'); rewrite <-2Rmult_assoc.
  now apply Rmult_lt_compat_l; [now apply Rmult_pos_pos |].
Qed.

(* NEW *)
Theorem seq_squeeze_thm_evtly :
  forall An Bn Un l, (exists N, forall n, (n >= N)%nat -> An n <= Un n <= Bn n)
  -> Un_cv An l -> Un_cv Bn l -> Un_cv Un l.
Proof.
  intros An Bn Un l [N1 H1] HA HB eps Heps.
  destruct (HA eps Heps) as [N2 H2].
  destruct (HB eps Heps) as [N3 H3].
  exists (Nat.max N1 (Nat.max N2 N3)).
  intros n [Hn [Hn' Hn'']%Nat.max_lub_iff]%Nat.max_lub_iff.
  setoid_rewrite Rdist_lt in H2.
  setoid_rewrite Rdist_lt in H3.
  specialize (H1 n Hn).
  apply Rdist_lt; split.
  - now apply Rlt_le_trans with (2 := proj1 H1), H2.
  - now apply Rle_lt_trans with (1 := proj2 H1), H3.
Qed.

(* NEW *)
Theorem seq_squeeze_thm :
  forall An Bn Un l, (forall n, An n <= Un n <= Bn n)
  -> Un_cv An l -> Un_cv Bn l -> Un_cv Un l.
Proof. now intros An Bn Un l H; apply seq_squeeze_thm_evtly; exists 0%nat. Qed.

(* NEW *)
Theorem adjacent_sequences_thm :
  forall An Bn, Un_growing An -> Un_decreasing Bn ->
    Un_cv (fun n => Bn n - An n) 0 -> { l | Un_cv An l /\ Un_cv Bn l }.
Proof.
  intros An Bn HA HB H.
  assert (dec : Un_decreasing (fun n => Bn n - An n)) by
    now intros n; apply Rminus_le_le_mono; [apply HB | apply HA].
  assert (ineq : forall n, An n <= Bn n).
    intros n; apply Rle_minus_le; generalize dependent n.
    now apply decreasing_ineq.
  assert ({l | Un_cv Bn l}) as [lb Hlb].
    apply decreasing_cv; [assumption | exists (- An 0%nat); intros x [i ->]].
    apply Ropp_le_contravar, (Rle_trans _ (An i)); [| apply ineq].
    now apply Rge_le, growing_prop; [| apply Nat.le_0_l].
  assert ({l | Un_cv An l}) as [la Hla].
    apply growing_cv; [assumption | exists (Bn 0%nat); intros x [i ->]].
    apply (Rle_trans _ (Bn i)); [apply ineq | apply decreasing_prop; [easy |]].
    now apply Nat.le_0_l.
  assert (eq : la = lb).
    apply eq_sym, Rminus_diag_uniq, (UL_sequence (fun n => Bn n - An n));
      [now apply CV_minus | assumption].
  now exists la; split; [exact Hla | rewrite <-eq in Hlb; exact Hlb].
Qed.

(* NEW *)
Lemma Un_cv_le :
  forall Un l, Un_cv Un l <->
  (forall eps, eps > 0 ->
    exists N, forall n, (n >= N)%nat -> Rdist (Un n) l <= eps).
Proof.
  intros Un l; split; intros HU eps Heps.
  - now destruct (HU eps Heps) as [N HN]; exists N; intros n Hn; left; apply HN.
  - assert (eps / 2 > 0) as He2 by now apply Rdiv_pos_pos; [| apply Rlt_0_2].
    destruct (HU (eps / 2) He2) as [N HN].
    exists N; intros n Hn; rewrite <-(Rplus_half_diag eps).
    apply Rle_lt_trans with (1 := HN n Hn).
    now apply Rplus_pos_gt.
Qed.

(** *** Cauchy sequences *)

Definition Cauchy_crit (Un : nat -> R) :=
  forall eps:R, eps > 0 -> exists N : nat, (forall n m:nat,
      (n >= N)%nat -> (m >= N)%nat -> Rdist (Un n) (Un m) < eps).

Lemma cauchy_bound :forall Un,  Cauchy_crit Un -> bounded_from_above (EUn Un).
Proof.
  intros Un Cauchy; specialize (Cauchy 1 Rlt_0_1) as [N HN].
  destruct (finite_greater Un N) as [M HM].
  exists (Rmax M (Un N + 1)); intros x [n ->].
  destruct (Nat.le_ge_cases n N) as [I | I].
  - now apply Rmax_Rle; left; apply HM.
  - apply Rmax_Rle; right; apply Rle_minus_chsd_rl.
    apply Rle_trans with (1 := Rle_abs _); left; apply HN;
      [assumption | apply Nat.le_refl].
Qed.

Lemma cauchy_maj : forall Un:nat -> R, Cauchy_crit Un -> has_ub Un.
Proof. now intros Un; apply cauchy_bound. Qed.

Lemma cauchy_opp :
  forall Un:nat -> R, Cauchy_crit Un -> Cauchy_crit (opp_seq Un).
Proof.
  intros Un CUn eps Heps.
  destruct (CUn eps Heps) as [N HN]; exists N; intros n m Hn Hm.
  unfold opp_seq; rewrite Rdist_def, <-Ropp_minus_distr, Rabs_Ropp.
  now rewrite Rminus_opp_r, Rplus_comm; apply HN.
Qed.

Lemma cauchy_min : forall Un:nat -> R, Cauchy_crit Un -> has_lb Un.
Proof. now intros Un H%cauchy_opp%cauchy_maj. Qed.

Lemma maj_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    { l:R | Un_cv (sequence_ub Un (cauchy_maj Un pr)) l }.
Proof.
  intros Un pr; apply decreasing_cv.
  - now apply Wn_decreasing.
  - now apply maj_min, cauchy_min.
Qed.

Lemma min_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    { l:R | Un_cv (sequence_lb Un (cauchy_min Un pr)) l }.
Proof.
  intros Un pr; apply growing_cv.
  - now apply Vn_growing.
  - now apply min_maj, cauchy_maj.
Qed.

(* NEW *)
Lemma Un_cv_cauchy :
  forall Un l, Un_cv Un l -> Cauchy_crit Un.
Proof.
  intros Un l Hl eps Heps.
  assert (fact: eps / 2 > 0) by now apply Rdiv_pos_pos; [| apply Rlt_0_2].
  destruct (Hl (eps / 2) fact) as [N HN]; exists N; intros n m Hn Hm.
  apply Rle_lt_trans with (1 := (Rdist_triangle _ _ l)).
  now rewrite (Rdist_sym l), <-(Rplus_half_diag eps); apply Rplus_lt_compat;
    apply HN.
Qed.

(* TODO: having sigma types as preconditions should be avoided. *)
Lemma CV_Cauchy :
  forall Un:nat -> R, { l:R | Un_cv Un l } -> Cauchy_crit Un.
Proof. now intros Un [l Hl%Un_cv_cauchy]. Qed.

Theorem R_complete :
  forall Un:nat -> R, Cauchy_crit Un -> { l:R | Un_cv Un l }.
Proof.
  intros Un H.
  remember (sequence_lb Un (cauchy_min Un H)) as Vn eqn:Vn_def.
  remember (sequence_ub Un (cauchy_maj Un H)) as Wn eqn:Wn_def.
  pose proof (Wn_decreasing Un (cauchy_maj Un H)) as Wn_dec.
  pose proof (Vn_growing Un (cauchy_min Un H)) as Vn_gro.
  pose proof (Vn_Un_Wn_order Un (cauchy_maj Un H) (cauchy_min Un H)) as order.
  rewrite <-Vn_def, <-Wn_def in *.
  enough (Un_cv (fun n => Wn n - Vn n) 0) as minus_cv.
    destruct (adjacent_sequences_thm Vn Wn Vn_gro Wn_dec minus_cv) as [l Hl].
    exists l; now apply (seq_squeeze_thm Vn Wn).
  apply Un_cv_le; intros eps Heps; destruct (H eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite Rdist_0_r, Rabs_nneg_id by
    now apply Rle_minus_le, (Rle_trans _ (Un n)); apply order.
  apply Rle_minus_chsd_rl.
  rewrite Wn_def; apply Un_lub_le; intros i.
  apply Rle_minus_chsd_rr.
  rewrite Vn_def; apply Un_glb_le; intros j.
  apply Rle_minus_chsd_rr, Rle_minus_chsd_rl; left.
  apply Rle_lt_trans with (1 := Rle_abs _).
  rewrite <-Rdist_def; apply HN; apply Nat.le_trans with (1 := Hn);
    now apply Nat.le_add_r.
Qed.

(* NEW *)
Lemma Un_cv_T : forall Un l, Un_cv Un l -> {l | Un_cv Un l}.
Proof. now intros Un l HU%Un_cv_cauchy; apply R_complete. Qed.

(* NEW *)
Lemma Un_cv_odd_even : forall Un l,
  (Un_cv (fun n => Un (2 * n)%nat) l /\ Un_cv (fun n => Un (S (2 * n))%nat) l)
  <-> Un_cv Un l.
Proof.
  intros Un l; split.
  - intros [cv_ev cv_odd]; intros eps Heps.
    destruct (cv_ev eps Heps) as [N1 HN1].
    destruct (cv_odd eps Heps) as [N2 HN2].
    exists (Nat.max (2 * N1) (2 * N2 + 1)); intros n [H1 H2]%Nat.max_lub_iff.
    destruct (Nat.EvenT_OddT_dec n) as [[m ->] | [m ->]].
    + now apply HN1, (Mult.mult_S_le_reg_l_stt 1), Nat.le_trans with (2 := H1).
    + rewrite Nat.add_1_r; apply HN2, (Mult.mult_S_le_reg_l_stt 1).
      now apply (Nat.add_le_mono_r _ _ 1).
  - now intros Ul; split; intros eps Heps; destruct (Ul eps Heps) as [N HN];
      exists N; intros n Hn; apply HN; [| apply Nat.le_le_succ_r];
      rewrite <-(Nat.mul_1_l N); apply Nat.mul_le_mono;
      try apply Nat.le_succ_diag_r.
Qed.

(** *** Divergence towards infinity *)

Definition cv_infty (Un:nat -> R) : Prop :=
  forall M:R,  exists N : nat, (forall n:nat, (N <= n)%nat -> M < Un n).

(* NEW *)
Lemma cv_infty_pos : forall Un,
  cv_infty Un <->
 (forall M, M > 0 -> exists N, forall n, (n >= N)%nat -> Un n > M).
Proof.
  intros Un; split; intros H; [now intros M _; apply H |].
  intros M; specialize (H ((Rabs M) + 1)) as [N HN].
  - now apply Rplus_nneg_pos; [apply Rabs_pos | apply Rlt_0_1].
  - exists N; intros n Hn; apply (Rlt_trans _ ((Rabs M) + 1)); [| now apply HN].
    apply Rle_lt_trans with (1 := (Rle_abs _)).
    apply Rplus_pos_gt, Rlt_0_1.
Qed.

Lemma cv_infty_cv_0 :
  forall Un:nat -> R, cv_infty Un -> Un_cv (fun n:nat => / Un n) 0.
Proof.
  intros Un H; intros eps Heps; destruct (H (/ eps)) as [N HN].
  exists N; intros n Hn.
  rewrite Rdist_def, Rminus_0_r, Rabs_pos_id by
    now apply Rinv_pos, (Rgt_trans _ (/ eps)); [apply HN | apply Rinv_pos].
  rewrite <-(Rinv_inv eps) by now apply Rgt_not_eq.
  apply Rinv_0_lt_contravar; [now apply Rinv_pos | now apply HN].
Qed.

(** *** Some examples *)

Lemma cv_pow : forall q, - 1 < q < 1 -> Un_cv (pow q) 0.
Proof.
  intros q Hq%Rabs_lt_iff eps Heps.
  destruct (pow_lt_1_zero q Hq eps Heps) as [N HN].
  now exists N; intros n Hn; rewrite Rdist_0_r; apply HN.
Qed.

(* NEW *)
Lemma geometric_seq_cv :
  forall a q, - 1 < q < 1 -> Un_cv (fun n => a * q ^ n) 0.
Proof.
  now intros a q Hq; rewrite <-(Rmult_0_r a); apply CV_scal_mult, cv_pow.
Qed.

Lemma cv_speed_pow_fact :
  forall x:R, Un_cv (fun n:nat => x ^ n / INR (fact n)) 0.
Proof.
  (* main idea: x ^ n / n! <= x ^ n / ((up x) ^ (n - (up x))
                            = (up x) ^ (up x) * (x / (up x)) ^ n.
     Since  x / (up x) < 1, then (x / (up x)) ^ n  -> 0 as n -> infty.
     A much shorter proof is possible using d'Alembert's ratio test but this
     proof should be writable without too much pain, otherwise this means
     that there are formalization problems. *)
  assert (key : forall n m, (n >= m)%nat -> (fact n >= m ^ (n - m))%nat). {
    intros n m H; induction H as [|n Hn IH].
    - now rewrite Nat.sub_diag, Nat.pow_0_r, <-fact_0; apply fact_le, Nat.le_0_l.
    - rewrite fact_succ, Nat.sub_succ_l by exact Hn.
      rewrite Nat.pow_succ_r by now apply Nat.le_0_l.
      now apply Nat.mul_le_mono; [apply Nat.le_le_succ_r | apply IH].
  }
  (* NOTE: please add some form of ssreflect's wlog tactic to vanilla *)
  enough (suf : forall x, 0 <= x -> Un_cv (fun n => x ^ n / INR (fact n)) 0). {
    intros x eps Heps; destruct (suf (Rabs x) (Rabs_pos x) eps Heps) as [N HN].
    exists N; intros n Hn; specialize (HN n Hn).
    rewrite Rdist_0_r, Rabs_div, <-RPow_abs, Rabs_nneg_id with (1 := pos_INR _).
    now apply Rle_lt_trans with (1 := Rle_abs _); rewrite <-Rdist_0_r.
  }
  intros x Hx; remember (Z.to_nat (up x)) as up_x eqn:up_x_def.
  assert (J : x < INR (up_x)) by
    now rewrite up_x_def, INR_IZR_INZ, Z2Nat.id; [now apply up_bounds |];
      apply le_IZR, Rlt_le, Rle_lt_trans with (1 := Hx), up_bounds.
  apply Rle_lt_trans with (1 := Hx) in J as J'.
  apply Rgt_not_eq in J' as J''.
  apply (seq_squeeze_thm_evtly (fun _ => 0)
          (fun n => INR up_x ^ up_x * (x / INR up_x) ^ n)).
  - exists up_x; intros n Hn; split.
    + now apply Rdiv_nneg_nneg, pos_INR; apply pow_le.
    + rewrite Rpow_div_distr, Rmult_div_assoc, Rmult_comm, Rdiv_def.
      rewrite <-Rmult_div_assoc; apply Rmult_le_compat_l; [now apply pow_le |].
      rewrite <-Rinv_div; apply Rinv_le_contravar;
        [now apply Rdiv_pos_pos; apply pow_lt |].
      rewrite Rdiv_pow, <-pow_INR by assumption.
      now apply le_INR, key.
  - apply const_seq_cv.
  - apply geometric_seq_cv, Rabs_lt_iff.
    now rewrite Rabs_nneg_id by (now apply Rdiv_nneg_nneg, Rlt_le);
    apply Rlt_div_chsd_rr; [| rewrite Rmult_1_l].
Qed.

Lemma INR_cv_infty : cv_infty INR.
Proof.
  intros M; destruct (INR_unbounded M) as [N HN]; exists N; intros n Hn.
  now apply Rlt_le_trans with (1 := HN), le_INR.
Qed.

(* NEW *)
Lemma Un_infty_quotient_1 : forall (Un : nat -> R) a b, cv_infty Un ->
  Un_cv (fun n => (Un n + a) / (Un n + b)) 1.
Proof.
  intros Un a b Udv. apply CV_minus_limit.
  destruct (Udv (- b)) as [N HN].
  apply (Un_cv_evtly_eq_compat (fun n => (a - b) * / (Un n + b))). {
    exists N; intros n Hn.
    rewrite <-(Rdiv_diag (Un n + b)) at 1 by
      now apply Rgt_not_eq, Rgt_plus_chsd_rr; rewrite Rminus_0_l; apply HN.
    now rewrite <-Rdiv_minus_distr, Rminus_plus_l_l.
  }
  rewrite <-(Rmult_0_r (a - b)); apply CV_scal_mult, cv_infty_cv_0.
  intros A; destruct (Udv (A - b)) as [N' H']; exists N'; intros n Hn.
  now apply Rlt_minus_chsd_rr; apply H'.
Qed.

(** *** Miscellaneous *)

(** **** Running maximum of a sequence *)

Fixpoint Rmax_N (Un : nat -> R) (N:nat) : R :=
  match N with
    | O => Un 0%nat
    | S n => Rmax (Un (S n)) (Rmax_N Un n)
  end.

(* NEW *)
Lemma Rmax_N_0 : forall Un, Rmax_N Un 0 = Un 0%nat.
Proof. reflexivity. Qed.

(* NEW *)
Lemma Rmax_N_succ : forall Un n, Rmax_N Un (S n) = Rmax (Un (S n)) (Rmax_N Un n).
Proof. reflexivity. Qed.

(** ** Finite sums *)

(** This part deals with sums of the form (f 0) + (f 1) + ... + (f (n - 1)),
    with f : Nat -> R.
    For historical reasons, there are two functions defining such sums.
    The legacy one is defined in Rfunctions (again for historical reasons) as
    sum_f_R0 f n = (f 0) + (f 1) + ... + (f n)
    Since it offers no empty sum, it is not very convenient to use and lemmas
    about sum_f_R0 often have too many side conditions.

    A new alternative is
    Rsum f n = (f 0) + (f 1) + ... + (f (n - 1))
    with Rsum f 0 = 0. Despite the very small change, it proves much more
    convenient to use in the long run.

    However, it seems not possible at this time to completely remove [sum_f_R0]
    so we will give two versions of some lemmas and provide a translation lemma
    between the two sums ([sum_f_R0_Rsum) *)

(** *** Basic lemmas about Rsum *)

Fixpoint Rsum (f : nat -> R) (n : nat) :=
  match n with
  | 0%nat => 0
  | S n' => Rsum f n' + f n'
  end.

Lemma Rsum_0 : forall f, Rsum f 0 = 0.
Proof. reflexivity. Qed.

Lemma Rsum_succ_r : forall f n, Rsum f (S n) = Rsum f n + f n.
Proof. reflexivity. Qed.

Lemma Rsum_1 : forall f, Rsum f 1 = f 0%nat.
Proof. now intros f; rewrite Rsum_succ_r, Rsum_0, Rplus_0_l. Qed.

Lemma Rsum_sum_f_R0 : forall f n, Rsum f (S n) = sum_f_R0 f n.
Proof.
  intros f n; induction n as [| n IH].
  - now rewrite Rsum_succ_r, sum_f_R0_0, Rsum_0, Rplus_0_l.
  - now rewrite Rsum_succ_r, sum_f_R0_succ, IH.
Qed.

Lemma Rsum_succ_l : forall f n,
  Rsum f (S n) = f 0%nat + Rsum (fun i => f (S i)) n.
Proof.
  intros f n; induction n as [| n IH].
  - now rewrite Rsum_succ_r, 2Rsum_0, Rplus_0_r, Rplus_0_l.
  - now rewrite Rsum_succ_r, IH, Rsum_succ_r, Rplus_assoc.
Qed.

Lemma Rsum_succ_l_eq : forall f n x,
  x = f 0%nat -> Rsum f (S n) = x + Rsum (fun i => f (S i)) n.
Proof. now intros f n x ->; apply Rsum_succ_l. Qed.

Lemma Rsum_add : forall f n m,
  Rsum f (n + m) = Rsum f n + Rsum (fun i => f (n + i)%nat) m.
Proof.
  intros f n m; induction m as [| m IH].
  - now rewrite Nat.add_0_r, Rsum_0, Rplus_0_r.
  - now rewrite Nat.add_succ_r, 2Rsum_succ_r, IH, Rplus_assoc.
Qed.

Lemma Rsum_sub : forall f n m, (n >= m)%nat ->
  Rsum (fun i => f (m + i)%nat) (n - m) = Rsum f n - Rsum f m.
Proof.
  intros f n m H.
  rewrite <-(Arith_prebase.le_plus_minus_r_stt m n), Rsum_add, Rplus_minus_l
    by assumption.
  now rewrite Nat.add_sub_swap, Nat.sub_diag, Nat.add_0_l
    by now apply Nat.le_refl.
Qed.

Lemma Rsum_plus : forall f g n,
  Rsum (fun i => f i + g i) n = Rsum f n + Rsum g n.
Proof.
  intros f g n; induction n as [| n IH].
  - now rewrite 3Rsum_0, Rplus_0_r.
  - now rewrite 3Rsum_succ_r, IH, <-!Rplus_assoc, (Rplus_3perm_lrm _ _ (f n)).
Qed.

Lemma Rsum_scal_l : forall f l n,
  Rsum (fun i => l * f i) n = l * Rsum f n.
Proof.
  intros f l n; induction n as [| n IH].
  - now rewrite 2Rsum_0, Rmult_0_r.
  - now rewrite 2Rsum_succ_r, IH, Rmult_plus_distr_l.
Qed.

Lemma Rsum_scal_r : forall f l n,
  Rsum (fun i => f i * l) n = Rsum f n * l.
Proof.
  intros f l n; induction n as [| n IH].
  - now rewrite 2Rsum_0, Rmult_0_l.
  - now rewrite 2Rsum_succ_r, IH, Rmult_plus_distr_r.
Qed.

Lemma Rsum_opp : forall f n, Rsum (fun i => - f i) n = - Rsum f n.
Proof.
  intros f n; induction n as [| n IH].
  - now rewrite 2Rsum_0, Ropp_0.
  - now rewrite 2Rsum_succ_r, IH, Ropp_plus_distr.
Qed.

Lemma Rsum_pos_compat : forall f n,
  (forall i, (i <= n)%nat -> f i > 0) -> Rsum f (S n) > 0.
Proof.
  intros f n H; induction n as [| n IH].
  - now rewrite Rsum_succ_r, Rsum_0, Rplus_0_l; apply (H 0%nat), Nat.le_refl.
  - rewrite Rsum_succ_r; apply Rplus_pos_pos; [apply IH | apply (H (S n))].
    + now intros i Hi%Nat.le_le_succ_r; apply H.
    + now apply Nat.le_refl.
Qed.

Lemma Rsum_nneg_compat : forall f n,
  (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= Rsum f n.
Proof.
  intros f n H; induction n as [| n IH].
  - now rewrite Rsum_0; apply Rle_refl.
  - rewrite Rsum_succ_r; apply Rplus_nneg_nneg; [apply IH | apply H].
    + now intros i Hi; apply H, Nat.lt_lt_succ_r.
    + now apply Nat.lt_succ_diag_r.
Qed.

Lemma Rsum_neg_compat : forall f n,
  (forall i, (i <= n)%nat -> f i < 0) -> Rsum f (S n) < 0.
Proof.
  intros f n H. apply Ropp_lt_cancel; rewrite Ropp_0, <-Rsum_opp.
  now apply Rsum_pos_compat; intros i Hi; apply Ropp_neg, H.
Qed.

Lemma Rsum_npos_compat : forall f n,
  (forall i, (i < n)%nat -> f i <= 0) -> Rsum f n <= 0.
Proof.
  intros f n H. apply Ropp_le_cancel; rewrite Ropp_0, <-Rsum_opp.
  now apply Rsum_nneg_compat; intros i Hi; apply Ropp_npos, H.
Qed.

Lemma Rsum_eq_compat : forall f g n,
  (forall i, (i < n)%nat -> f i = g i) -> Rsum f n = Rsum g n.
Proof.
  intros f g n H; induction n as [| n IH].
  - now rewrite 2Rsum_0.
  - rewrite 2Rsum_succ_r, IH, H; [easy | apply Nat.lt_succ_diag_r|].
    now intros i Hi%Nat.lt_lt_succ_r; apply H.
Qed.

Lemma Rsum_eq_0_compat : forall f n,
  (forall i, (i < n)%nat -> f i = 0) -> Rsum f n = 0.
Proof.
  intros f; induction n as [| n IH]; intros H; [now rewrite Rsum_0 |].
  rewrite Rsum_succ_r, H, Rplus_0_r by now apply Nat.lt_succ_diag_r.
  now apply IH; intros i HI%Nat.lt_lt_succ_r; apply H.
Qed.

Lemma Rsum_le_compat : forall f g n,
  (forall i, (i < n)%nat -> f i <= g i) -> Rsum f n <= Rsum g n.
Proof.
  intros f g n H; induction n as [| n IH].
  - now rewrite 2Rsum_0; apply Rle_refl.
  - rewrite 2Rsum_succ_r; apply Rplus_le_compat; [apply IH | apply H].
    + now intros i Hi%Nat.lt_lt_succ_r; apply H.
    + now apply Nat.lt_succ_diag_r.
Qed.

Lemma Rsum_lt_compat : forall f g n,
  (forall i, (i <= n)%nat -> f i < g i) -> Rsum f (S n) < Rsum g (S n).
Proof.
  intros f g n H; induction n as [| n IH].
  - now rewrite 2Rsum_1; apply H.
  - rewrite 2Rsum_succ_r; apply Rplus_lt_compat; [apply IH | apply H].
    + now intros i Hi%Nat.le_le_succ_r; apply H.
    + now apply Nat.le_refl.
Qed.

(** [w] stands for "weak" :
    these weakened versions are more practical in many cases *)
Lemma Rsum_pos_compat_w :
  forall f, (forall i, f i > 0) -> forall n, Rsum f (S n) > 0.
Proof. now intros f H n; apply Rsum_pos_compat; intros i _. Qed.

Lemma Rsum_nneg_compat_w :
  forall f, (forall i, 0 <= f i) -> forall n, 0 <= Rsum f n.
Proof. now intros f H n; apply Rsum_nneg_compat; intros i _. Qed.

Lemma Rsum_neg_compat_w : forall f,
  (forall i, f i < 0) -> forall n, Rsum f (S n) < 0.
Proof. now intros f H n; apply Rsum_neg_compat; intros i _. Qed.

Lemma Rsum_npos_compat_w : forall f,
  (forall i, f i <= 0) -> forall n, Rsum f n <= 0.
Proof. now intros f H n; apply Rsum_npos_compat; intros i _. Qed.

Lemma Rsum_eq_compat_w :
  forall f g, (forall i, f i = g i) -> forall n, Rsum f n = Rsum g n.
Proof. now intros f g H n; apply Rsum_eq_compat; intros i _. Qed.

Lemma Rsum_eq_0_compat_w : forall f,
  (forall i, f i = 0) -> forall n, Rsum f n = 0.
Proof. now intros f H n; apply Rsum_eq_0_compat; intros i _. Qed.

Lemma Rsum_le_compat_w : forall f g,
  (forall i, f i <= g i) -> forall n, Rsum f n <= Rsum g n.
Proof. now intros f g H n; apply Rsum_le_compat; intros i _. Qed.

Lemma Rsum_lt_compat_w : forall f g,
  (forall i, f i < g i) -> forall n, Rsum f (S n) < Rsum g (S n).
Proof. now intros f g H n; apply Rsum_lt_compat; intros i _. Qed.

Lemma Rsum_minus : forall f g n,
  Rsum (fun i => f i - g i) n = Rsum f n - Rsum g n.
Proof.
  intros f g n; rewrite Rminus_def, <-Rsum_opp, <-Rsum_plus.
  now apply Rsum_eq_compat_w; intros i; rewrite Rminus_def.
Qed.

Lemma Rsum_triangle : forall f n,
  Rabs (Rsum f n) <= Rsum (fun i => Rabs (f i)) n.
Proof.
  intros f n; induction n as [| n IH].
  - now rewrite !Rsum_0, !Rabs_0; apply Rle_refl.
  - rewrite 2!Rsum_succ_r; apply Rle_trans with (1 := Rabs_triangle _ _).
    now apply Rplus_le_compat; [apply IH | apply Rle_refl].
Qed.

(** *** Lemmas about sum_f_R0 *)

(* NEW, while not strictly necessary because of Rsum_sum_f_R0,
   it helps instanciate other lemmas with things like (1 := (sum_f_R0_Rsum _)).
   Also, there will be a lot of translations... *)
Lemma sum_f_R0_Rsum : forall f n, sum_f_R0 f n = Rsum f (S n).
Proof. now intros f n; rewrite <-Rsum_sum_f_R0. Qed.

(* NEW name *)
Lemma sum_f_R0_pos_compat : forall An N,
  (forall n:nat, (n <= N)%nat -> 0 < An n) -> 0 < sum_f_R0 An N.
Proof. now intros An N H; rewrite !sum_f_R0_Rsum; apply Rsum_pos_compat. Qed.
Notation tech1 := sum_f_R0_pos_compat.

(* NEW name, Chasles' relation *)
Lemma sum_f_R0_chasles :
  forall An m n, (m < n)%nat ->
    sum_f_R0 An n =
    sum_f_R0 An m + sum_f_R0 (fun i:nat => An (S m + i)%nat) (n - S m).
Proof.
  intros An m n I; rewrite !sum_f_R0_Rsum.
  rewrite <-(Arith_prebase.le_plus_minus_r_stt (S m) (S n)) by
    now apply ->Nat.succ_le_mono; apply Nat.lt_le_incl.
  now rewrite Rsum_add, Nat.sub_succ_l.
Qed.
Notation tech2 := sum_f_R0_chasles (only parsing).

Lemma plus_sum :
  forall (An Bn:nat -> R) (N:nat),
    sum_f_R0 (fun i:nat => An i + Bn i) N = sum_f_R0 An N + sum_f_R0 Bn N.
Proof. now intros An Bn N; rewrite !sum_f_R0_Rsum; apply Rsum_plus. Qed.

Lemma sum_eq :
  forall (An Bn:nat -> R) (N:nat),
    (forall i:nat, (i <= N)%nat -> An i = Bn i) ->
    sum_f_R0 An N = sum_f_R0 Bn N.
Proof.
  intros An Bn N H; rewrite !sum_f_R0_Rsum; apply Rsum_eq_compat.
  now intros i Hi; apply H, Nat.succ_le_mono.
Qed.

(* NEW *)
Lemma sum_f_R0_opp :
  forall An N, sum_f_R0 (fun n => - An n) N = - sum_f_R0 An N.
Proof. now intros An N; rewrite !sum_f_R0_Rsum, Rsum_opp. Qed.

Lemma scal_sum :
  forall (An:nat -> R) (N:nat) (x:R),
    x * sum_f_R0 An N = sum_f_R0 (fun i:nat => An i * x) N.
Proof. now intros An N x; rewrite Rmult_comm, !sum_f_R0_Rsum, Rsum_scal_r. Qed.

(* NEW *)
Lemma scal_sum_l :
  forall (An:nat -> R) (N:nat) (x:R),
    x * sum_f_R0 An N = sum_f_R0 (fun i:nat => x * An i) N.
Proof. now intros An N x; rewrite !sum_f_R0_Rsum, Rsum_scal_l. Qed.

Lemma decomp_sum :
  forall (An:nat -> R) (N:nat),
    (0 < N)%nat ->
    sum_f_R0 An N = An 0%nat + sum_f_R0 (fun i:nat => An (S i)) (pred N).
Proof.
  intros An N H; rewrite <-!Rsum_sum_f_R0, Rsum_succ_l; f_equal.
  now rewrite Nat.succ_pred; [reflexivity | apply Nat.neq_0_lt_0].
Qed.

Lemma minus_sum :
  forall (An Bn:nat -> R) (N:nat),
    sum_f_R0 (fun i:nat => An i - Bn i) N = sum_f_R0 An N - sum_f_R0 Bn N.
Proof. now intros An Bn N; rewrite !sum_f_R0_Rsum, Rsum_minus. Qed.

Lemma sum_decomposition :
  forall (An:nat -> R) (N:nat),
    sum_f_R0 (fun l:nat => An (2 * l)%nat) (S N) +
    sum_f_R0 (fun l:nat => An (S (2 * l))) N = sum_f_R0 An (2 * S N).
Proof.
  intros An N; induction N as [| N IH].
  - rewrite Nat.mul_1_r, 3sum_f_R0_succ, Nat.mul_1_r, 3sum_f_R0_0.
    now rewrite Nat.mul_0_r, Rplus_3perm_lrm.
  - rewrite sum_f_R0_succ.
    rewrite (sum_f_R0_succ (fun l : nat => An (S (2 * l)))), <-Rplus_assoc.
    rewrite (Rplus_3perm_lrm _ (An _)), IH.
    rewrite (Nat.mul_succ_r _ (S N)), Nat.add_succ_r, Nat.add_1_r.
    now rewrite 2sum_f_R0_succ, Rplus_3perm_lrm.
Qed.

Lemma sum_Rle :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> An n <= Bn n) ->
    sum_f_R0 An N <= sum_f_R0 Bn N.
Proof.
  intros An Bn N H; rewrite <-!Rsum_sum_f_R0; apply Rsum_le_compat.
  now intros i Hi; apply H, Nat.succ_le_mono.
Qed.

Lemma sum_cte :
  forall (x:R) (N:nat), sum_f_R0 (fun _:nat => x) N = x * INR (S N).
Proof.
  intros x N; induction N as [| N IH].
  - now rewrite sum_f_R0_0, INR_IZR_INZ, Rmult_1_r.
  - rewrite sum_f_R0_succ, IH; rewrite <-(Rmult_1_r x) at 2.
    now rewrite <-Rmult_plus_distr_l, <-S_INR.
Qed.

Lemma cond_pos_sum :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, 0 <= An n) -> 0 <= sum_f_R0 An N.
Proof. now intros An N H; rewrite sum_f_R0_Rsum; apply Rsum_nneg_compat. Qed.

Lemma sum_eq_R0 :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> An n = 0) -> sum_f_R0 An N = 0.
Proof.
  intros An N H; rewrite sum_f_R0_Rsum; apply Rsum_eq_0_compat.
  now intros i HI; apply H, Nat.succ_le_mono.
Qed.

Lemma sum_N_predN :
  forall (An:nat -> R) (N:nat),
    (0 < N)%nat -> sum_f_R0 An N = sum_f_R0 An (pred N) + An N.
Proof.
  now intros An [| N] HN; [easy |]; rewrite Nat.pred_succ, sum_f_R0_succ.
Qed.

(** *** Some classical computations of sums *)

(** **** Geometric series *)

(* TODO: what to do with this? almost the same as
         Coq.Reals.Rfunctions.GP_finite *)
Lemma tech3 :
  forall (k:R) (N:nat),
    k <> 1 -> sum_f_R0 (fun i:nat => k ^ i) N = (1 - k ^ S N) / (1 - k).
Proof.
  intros k N Hk%Rminus_eq_contra; rewrite Rdiv_minus_minus_sym.
  now apply Req_mult_chsd_rr; [assumption |]; rewrite GP_finite, Nat.add_1_r.
Qed.

(** **** A summation formula with Cauchy product *)

(* NOTE: The proof of the following lemma showcases the benefits of using Rsum
   over sum_f_R0. While using almost no automation (no ring, lra, lia, auto) the
   proof is reduced to about 30 lines whereas the proof is a 182 lines nightmare
   in upstream (8.18+alpha) and 400 lines in 8.16. *)

Theorem Rsum_cauchy_finite :
  forall f g n, Rsum f (S n) * Rsum g (S n) =
    Rsum (fun i => Rsum (fun j => f j * g (i - j)%nat) (S i)) (S n) +
    Rsum (fun i => Rsum (fun j => f (S i + j)%nat * g (n - j)%nat)
      (S n - S i)%nat) n.
Proof.
  intros f g n; induction n as [| n IH];
    [now rewrite Rsum_0, !Rsum_1, Nat.sub_0_r, Rplus_0_r |].
  rewrite (Rsum_succ_r (fun _ => Rsum _ _)), Rplus_assoc.
  rewrite (Rsum_succ_r f), (Rsum_succ_r g).
  rewrite Rmult_plus_distr_r, 2Rmult_plus_distr_l, IH, !Rplus_assoc; f_equal.
  (* First problem : Coq does not understand that the function in the last
     sum has the form Rsum (fun i => phi (S i)) *)
  set (phi := fun i => Rsum (fun j => f (i + j)%nat * g (S n - j)%nat) (S (S n) - i)).
  rewrite (Rsum_eq_compat (fun _ => Rsum _ (S (S n) - _)) (fun i => phi (S i)))
    by now intros i Hi; unfold phi.
  rewrite <-Rsum_succ_l_eq by now unfold phi; rewrite Nat.sub_0_r;
    apply Rsum_eq_compat_w; intros i; rewrite Nat.add_0_l.
  unfold phi; clear phi.

  (* Second problem : cannot rewrite under Rsum *)
  rewrite (Rsum_eq_compat (fun i => Rsum _ _) (fun i => f (S n) * (g i) +
       Rsum (fun j => f (i + j)%nat * g (S n - j)%nat) (S n - i)) (S (S n)));
    cycle 1. {
    intros i Hi%Arith_prebase.lt_n_Sm_le.
    rewrite (Nat.sub_succ_l _ (S n)), Rsum_succ_r, Rplus_comm by easy; f_equal.
    now rewrite Arith_prebase.le_plus_minus_r_stt, Private_sub_sub_id_r.
  }
  rewrite Rsum_plus, <-(Rsum_scal_l _ (f (S n))), <-Rsum_succ_r.
  rewrite <-!Rplus_assoc, Rplus_3perm_rml, !Rplus_assoc; f_equal.

  rewrite (Rsum_succ_r _ (S n)), Nat.sub_diag, Rsum_0, Rplus_0_r.
  (* Second problem again : cannot rewrite under Rsum *)
  rewrite (Rsum_eq_compat (fun i => Rsum _ (_ - i)) (fun i => f i * g (S n) +
    Rsum (fun j : nat => f (i + S j)%nat * g (S n - S j)%nat) (n - i)) (S n))
    by (now intros i Hi%Arith_prebase.lt_n_Sm_le;
    rewrite Nat.sub_succ_l, Rsum_succ_l, Nat.add_0_r, Nat.sub_0_r).
  rewrite Rsum_plus; f_equal; [now rewrite Rsum_scal_r |].

  rewrite Rsum_succ_r, Nat.sub_diag, Rsum_0, Rplus_0_r; apply Rsum_eq_compat.
  intros i _; rewrite Nat.sub_succ; apply Rsum_eq_compat.
  now intros j _; rewrite Nat.add_succ_comm, Nat.sub_succ.
Qed.

(** **** Newton's binomial theorem *)

Definition C (n p:nat) : R :=
  INR (fact n) / (INR (fact p) * INR (fact (n - p))).

Lemma pascal_step1 : forall n i:nat, (i <= n)%nat -> C n i = C n (n - i).
Proof.
  intros n i Hn; unfold C; rewrite Rmult_comm.
  now replace (n - (n - i))%nat with i by
    now symmetry; apply Nat.add_sub_eq_l, Nat.sub_add.
Qed.

Lemma pascal_step2 :
  forall n i:nat,
    (i <= n)%nat -> C (S n) i = INR (S n) / INR (S n - i) * C n i.
Proof.
  intros n u Hi; unfold C; rewrite Rmult_div, <-Rmult_assoc.
  rewrite Rmult_3perm_mlr, Nat.sub_succ_l, Rmult_assoc by assumption.
  now rewrite <-2(mult_INR (S _)), <-2fact_succ.
Qed.

Lemma pascal_step3 :
  forall n i:nat, (i < n)%nat -> C n (S i) = INR (n - i) / INR (S i) * C n i.
Proof.
  intros n i Hi; unfold C; rewrite Rmult_div.
  rewrite Nat.sub_succ_r, fact_succ, mult_INR.
  rewrite <-(Nat.succ_pred (n - i)) at 3 by now apply Nat.sub_gt.
  rewrite fact_succ, Nat.succ_pred by now apply Nat.sub_gt.
  rewrite mult_INR, <-!Rmult_assoc.
  now rewrite (Rmult_3perm_mrl _ _ (INR (n - i))), !Rmult_assoc, Rdiv_mult_l_l;
    [| apply not_0_INR, Nat.sub_gt].
Qed.

Lemma pascal :
  forall n i:nat, (i < n)%nat -> C n i + C n (S i) = C (S n) (S i).
Proof.
  intros n i Hi; rewrite pascal_step3 by assumption; unfold C.
  rewrite Rmult_div, <-(Rdiv_mult_l_l (INR (S i))), <-Rdiv_plus_distr by
    now apply not_0_INR.
  rewrite Nat.sub_succ, (fact_succ i), mult_INR, Rmult_assoc; f_equal.
  rewrite <-Rmult_plus_distr_r, <-plus_INR, Nat.add_succ_l.
  rewrite Arith_prebase.le_plus_minus_r_stt by now apply Nat.lt_le_incl.
  now rewrite fact_succ, mult_INR.
Qed.

(* NEW *)
Lemma binomial_coeff_diag : forall n, C n n = 1.
Proof.
  intros n; unfold C; rewrite Nat.sub_diag, fact_0, INR_1, Rmult_1_r.
  now rewrite Rdiv_diag; [reflexivity |]; apply not_0_INR, fact_neq_0.
Qed.

(* NEW *)
Lemma binomial_coeff_0_r : forall n, C n 0 = 1.
Proof.
  intros n; unfold C; rewrite Nat.sub_0_r, fact_0, INR_1, Rmult_1_l.
  now rewrite Rdiv_diag; [reflexivity |]; apply not_0_INR, fact_neq_0.
Qed.

Lemma Newton's_binomial_thm :
  forall x y n, (x + y) ^ n = Rsum (fun i => C n i * x ^ i * y ^ (n - i)) (S n).
Proof.
  intros x y n; induction n as [| n IH].
    now rewrite Rsum_1, Nat.sub_0_r, !pow_0_r, binomial_coeff_0_r, !Rmult_1_l.
  rewrite pow_succ, Rmult_plus_distr_r, (Rmult_comm y), IH.
  rewrite <-Rsum_scal_l, <-Rsum_scal_r.
  rewrite Rsum_succ_r, (Rplus_comm _ (x * _)).
  rewrite Rsum_succ_l, (Rplus_comm (_ * y)).
  rewrite Rplus_assoc, <-(Rplus_assoc _ _ (_ * y)), <-Rsum_plus.
  rewrite <-!Rmult_assoc, (Rmult_3perm_mlr x), (Rmult_assoc _ x), <-pow_succ.
  rewrite <-(Nat.sub_succ n), binomial_coeff_diag, <-(binomial_coeff_diag (S n)).
  rewrite !Rmult_assoc, (Rmult_comm _ y), <-pow_succ, <-Nat.sub_succ_l
    by now apply Nat.le_0_l.
  rewrite Rsum_succ_r, (Rplus_comm _ (_ * x ^ (S n) * _)), Rmult_assoc; f_equal.
  rewrite Rsum_succ_l, Rplus_comm, Rmult_assoc, 2!binomial_coeff_0_r; f_equal.
  apply Rsum_eq_compat; intros i Hi.
  rewrite <-pascal by assumption; rewrite 2Rmult_plus_distr_r; f_equal.
  - rewrite Nat.sub_succ, <-!Rmult_assoc; f_equal.
    now rewrite (Rmult_comm x), Rmult_assoc, pow_succ.
  - now rewrite !Rmult_assoc, (Rmult_comm _ y), <-pow_succ, Nat.sub_succ_l
      by now apply Nat.le_succ_l.
Qed.

Lemma binomial :
  forall (x y:R) (n:nat),
    (x + y) ^ n = sum_f_R0 (fun i:nat => C n i * x ^ i * y ^ (n - i)) n.
Proof. intros x y n; rewrite <-Rsum_sum_f_R0; apply Newton's_binomial_thm. Qed.

(** *** Convergence of series *)

(** **** Definition of convergence and basic properties *)

(* NOTE: A notation is better than a definition (e.g. of infinite_sum)
   because needs no unfolding *)
Notation Rseries_cv := (fun f l => Un_cv (fun n => Rsum f n) l).

Lemma Rseries_unique_sum : forall f l1 l2,
  Rseries_cv f l1 -> Rseries_cv f l2 -> l1 = l2.
Proof. now intros l1 l2; apply UL_sequence. Qed.

Lemma Rseries_abs_cv : forall f l,
  Rseries_cv (fun i => Rabs (f i)) l -> {l | Rseries_cv f l}.
Proof.
  intros f l H%Un_cv_cauchy; apply R_complete; intros eps Heps.
  destruct (H eps Heps) as [N HN]; exists N.
  intros n m Hn Hm; destruct (Nat.le_ge_cases n m) as [I | I];
    [rewrite Rdist_sym |].
  (* NOTE: something better than all: ...; ...; ... to handle identical goals
     and contexts would be welcome. [enough] is not enough (no pun intended)
     because it forces you to rewrite the goal. *)
  all: rewrite Rdist_def, <-Rsum_sub by easy;
    apply Rle_lt_trans with (1 := Rsum_triangle _ _);
    apply Rle_lt_trans with (1 := Rle_abs _);
    (* NOTE: Why does coq fail to instantiate the function in Rsum_sub? *)
    rewrite (Rsum_sub (fun i => _ (_ i))) by assumption;
    apply HN; assumption.
Qed.

(** For historical reasons, infinite_sum is in Coq.Reals.Rfunctions.
    Its name may be misleading since it is a finite limit of a sum. *)

(* NEW *)
Lemma infinite_sum_Un_cv :
  forall An l, infinite_sum An l <-> Un_cv (fun N => sum_f_R0 An N) l.
Proof. now intros An l; split. Qed.

Lemma Un_cv_Rsum_sum_f_R0 :
  forall f l, Un_cv (Rsum f) l <-> Un_cv (sum_f_R0 f) l.
Proof.
  intros f l; split; intros H.
  - apply CV_shift_succ' in H; apply Un_cv_eq_compat with (2 := H).
    now intros n; rewrite sum_f_R0_Rsum.
  - apply CV_shift_succ, Un_cv_eq_compat with (2 := H).
    now intros n; rewrite Rsum_sum_f_R0.
Qed.

Lemma Rseries_cv_infinite_sum :
  forall f l, Rseries_cv f l <-> infinite_sum f l.
Proof.
  intros f l; rewrite infinite_sum_Un_cv.
  now apply Un_cv_Rsum_sum_f_R0.
Qed.

(* Unicity of the limit defined by convergent series *)
Lemma uniqueness_sum :
  forall (An:nat -> R) (l1 l2:R),
    infinite_sum An l1 -> infinite_sum An l2 -> l1 = l2.
Proof.
  now intros An l1 l2; rewrite <-!Rseries_cv_infinite_sum;
    apply Rseries_unique_sum.
Qed.

(* Cauchy's criterion for series *)
Definition Cauchy_crit_series (An:nat -> R) : Prop :=
  Cauchy_crit (fun N:nat => sum_f_R0 An N).

(* If (|An|) satisfies the Cauchy's criterion for series, then (An) too *)
Lemma cauchy_abs :
  forall An:nat -> R,
    Cauchy_crit_series (fun i:nat => Rabs (An i)) -> Cauchy_crit_series An.
Proof.
  intros An [l Hl]%R_complete; apply CV_Cauchy.
  apply Un_cv_Rsum_sum_f_R0, Rseries_abs_cv in Hl as [l' Hl']; clear l.
  now exists l'; apply Un_cv_Rsum_sum_f_R0.
Qed.

Lemma cv_cauchy_1 :
  forall An:nat -> R,
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l } ->
    Cauchy_crit_series An.
Proof. now intros An H; apply CV_Cauchy. Qed.

Lemma cv_cauchy_2 :
  forall An:nat -> R,
    Cauchy_crit_series An ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof. now intros An H%R_complete. Qed.

(* NEW *)
Lemma sum_cv_abs_cv :
  forall An, {l | infinite_sum (fun n => Rabs (An n)) l} ->
    {l | infinite_sum An l}.
Proof. now intros An H%cv_cauchy_1%cauchy_abs%cv_cauchy_2. Qed.

(** **** Series of non-negative terms *)

Lemma Rsum_nneg_growing : forall f, (forall n, 0 <= f n) -> Un_growing (Rsum f).
Proof.
  intros f Hf n.
  now rewrite Rsum_succ_r; apply Rge_le, Rplus_nneg_ge, Rle_ge.
Qed.

Lemma Rseries_nneg_bounded_cv :
  forall f, (forall n, 0 <= f n) -> has_ub (Rsum f) -> { l | Rseries_cv f l }.
Proof. now intros f H%Rsum_nneg_growing HA; apply growing_cv. Qed.

Lemma Rseries_nneg_cv_bounded :
  forall f, (forall n, 0 <= f n) ->
    (forall l, Rseries_cv f l -> forall n, Rsum f n <= l).
Proof. now intros f Hf%Rsum_nneg_growing l Hl; apply growing_ineq. Qed.

Lemma Rsum_abs_bounded_cv :
  forall f, has_ub (Rsum (fun n => Rabs (f n))) -> {l | Rseries_cv f l}.
Proof.
  now intros f [l Hl%Rseries_abs_cv]%Rseries_nneg_bounded_cv;
    [| now intros n; apply Rabs_pos].
Qed.

Lemma Rseries_cv_le_compat :
  forall f g l2, (forall n, 0 <= f n <= g n) ->
  Rseries_cv g l2 -> { l1 | Rseries_cv f l1 /\ l1 <= l2 }.
Proof.
  intros f g l2 Hfg Hg.
  assert (forall n, 0 <= g n) as g_nneg by
    now intros n; apply (Rle_trans _ (f n)); apply Hfg.
  pose proof (Rseries_nneg_cv_bounded g g_nneg l2 Hg) as Sgb.
  assert (H : forall n, Rsum f n <= Rsum g n) by now apply Rsum_le_compat_w, Hfg.
  assert ({l | Rseries_cv f l}) as [l Hl].
    apply Rseries_nneg_bounded_cv, has_ub_set_seq; [apply Hfg |]; exists l2.
    now intros n; apply Rle_trans with (1 := (H n)).
  now exists l; split; [easy |]; apply Un_cv_le_compat with (1 := H).
Qed.

Lemma has_ub_Rseries_shift :
  forall f N,
    has_ub (Rsum (fun i => f (N + i)%nat)) <-> has_ub (Rsum f).
Proof.
  intros f N; setoid_rewrite has_ub_set_seq; split; cycle 1.
  - intros [M HM]; exists (M - Rsum f N); intros n.
    now apply Rle_plus_chsd_lr; rewrite <-Rsum_add.
  - intros [M HM]; exists (Rsum (fun i => Rabs (f i)) N + Rabs M).
    intros n; destruct (Nat.le_ge_cases N n) as [I | I].
    + rewrite <-(Arith_prebase.le_plus_minus_r_stt N n), Rsum_add by easy.
      apply Rplus_le_compat.
      * now apply Rle_trans with (1 := Rle_abs _), Rsum_triangle.
      * now apply Rle_trans with (2 := Rle_abs _); apply HM.
    + apply Rle_trans with (1 := Rle_abs _).
      apply Rle_trans with (1 := Rsum_triangle _ _).
      apply Rle_trans with (2 := Rle_plus_nneg _ _ (Rabs_pos _)).
      apply Un_growing_le_compat; [| assumption].
      now apply Rsum_nneg_growing; intros k; apply Rabs_pos.
Qed.

Lemma has_ub_Rsum_le_compat :
  forall f g, (exists N, forall n, (n >= N)%nat -> f n <= g n) ->
  has_ub (Rsum g) -> has_ub (Rsum f).
Proof.
  intros An Bn [N HN]; setoid_rewrite <-(has_ub_Rseries_shift _ N).
  setoid_rewrite has_ub_set_seq; intros [M HM]; exists M; intros n.
  apply Rle_trans with (2 := (HM n)); apply Rsum_le_compat_w.
  now intros i; apply HN, Nat.le_add_r.
Qed.

Lemma sum_growing :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, An n <= Bn n) -> sum_f_R0 An N <= sum_f_R0 Bn N.
Proof. now intros An Bn N H; apply sum_Rle; intros n _. Qed.

(* NEW *)
Lemma sum_f_R0_nneg_ndecr :
  forall An, (forall n, 0 <= An n) -> Un_growing (sum_f_R0 An).
Proof.
  intros An HA; intros n; rewrite sum_f_R0_succ; apply Rge_le, Rplus_nneg_ge.
  now apply Rle_ge, HA.
Qed.

Lemma sum_incr :
  forall (An:nat -> R) (N:nat) (l:R),
    Un_cv (fun n:nat => sum_f_R0 An n) l ->
    (forall n:nat, 0 <= An n) -> sum_f_R0 An N <= l.
Proof.
  intros An N l cvA A_nneg; apply growing_ineq; [| assumption].
  now apply sum_f_R0_nneg_ndecr.
Qed.

(* NEW *)
Lemma sum_nneg_bounded_cv :
  forall An, (forall i, 0 <= An i) -> has_ub (sum_f_R0 An)
  -> { l | infinite_sum An l }.
Proof. now intros An An_nneg%sum_f_R0_nneg_ndecr HA; apply growing_cv. Qed.

(* NEW *)
Lemma sum_abs_bounded_cv :
  forall An, has_ub (fun N => (sum_f_R0 (fun n => Rabs (An n))) N) ->
    {l | infinite_sum An l}.
Proof.
  intros An HA; apply sum_cv_abs_cv, growing_cv; [| assumption].
  now apply sum_f_R0_nneg_ndecr; intros n; apply Rabs_pos.
Qed.

(* NEW *)
Lemma sum_le_compat_nneg :
  forall An Bn l2, (forall i, 0 <= An i <= Bn i) ->
  infinite_sum Bn l2 -> { l1 | infinite_sum An l1 /\ l1 <= l2 }.
Proof.
  intros f g l2 Hfg Hg%Rseries_cv_infinite_sum.
  pose proof (Rseries_cv_le_compat f g l2 Hfg Hg) as [l1 Hf].
  now exists l1; setoid_rewrite <-Rseries_cv_infinite_sum.
Qed.

(* NEW *)
Lemma has_ub_sum_f_from :
  forall An N,
    has_ub (sum_f_R0 (fun i => An (N + i)%nat)) <-> has_ub (sum_f_R0 An).
Proof.
  (* TODO: Still way too long *)
  intros f N; setoid_rewrite has_ub_set_seq; setoid_rewrite sum_f_R0_Rsum.
  split; intros [M HM].
  - assert (I : has_ub (Rsum (fun i => f (N + i)%nat))). {
      apply has_ub_set_seq; exists (Rabs M).
      intros [| n].
      + now rewrite Rsum_0; apply Rabs_pos.
      + now apply Rle_trans with (2 := Rle_abs _).
    }
    now apply (has_ub_Rseries_shift f N) in I as [M' HM']%has_ub_set_seq;
      exists M'.
  - assert (I : has_ub (Rsum f)). {
      apply has_ub_set_seq; exists (Rabs M); intros [| n].
      + now rewrite Rsum_0; apply Rabs_pos.
      + now apply Rle_trans with (2 := Rle_abs _).
    }
    apply (has_ub_Rseries_shift f N) in I as [M' HM']%has_ub_set_seq.
    now exists M'; intros n; apply HM'.
Qed.

(* NEW *)
Lemma has_ub_sum_le_compat :
  forall An Bn, (exists N, forall n, (n >= N)%nat -> An n <= Bn n) ->
  has_ub (sum_f_R0 Bn) -> has_ub (sum_f_R0 An).
Proof.
  intros An Bn [N HN]; setoid_rewrite <-(has_ub_sum_f_from _ N).
  setoid_rewrite has_ub_set_seq; intros [M HM]; exists M; intros n.
  apply Rle_trans with (2 := (HM n)); apply sum_Rle.
  now intros k _; apply HN, Nat.le_add_r.
Qed.

(* NEW, to replace sum_maj1
   TODO: The condition that Bn converges is superfluous, but how to state the
   lemma without it? *)
Lemma Rseries_dominated : forall An Bn lA lB,
  Rseries_cv An lA -> Rseries_cv Bn lB -> (forall n, Rabs (An n) <= Bn n) ->
  forall N, Rabs (lA - Rsum An N) <= lB - Rsum Bn N.
Proof.
  intros An Bn lA lB HA HB I N; apply Rabs_le_iff; split.
  - rewrite Ropp_minus_distr; apply Rle_minus_chsd_rl.
    rewrite Rplus_minus_assoc; apply Rle_plus_chsd_rr.
    rewrite <-Rsum_plus; apply growing_ineq.
    + apply Rsum_nneg_growing; intros n; apply Rle_minus_chsd_rl.
      now rewrite Rminus_0_l; apply (Rabs_le_iff (An n)).
    + apply Un_cv_eq_compat with (1 := Rsum_plus _ _).
      now apply CV_plus.
  - apply ->Rle_plus_chsd_lr; rewrite Rplus_minus_assoc, Rplus_minus_swap.
    apply Rle_plus_chsd_rr.
    rewrite <-Rsum_minus; apply growing_ineq.
    + apply Rsum_nneg_growing; intros n; apply Rle_plus_chsd_rr.
      now rewrite Rplus_0_l; apply Rabs_le_iff.
    + apply Un_cv_eq_compat with (1 := Rsum_minus _ _).
      now apply CV_minus.
Qed.

(** ** Alternated Series *)

(** *** Formalization of alternated series *)

(* TODO : add more appropriate name ? tg is probably the abbreviation of
   the french "terme général" *)
Definition tg_alt (Un:nat -> R) (i:nat) : R := (-1) ^ i * Un i.
Definition positivity_seq (Un:nat -> R) : Prop := forall n:nat, 0 <= Un n.
(* positivity_seq Un
   forall i, 0 <= Un i : almost same length, one more unfold... probably better
   not to use it *)

(* NEW *)
Lemma tg_alt_def : forall Un n, tg_alt Un n = (- 1) ^ n * Un n.
Proof. reflexivity. Qed.

(* NEW *)
Lemma tg_alt_odd : forall Un n, tg_alt Un (S (2 * n)) = - Un (S (2 * n)).
Proof. now intros Un n; rewrite tg_alt_def, pow_1_odd, Rmult_m1_l. Qed.

(* NEW *)
Lemma tg_alt_even : forall Un n, tg_alt Un (2 * n) = Un (2 * n)%nat.
Proof. now intros Un n; rewrite tg_alt_def, pow_1_even, Rmult_1_l. Qed.

(* CV_ALT_step[01] *)
Lemma alt_series_odd_even_mono : forall Un, Un_decreasing Un ->
  let Vn := (fun n => Rsum (tg_alt Un) (S (2 * n))) in
  let Wn := (fun n => Rsum (tg_alt Un) (2 * n)) in
  Un_decreasing Vn /\ Un_growing Wn.
Proof.
  intros Un Udec; split; intros n; rewrite Private_twice_succ.
  - rewrite 2(Rsum_succ_r _ (S _)), Rplus_assoc; apply Rle_plus_npos.
    rewrite <-Private_twice_succ, tg_alt_odd, tg_alt_even, Private_twice_succ.
    apply Rle_plus_chsd_ll; rewrite Rplus_0_r, Ropp_involutive; apply Udec.
  - rewrite 2(Rsum_succ_r), Rplus_assoc; apply Rle_plus_nneg.
    rewrite tg_alt_odd, tg_alt_even.
    now apply Rle_plus_chsd_rr; rewrite Rplus_0_l; apply Udec.
Qed.

(* CV_ALT_step[234] *)
Lemma alt_series_bounded : forall Un, Un_decreasing Un ->
  (forall i, 0 <= Un i) -> forall n, 0 <= Rsum (tg_alt Un) n <= (Un 0%nat).
Proof.
  intros Un Udec Unneg n; induction n as [| n IH].
  - now rewrite Rsum_0; split; [apply Rle_refl |].
  - pose proof (alt_series_odd_even_mono Un Udec) as [Vndec Wngro].
    destruct (Nat.EvenT_OddT_dec n) as [[m ->] | [m ->]].
    + split; [now rewrite Rsum_succ_r, tg_alt_even; apply Rplus_nneg_nneg |].
      rewrite <-(Nat.mul_0_r 2) at 2; rewrite <-tg_alt_even, <-Rplus_0_l.
      rewrite <-(Rsum_0 (tg_alt Un)), <-Rsum_succ_r.
      now apply (Un_decreasing_le_contravar (fun n => Rsum _ (S (2 * n))));
        [| apply Nat.le_0_l].
    + split; cycle 1.
      * apply Rle_trans with (2 := proj2 IH).
        rewrite Rsum_succ_r, Nat.add_1_r, tg_alt_odd.
        now apply Rplus_npos_le, Ropp_nneg.
      * rewrite <-(Rsum_0 (tg_alt Un)), <-(Nat.mul_0_r 2) at 1.
        rewrite Nat.add_1_r, <-Private_twice_succ.
        now apply (Un_growing_le_compat (fun n => Rsum _ (2 * n)));
        [| apply Nat.le_0_l].
Qed.

Lemma alt_series_odd_even_diff_cv_0 : forall Un, Un_cv Un 0 ->
  let Vn := (fun n => Rsum (tg_alt Un) (S (2 * n))) in
  let Wn := (fun n => Rsum (tg_alt Un) (2 * n)) in
  Un_cv (fun n => Vn n - Wn n) 0.
Proof.
  intros Un U0 Vn Wn; intros eps Heps; destruct (U0 eps Heps) as [N HN].
  exists N; intros n Hn; rewrite Rdist_0_r; unfold Vn, Wn.
  rewrite <-Nat.add_1_r, Rsum_add, Rplus_minus_l, Rsum_1, Nat.add_0_r.
  unfold tg_alt; rewrite pow_1_even, Rmult_1_l, <-Rdist_0_r.
  apply HN; rewrite <-(Nat.mul_1_l N); apply Nat.mul_le_mono; [| assumption].
  now apply Nat.le_succ_diag_r.
Qed.

Lemma alt_series_thm : forall Un, Un_decreasing Un -> Un_cv Un 0 ->
  {l | Un_cv (Rsum (tg_alt Un)) l}.
Proof.
  intros Un Udec U0.
  pose proof (alt_series_odd_even_mono Un Udec) as [Vn_dec Wn_gro].
  pose proof (alt_series_odd_even_diff_cv_0 Un U0) as diff0.
  pose proof (adjacent_sequences_thm _ _ Wn_gro Vn_dec diff0) as [l Hl].
  now exists l; apply Un_cv_odd_even.
Qed.

Lemma alt_series_ineq :
  forall Un l, Un_decreasing Un -> Un_cv (Rsum (tg_alt Un)) l ->
  forall i j, Rsum (tg_alt Un) (2 * i) <= l <= Rsum (tg_alt Un) (S (2 * j)).
Proof.
  intros Un l Udec [Wn_l Vn_l]%Un_cv_odd_even i j; split.
  - now apply growing_ineq with (2 := Wn_l); apply alt_series_odd_even_mono.
  - now apply decreasing_ineq with (2 := Vn_l); apply alt_series_odd_even_mono.
Qed.

Lemma alt_series_estimation : forall Un l, Un_decreasing Un ->
  Un_cv (Rsum (tg_alt Un)) l ->
  forall n, Rmin 0 (tg_alt Un n) <= l - (Rsum (tg_alt Un) n) <= Rmax 0 (tg_alt Un n).
Proof.
  intros Un l Udec U_l n; pose proof (alt_series_ineq Un l Udec U_l) as I.
  destruct (Nat.EvenT_OddT_dec n) as [[m ->] | [m ->]].
  - split.
    + apply Rle_trans with (1 := Rmin_l _ _), Rle_plus_chsd_rr.
      now rewrite Rplus_0_l; apply I.
    + apply Rle_trans with (2 := Rmax_r _ _), Rle_minus_chsd_rl.
      now rewrite <-Rsum_succ_r; apply I.
  - split.
    + apply Rle_trans with (1 := Rmin_r _ _), Rle_plus_chsd_lr.
      rewrite Nat.add_1_r, <-Rsum_succ_r, <-Private_twice_succ.
      now apply I.
    + apply Rle_trans with (2 := Rmax_l _ _), Rle_minus_chsd_rl.
      now rewrite Nat.add_1_r, Rplus_0_r; apply I.
Qed.

Lemma CV_ALT_step0 : forall Un, Un_decreasing Un ->
  Un_growing (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N))).
Proof.
  intros Un Udec n; rewrite 2sum_f_R0_Rsum, <-2Private_twice_succ.
  now apply alt_series_odd_even_mono.
Qed.

Lemma CV_ALT_step1 : forall Un, Un_decreasing Un ->
  Un_decreasing (fun N:nat => sum_f_R0 (tg_alt Un) (2 * N)).
Proof.
  now intros Un Udec n; rewrite 2sum_f_R0_Rsum; apply alt_series_odd_even_mono.
Qed.

Lemma CV_ALT_step3 : forall Un N, Un_decreasing Un -> positivity_seq Un ->
  sum_f_R0 (fun i:nat => tg_alt Un (S i)) N <= 0.
Proof.
  intros Un N Udec Unneg; rewrite sum_f_R0_Rsum.
  apply (Rplus_le_reg_l (Un 0%nat)); rewrite Rplus_0_r, <-(Nat.mul_0_r 2) at 1.
  now rewrite <-tg_alt_even, <-Rsum_succ_l; apply alt_series_bounded.
Qed.

Lemma CV_ALT_step2 : forall Un N, Un_decreasing Un -> positivity_seq Un ->
  sum_f_R0 (fun i:nat => tg_alt Un (S i)) (S (2 * N)) <= 0.
Proof. now intros Un N Udec Unneg; apply CV_ALT_step3. Qed.

Lemma CV_ALT_step4 : forall Un, Un_decreasing Un -> positivity_seq Un ->
  has_ub (fun N:nat => sum_f_R0 (tg_alt Un) (S (2 * N))).
Proof.
  intros Un Udec Upos; apply has_ub_set_seq; exists (Un 0%nat); intros n.
  now rewrite sum_f_R0_Rsum; apply alt_series_bounded.
Qed.

Theorem alternated_series : forall Un, Un_decreasing Un -> Un_cv Un 0 ->
  { l:R | Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l }.
Proof.
  intros Un Udec U0; pose proof (alt_series_thm Un Udec U0) as [l Hl].
  exists l. apply Un_cv_eq_compat with (1 := sum_f_R0_Rsum _).
  now apply CV_shift_succ'.
Qed.

Lemma CV_ALT : forall Un, Un_decreasing Un -> positivity_seq Un -> Un_cv Un 0 ->
  { l:R | Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l }.
Proof. now intros Un Udec _ U0; apply alternated_series. Qed.

Theorem alternated_series_ineq : forall Un l N, Un_decreasing Un ->
    Un_cv Un 0 -> Un_cv (fun N:nat => sum_f_R0 (tg_alt Un) N) l ->
    sum_f_R0 (tg_alt Un) (S (2 * N)) <= l <= sum_f_R0 (tg_alt Un) (2 * N).
Proof.
  intros Un l N Udec _ Hl.
  rewrite 2sum_f_R0_Rsum, <-Private_twice_succ; apply alt_series_ineq; [easy |].
  now apply CV_shift_succ, Un_cv_eq_compat with (1 := Rsum_sum_f_R0 _).
Qed.

(** **** Application: construction of PI *)

Definition PI_tg (n:nat) := / INR (2 * n + 1).

Lemma PI_tg_pos : forall n:nat, 0 <= PI_tg n.
Proof. now intros n; apply Rinv_nneg, pos_INR. Qed.

Lemma PI_tg_decreasing : Un_decreasing PI_tg.
Proof.
  intros n; apply Rinv_le_contravar, le_INR, Plus.plus_le_compat_r_stt.
    apply lt_0_INR; rewrite Nat.add_1_r; apply Nat.lt_0_succ.
  now apply Nat.mul_le_mono_l, Nat.le_succ_diag_r.
Qed.

Lemma PI_tg_cv : Un_cv PI_tg 0.
Proof.
  apply cv_infty_cv_0; intros M.
  destruct (INR_unbounded M) as [N HN]; exists N; intros n Hn.
  apply Rlt_trans with (1 := HN), lt_INR.
  rewrite Nat.add_1_r; apply Nat.lt_succ_r, Nat.le_trans with (1 := Hn).
  rewrite <-(Nat.mul_1_l n) at 1; apply Nat.mul_le_mono.
  - now apply Nat.le_succ_diag_r.
  - now apply Nat.le_refl.
Qed.

Lemma exist_PI :
  { l:R | Un_cv (fun N:nat => sum_f_R0 (tg_alt PI_tg) N) l }.
Proof.
  now apply alternated_series; [ apply PI_tg_decreasing | apply PI_tg_cv].
Qed.

(** Now, PI is defined *)
Definition Alt_PI : R := 4 * (let (a,_) := exist_PI in a).

(** We can get an approximation of PI with the following inequality *)
Lemma Alt_PI_ineq :
  forall N:nat,
    sum_f_R0 (tg_alt PI_tg) (S (2 * N)) <= Alt_PI / 4 <=
    sum_f_R0 (tg_alt PI_tg) (2 * N).
Proof.
  intro; apply alternated_series_ineq;
    [apply PI_tg_decreasing | apply PI_tg_cv |].
  unfold Alt_PI; destruct exist_PI as [l Hl].
  now rewrite Rmult_div_r; [| apply not_0_IZR].
Qed.

Lemma Alt_PI_RGT_0 : 0 < Alt_PI.
Proof.
  pose proof (Alt_PI_ineq 0) as [I%(Rmult_le_compat_l 4) _];
    [| now apply IZR_le].
  rewrite Rmult_div_assoc, Rmult_div_r in I by now apply not_0_IZR.
  apply Rlt_le_trans with (2 := I).
  rewrite Nat.mul_0_r, sum_f_R0_succ, sum_f_R0_0.
  apply Rmult_pos_pos; [now apply IZR_lt |].
  unfold tg_alt, PI_tg.
  rewrite <-(Nat.mul_0_r 2) at 1; rewrite pow_1_even, Rmult_1_l.
  rewrite <-(Nat.mul_0_r 2) at 4; rewrite pow_1_odd, Rmult_m1_l.
  rewrite <-Rminus_def; apply Rgt_minus, Rinv_0_lt_contravar, lt_INR.
    now apply lt_0_INR; rewrite Nat.mul_0_r, Nat.add_0_l; apply Nat.lt_0_1.
  apply Nat.add_lt_mono_r; rewrite Nat.mul_0_r, Nat.mul_1_r.
  now apply Nat.lt_0_2.
Qed.

(** ** Power Series *)

(* NEW *)
Lemma bound_quotient_iterated :
  forall f N q,
    (forall n, (n >= N)%nat -> f n <> 0 /\ (Rabs (f (S n) / f n) <= q))
    -> forall i, Rabs (f (N + i)%nat) <= Rabs (f N) * q ^ i.
Proof.
  intros f N q H; induction i as [| i IH].
  - now rewrite Nat.add_0_r, pow_0_r, Rmult_1_r; apply Rle_refl.
  - rewrite <-(Rmult_div_r (Rabs (f (N + i)%nat))) at 1 by
      now apply ->Rabs_neq_0; apply H, Nat.le_add_r.
    rewrite pow_succ, (Rmult_comm q), <-Rmult_assoc, <-Rmult_div_assoc.
    now apply Rmult_le_compat; [| apply Rdiv_nneg_nneg |..]; try apply Rabs_pos;
      [apply IH | rewrite <-Rabs_div, Nat.add_succ_r; apply H, Nat.le_add_r].
Qed.

Lemma geometric_sum : forall a q, q <> 1 ->
  forall n, Rsum (fun i => a * q ^ i) n = a * (1 - q ^ n) / (1 - q).
Proof.
  intros a q Hq n; induction n as [| n IH].
  - now rewrite Rsum_0, pow_0_r, Rminus_diag, Rmult_0_r, Rdiv_0_l.
  - rewrite Rsum_succ_r, IH, <-2Rmult_div_assoc, <-Rmult_plus_distr_l.
    apply Rmult_eq_compat_l, Req_mult_chsd_rr; [now apply Rminus_eq_contra |].
    rewrite Rmult_plus_distr_r, Rdiv_mult_id_l by now apply Rminus_eq_contra.
    rewrite Rmult_minus_distr_l, Rmult_1_r, Rmult_comm, <-pow_succ.
    now rewrite Rplus_minus_assoc, Rminus_plus_r.
Qed.

Lemma geometric_series :
  forall a q, - 1 < q < 1 -> Rseries_cv (fun n => a * q ^ n) (a / (1 - q)).
Proof.
  intros a q Hq.
  apply (Un_cv_eq_compat (fun n => (a / (1 - q) - (a / (1 - q)) * q ^ n))). {
    intros n; rewrite geometric_sum, <-Rmult_div_swap, (Rdiv_def a) by
      now apply Rlt_not_eq.
    rewrite <-!Rmult_div_assoc, <-Rmult_minus_distr_l; f_equal.
    now rewrite Rdiv_minus_distr, <-Rdiv_1_l.
  }
  rewrite <-Rminus_0_r; apply CV_minus; [apply const_seq_cv |].
  now rewrite <-(Rmult_0_r (a / (1 - q))); apply CV_scal_mult, cv_pow.
Qed.

(* NEW *)
Definition power_series (f : nat -> R) (x l : R) :=
  Rseries_cv (fun n => f n * x ^ n) l.

(* NEW *)
Theorem d'Alembert_ratio_test : forall f M,
  (exists N, forall n, ((n >= N)%nat -> f n <> 0 /\ Rabs (f (S n) / f n) <= M))
  -> (forall x, Rabs x < / M -> {l | power_series f x l}).
Proof.
  intros f M H x Hx; apply Rsum_abs_bounded_cv; destruct H as [N HN].
  assert (Mpos : M > 0) by now rewrite <-(Rinv_inv M);
    apply Rinv_pos, Rle_lt_trans with (2 := Hx), Rabs_pos.
  remember (Rabs (M * x)) as q eqn:q_def; assert (I : q < 1) by
    now rewrite q_def, Rabs_mult, Rabs_pos_id by easy; apply Rlt_mult_chsd_lr;
    [assumption |]; rewrite Rdiv_1_l.
  apply (has_ub_Rseries_shift _ N).
  apply (has_ub_Rsum_le_compat _ (fun n => Rabs (f N) * (Rabs x) ^ N * q ^ n)). {
    exists N; intros n Hn; rewrite q_def, pow_add, !Rabs_mult, Rpow_mult_distr.
    rewrite (Rabs_pos_id M) by easy; rewrite !RPow_abs, <-!Rmult_assoc.
    apply Rmult_le_compat_r; [now apply Rabs_pos |].
    rewrite Rmult_3perm_lrm; apply Rmult_le_compat_r; [now apply Rabs_pos |].
    now apply bound_quotient_iterated.
  }
  apply has_ub_set_seq; exists (Rabs (f N) * Rabs x ^ N / (1 - q)).
  intros n; apply growing_ineq, geometric_series.
  - apply Rsum_nneg_growing; intros k; apply Rmult_nneg_nneg.
    + rewrite RPow_abs; apply Rmult_nneg_nneg; apply Rabs_pos.
    + apply pow_le; rewrite q_def; apply Rabs_pos.
  - split; [| assumption]; rewrite q_def.
    now apply Rlt_le_trans with (2 := Rabs_pos _); apply IZR_lt.
Qed.

Theorem d'Alembert_infinite_radius : forall f,
  (forall n, f n <> 0) -> Un_cv (fun n => f (S n) / (f n)) 0
  -> forall x, {l | power_series f x l}.
Proof.
  intros f Hf HU x; apply (d'Alembert_ratio_test _ (/ (Rabs x + 1)));
    [| now rewrite Rinv_inv; apply Rplus_pos_gt, Rlt_0_1].
  destruct (HU (/ (Rabs x + 1))) as [N HN];
    [now apply Rinv_pos, Rplus_nneg_pos; [apply Rabs_pos | apply Rlt_0_1] |].
  exists N; intros n Hn; split; [now apply Hf |].
  now rewrite <-Rdist_0_r; left; apply HN.
Qed.

Theorem d'Alembert_finite_radius : forall f l,
  (forall n, f n <> 0) -> Un_cv (fun n => Rabs (f (S n) / (f n))) l
  -> forall x, Rabs x < / l -> {l | power_series f x l}.
Proof.
  intros f l Hf HU x Hx.
  apply (d'Alembert_ratio_test _ (/ ((Rabs x + / l) / 2))); cycle 1.
    now rewrite Rinv_inv; apply Rlt_half_plus.
  destruct (HU (/ ((Rabs x + / l) / 2) - l)) as [N HN].
    apply Rgt_minus; rewrite <-(Rinv_inv l) at 2; apply Rinv_0_lt_contravar;
    [apply Rdiv_pos_pos, Rlt_0_2 | now apply Rlt_half_plus].
    now apply Rplus_nneg_pos; [| apply Rle_lt_trans with (2 := Hx)];
      apply Rabs_pos.
  exists N; intros n Hn; split; [apply Hf |].
  now apply (Rminus_le_reg_r l), Rle_trans with (1 := Rle_abs _); left; apply HN.
Qed.

(* NEW, TODO Un_cv_ub_compat *)
Lemma Un_cv_lb_compat : forall Un m l,
  (exists N, forall n, (n >= N)%nat -> m <= Un n) -> Un_cv Un l
  -> m <= l.
Proof.
  intros Un m l [N HN] HU; apply Rle_plus_epsilon; intros eps Heps.
  destruct (HU eps Heps) as [N' HN'].
  specialize (HN (Nat.max N N') (Nat.le_max_l _ _)).
  specialize (HN' (Nat.max N N') (Nat.le_max_r _ _)).
  apply Rle_trans with (1 := HN); apply Rle_minus_chsd_rl.
  now apply Rle_trans with (1 := Rle_abs _); left; apply HN'.
Qed.

(* NEW, TODO move *)
Lemma Un_cv_0_abs_cv_0 : forall Un,
  Un_cv Un 0 <-> Un_cv (fun n => Rabs (Un n)) 0.
Proof.
  intros Un; split; intros H eps Heps; destruct (H eps Heps) as [N HN];
    exists N; intros n Hn; rewrite Rdist_0_r;
    [rewrite Rabs_Rabsolu | rewrite <-Rabs_Rabsolu]; rewrite <-Rdist_0_r;
    now apply HN.
Qed.

(* NEW *)
Lemma Rseries_cv_eq_compat : forall f g l, (forall n, f n = g n) ->
  Rseries_cv f l -> Rseries_cv g l.
Proof.
  now intros f g l H Hf; apply (Un_cv_eq_compat (Rsum f));
    [apply Rsum_eq_compat_w |].
Qed.

(* NEW *)
Theorem d'Alembert_ratio_cv : forall f l, (forall n, f n <> 0) ->
  Un_cv (fun n => Rabs (f (S n) / (f n))) l -> l < 1 -> {l' | Rseries_cv f l'}.
Proof.
  intros f l Hf HU Hl; assert (0 <= l) as Il' by
    now apply Un_cv_lb_compat with (2 := HU); exists 0%nat; intros n Hn;
    apply Rabs_pos.
  destruct (Rle_lt_or_eq_dec _ _ Il') as [I | E]; clear Il'; cycle 1.
  1: rewrite <-E in HU; apply Un_cv_0_abs_cv_0 in HU.
  1: pose proof (d'Alembert_infinite_radius f Hf HU 1) as [l' Hl'].
  2: apply Rinv_0_lt_contravar in Hl; [| assumption].
  2: rewrite Rinv_1, <-Rabs_1 in Hl.
  2: pose proof (d'Alembert_finite_radius f l Hf HU 1 Hl) as [l' Hl'].
  all: exists l'; apply Rseries_cv_eq_compat with (2 := Hl').
  all: now intros n; rewrite pow_1_l, Rmult_1_r.
Qed.

Definition Pser (An : nat -> R) (x l:R) : Prop :=
  infinite_sum (fun n:nat => An n * x ^ n) l.

Lemma Pser_power_series : forall f x l, Pser f x l <-> power_series f x l.
Proof. now intros f x l; split; intros H; apply Rseries_cv_infinite_sum. Qed.

Lemma geometric_infinite_sum :
  forall a q, - 1 < q < 1 -> infinite_sum (fun n => a * q ^ n) (a / (1 - q)).
Proof. now intros a q Hq; apply Rseries_cv_infinite_sum, geometric_series. Qed.

Theorem Alembert_C3 :
  forall (An:nat -> R) (x:R),
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    { l:R | Pser An x l }.
Proof.
  intros An x A_neq0 HA%Un_cv_0_abs_cv_0.
  pose proof (d'Alembert_infinite_radius An A_neq0 HA x) as [l Hl].
  now exists l; apply Pser_power_series.
Qed.

Lemma Alembert_C2 :
  forall An:nat -> R,
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros An A_neq0 HA; pose proof (Rlt_0_1) as I.
  pose proof (d'Alembert_ratio_cv An 0 A_neq0 HA I) as [l Hl].
  now exists l; apply Rseries_cv_infinite_sum.
Qed.

Lemma AlembertC3_step1 :
  forall (An:nat -> R) (x:R),
    x <> 0 ->
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    { l:R | Pser An x l }.
Proof. now intros An x _ A_neq0; apply Alembert_C3. Qed.

Lemma AlembertC3_step2 :
  forall (An:nat -> R) (x:R), x = 0 -> { l:R | Pser An x l }.
Proof.
  intros An x ->; exists (An 0%nat); intros eps Heps; exists 0%nat; intros n _.
  replace (sum_f_R0 (fun n0:nat => An n0 * 0 ^ n0) n) with (An 0%nat);
    [now rewrite Rdist_def, Rminus_diag, Rabs_0 |].
  induction n as [|n IH].
  - now rewrite sum_f_R0_0, pow_0_r, Rmult_1_r.
  - now rewrite sum_f_R0_succ, <-IH, pow_ne_zero, Rmult_0_r, Rplus_0_r.
Qed.

(** Convergence of power series in D(O,1/k)
    k=0 is described in Alembert_C3     *)
Lemma Alembert_C6 :
  forall (An:nat -> R) (x k:R),
    0 < k ->
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    Rabs x < / k -> { l:R | Pser An x l }.
Proof.
  intros An x k _ A_neq0 HA Hx.
  pose proof (d'Alembert_finite_radius An k A_neq0 HA x Hx) as [l Hl].
  now exists l; apply Pser_power_series, Hl.
Qed.

Lemma Alembert_C5 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    (forall n:nat, An n <> 0) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros An k [_ Hk] A_neq0 HU.
  pose proof (d'Alembert_ratio_cv An k A_neq0 HU Hk) as [l Hl].
  now exists l; apply Rseries_cv_infinite_sum.
Qed.

Lemma Cesaro_summation :
  forall f g l, Un_cv g l -> (forall n, 0 <= f n) -> cv_infty (Rsum f) ->
    Un_cv (fun n => Rsum (fun k => f k * g k) n / Rsum f n) l.
Proof.
  intros f g l Hg fpos Hf; intros eps Heps; unfold Rdist.
  assert (eps2_pos : eps / 2 > 0) by now apply Rdiv_pos_pos, IZR_lt.
  destruct (Hg _ eps2_pos) as [Ng HNg]; clear Hg.
  remember (fun i => (f i) * ((g i) - l)) as h eqn:h_def.
  destruct (Hf (Rabs (Rsum h Ng) / (eps / 2))) as [Nf HNf]; clear Hf.
  exists (Nat.max Nf Ng); intros n [n_ge_Nf n_ge_Ng]%Nat.max_lub_iff.
  specialize (HNf n n_ge_Nf); assert (sum_f_pos : Rsum f n > 0) by
    now apply Rle_lt_trans with (2 := HNf), Rdiv_nneg_nneg;
   [apply Rabs_pos | left].
  rewrite <-(Rmult_div_r (Rsum f n) l) by now apply Rgt_not_eq.
  rewrite <-Rsum_scal_r, <-Rdiv_minus_distr, <-Rsum_minus, (Rsum_eq_compat _ h)
    by now intros i _; rewrite h_def, Rmult_minus_distr_l.
  pose proof (Arith_prebase.le_plus_minus_r_stt _ _ n_ge_Ng) as n_Ng%eq_sym.
  rewrite n_Ng at 1; rewrite Rsum_add, Rdiv_plus_distr, <-(Rplus_half_diag eps).
  apply Rle_lt_trans with (1 := (Rabs_triangle _ _)).
  rewrite !Rabs_div, !(Rabs_pos_id (_ f _)) by assumption.
  apply Rplus_lt_le_compat; [now apply Rdiv_pos_lt_swap |].
  apply Rle_div_chsd_rl; [assumption |].
  rewrite n_Ng at 2; rewrite Rsum_add, Rplus_comm, Rmult_plus_distr_r.
  apply Rle_trans with (1 := Rsum_triangle _ _).
  rewrite <-2Rsum_scal_r, <-Rplus_0_r at 1; apply Rplus_le_compat.
  - apply Rsum_le_compat_w. intros i; rewrite h_def, Rabs_mult.
    rewrite (Rabs_nneg_id _ (fpos _)).
    apply Rmult_le_compat_l, Rlt_le, HNg, Nat.le_add_r; now apply fpos.
  - now apply Rsum_nneg_compat_w; intros i; apply Rmult_nneg_nneg, Rlt_le.
Qed.

(* NEW *)
Lemma INR_Rsum_ones : forall n, Rsum (fun _ => 1) n = INR n.
Proof.
  induction n as [| n IH].
  - now rewrite Rsum_0, INR_IZR_INZ.
  - now rewrite Rsum_succ_r, IH, <-S_INR.
Qed.

(* NEW *)
Lemma cv_infty_eq_compat : forall Un Vn, (forall n, Vn n = Un n) ->
  cv_infty Un -> cv_infty Vn.
Proof.
  intros Un Vn H HU A; destruct (HU A) as [N HN]; exists N; intros n Hn.
  now rewrite H; apply HN.
Qed.

Lemma Cesaro_arithmetic_mean : forall f l, Un_cv f l ->
  Un_cv (fun n => Rsum f n / INR n) l.
Proof.
  intros f l HU. apply (Un_cv_eq_compat
    (fun n => (Rsum (fun i => ((fun _ => 1) i * f i)) n) / Rsum (fun _ => 1) n)).
  - intros n; rewrite INR_Rsum_ones; apply Rdiv_eq_compat_r, Rsum_eq_compat_w.
      now intros i; rewrite Rmult_1_l.
  - apply Cesaro_summation; [assumption | intros; apply Rle_0_1 |].
    apply (cv_infty_eq_compat INR), INR_cv_infty. now apply INR_Rsum_ones.
Qed.

(** ** Miscellaneous *)

(** *** Rsigma *)

(* from https://stackoverflow.com/questions/43849824/coq-rewriting-using-lambda-arguments *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Generalizable All Variables.

Instance subrel_eq_respect {A B : Type} `(sa : subrelation A RA eq)
`(sb : subrelation B eq RB) :
   subrelation eq (respectful RA RB).
Proof. intros. intros f g Hfg. subst. intros a a' Raa'. apply sb.
f_equal. apply (sa _ _ Raa'). Qed.

Instance pointwise_eq_ext {A B : Type} `(sb : subrelation B RB eq)
  : subrelation (pointwise_relation A RB) eq.
Proof. intros f g Hfg. apply functional_extensionality. intro x; apply sb, (Hfg x). Qed.
(*
Lemma lol : exists n, (n + 1 = S n)%nat.
Proof.
  (* rewrite under exists LOL *)
  setoid_rewrite Nat.add_1_r.
  now exists 0.
Qed.

Lemma rofl : forall n, (n + 1 = S n)%nat.
Proof.
  (* rewrite under forall ROFL *)
  now setoid_rewrite Nat.add_1_r.
Qed.

Lemma plop : forall n : nat, (fun n => n + 1) = (fun n => S n).
Proof.
  (* rewrite under fun ! *)
  now setoid_rewrite Nat.add_1_r.
Qed.
*)
(*
Set Implicit Arguments.

Section Sigma.

  Variable f : nat -> R.

  Definition sigma (low high:nat) : R :=
    sum_f_R0 (fun k:nat => f (low + k)) (high - low).

  Theorem sigma_split :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high = sigma low k + sigma (S k) high.
  Proof.
    intros low high k low_le_k k_lt_high; induction low_le_k as [| k I IH].
    - unfold sigma; rewrite Nat.sub_diag, sum_f_R0_0, Nat.sub_succ_r.
      setoid_rewrite Nat.add_succ_comm. (* KILLING FEATURE *)
      now rewrite <-(decomp_sum (fun k => f (low + k))) by
        now apply Nat.lt_add_lt_sub_l; rewrite Nat.add_0_r.
    - rewrite IH by
        now apply Nat.lt_trans with (2 := k_lt_high), Nat.lt_succ_diag_r.
      unfold sigma.
      rewrite Nat.sub_succ_l by assumption; rewrite sum_f_R0_succ.
      rewrite Rplus_assoc; f_equal.
      rewrite (Nat.sub_succ_r _ (S k)).
      setoid_rewrite (Nat.add_succ_comm (S k) _).
      rewrite Nat.add_succ_r, Arith_prebase.le_plus_minus_r_stt by assumption.
      rewrite <-(Nat.add_0_r (S k)) at 2.
      now rewrite <-(decomp_sum (fun i => f ((S k) + i))) by
        now apply Nat.lt_add_lt_sub_l; rewrite Nat.add_0_r.
  Qed.

  Theorem sigma_diff :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high - sigma low k = sigma (S k) high.
  Proof. now intros low high k Hl Hk; apply Req_minus_chsd_rl, sigma_split. Qed.

  Theorem sigma_diff_neg :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low k - sigma low high = - sigma (S k) high.
  Proof.
    intros low high k H1 H2; rewrite (sigma_split H1 H2); ring.
  Qed.

  Theorem sigma_first :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f low + sigma (S low) high.
  Proof.
    intros low high H; unfold sigma; rewrite decomp_sum by
      now apply Nat.lt_add_lt_sub_l; rewrite Nat.add_0_r.
    rewrite Nat.add_0_r; f_equal; rewrite Nat.sub_succ_r.
    now setoid_rewrite Nat.add_succ_comm.
  Qed.

  Theorem sigma_last :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f high + sigma low (pred high).
  Proof.
    intros low high H1; unfold sigma.
    rewrite <-(Nat.succ_pred (high - low)), sum_f_R0_succ
      by now apply Nat.sub_gt.
    rewrite Rplus_comm, Nat.succ_pred_pos by
      now apply Nat.lt_add_lt_sub_l; rewrite Nat.add_0_r.
    now rewrite Arith_prebase.le_plus_minus_r_stt, Private_sub_pred_l
      by now apply Nat.lt_le_incl.
  Qed.

  Theorem sigma_eq_arg : forall low:nat, sigma low low = f low.
  Proof.
    now intros low; unfold sigma; rewrite Nat.sub_diag, sum_f_R0_0, Nat.add_0_r.
  Qed.

End Sigma.
*)
(** *** Rprod *)

(* NEW: a better prod, TODO: add missing lemmas and document *)

(** **** Rprod f n = (f 0) * (f 1) * ... * (f (n - 1)), a simple finite product *)

Fixpoint Rprod (f : nat -> R) (n : nat) :=
  match n with
  | 0%nat => 1
  | (S n) => Rprod f n * (f n)
  end.

Lemma Rprod_0 : forall f, Rprod f 0%nat = 1.
Proof. reflexivity. Qed.

Lemma Rprod_succ_r : forall f n, Rprod f (S n) = Rprod f n * f n.
Proof. reflexivity. Qed.

Lemma Rprod_1 : forall f, Rprod f 1 = f 0%nat.
Proof. now intros f; rewrite Rprod_succ_r, Rprod_0, Rmult_1_l. Qed.

Lemma Rprod_succ_l : forall f n,
  Rprod f (S n) = f 0%nat * Rprod (fun i => f (S i)) n.
Proof.
  induction n as [| n IH].
  - now rewrite Rprod_1, Rprod_0, Rmult_1_r.
  - now rewrite Rprod_succ_r, IH at 1; rewrite Rprod_succ_r, Rmult_assoc.
Qed.

Lemma Rprod_add : forall f n m,
  Rprod f (n + m) = Rprod f n * Rprod (fun i => f (n + i)%nat) m.
Proof.
  intros f n m; induction m as [| m IH].
  - now rewrite Nat.add_0_r, Rprod_0, Rmult_1_r.
  - now rewrite Nat.add_succ_r, Rprod_succ_r, IH, Rprod_succ_r, Rmult_assoc.
Qed.

Lemma Rprod_eq_compat : forall f g n,
  (forall i, (i < n)%nat -> f i = g i) -> Rprod f n = Rprod g n.
Proof.
  intros f g n; induction n as [| n IH].
  - now intros _; rewrite 2Rprod_0.
  - intros H; rewrite 2Rprod_succ_r, H by now apply Nat.lt_succ_diag_r.
    now rewrite IH by now intros i Hi; apply H, Nat.lt_lt_succ_r.
Qed.

Lemma Rprod_eq_compat_w : forall f g,
  (forall i, f i = g i) -> forall n, Rprod f n = Rprod g n.
Proof. now intros f g H; intros n; apply Rprod_eq_compat; intros i _. Qed.

Lemma Rprod_nneg_compat : forall f n,
  (forall i, (i < n)%nat -> 0 <= f i) -> 0 <= Rprod f n.
Proof.
  intros f n; induction n as [| n IH].
  - now intros _; rewrite Rprod_0; apply Rle_0_1.
  - intros Hf; rewrite Rprod_succ_r; apply Rmult_nneg_nneg.
    + now apply IH; intros i Hi; apply Hf, Nat.lt_lt_succ_r.
    + now apply Hf, Nat.lt_succ_diag_r.
Qed.

Lemma Rprod_nneg_compat_w :
  forall f, (forall i, 0 <= f i) -> forall n, 0 <= Rprod f n.
Proof.
  intros f Hf n; induction n as [| n IH].
  - now rewrite Rprod_0; apply Rle_0_1.
  - now rewrite Rprod_succ_r; apply Rmult_nneg_nneg.
Qed.

Lemma Rprod_nneg_le_compat :
  forall f g n, (forall i, (i < n)%nat -> 0 <= f i <= g i) ->
    0 <= Rprod f n <= Rprod g n.
Proof.
  intros f g n; induction n as [| n IH].
  - now intros _; rewrite 2Rprod_0; split; [apply Rle_0_1 | apply Rle_refl].
  - intros Hfg; split; [now apply Rprod_nneg_compat, Hfg |].
    rewrite 2Rprod_succ_r; apply Rmult_le_compat.
    + now apply IH; intros i Hi; apply Hfg, Nat.lt_lt_succ_r.
    + now apply Hfg, Nat.lt_succ_diag_r.
    + now apply IH; intros i Hi; apply Hfg, Nat.lt_lt_succ_r.
    + now apply Hfg, Nat.lt_succ_diag_r.
Qed.

Lemma Rprod_nneg_le_compat_w :
  forall f g, (forall i, 0 <= f i <= g i) ->
    forall n, 0 <= Rprod f n <= Rprod g n.
Proof. now intros f g H n; apply Rprod_nneg_le_compat; intros i _. Qed.

(** **** Application to factorial and binomial coefficients *)

Lemma fact_Rprod :
  forall n, INR (fact n) = Rprod (fun i => INR (S i)) n.
Proof.
  intros n; induction n as [| n IH].
  - now rewrite fact_0, Rprod_0, INR_1.
  - now rewrite fact_succ, mult_INR, Rmult_comm, Rprod_succ_r, IH.
Qed.

Lemma RfactN_fact2N_factk :
  forall N k:nat,
    (k <= 2 * N)%nat ->
      (INR (fact N))² <= INR (fact (2 * N - k)) * INR (fact k).
Proof.
  intros N.
  enough (suff : forall k, (k <= N)%nat ->
    (INR (fact N))² <= INR (fact (2 * N - k)) * INR (fact k)). {
    intros k Hk; destruct (Nat.le_ge_cases k N) as [I | I]; [now apply suff |].
    rewrite Rsqr_def, (Rmult_comm _ (INR (fact k))).
    replace k with (2 * N - (2 * N - k))%nat by now rewrite Private_sub_sub_id_r.
    rewrite Private_sub_sub_id_r at 2 by easy; apply suff.
    rewrite <-Nat.double_twice; unfold Nat.double.
    now apply Nat.le_sub_le_add_l, Nat.add_le_mono_r.
  }
  intros k Hk. rewrite Rsqr_def, !fact_Rprod.
  rewrite <-Nat.double_twice; unfold Nat.double; rewrite <-Nat.add_sub_assoc
    by assumption.
  rewrite Rprod_add, Rmult_assoc; apply Rmult_le_compat_l.
    apply Rprod_nneg_compat_w; intros i; apply pos_INR.
  rewrite <-(Nat.sub_add k N) at 1 by assumption; rewrite Nat.add_comm.
  rewrite Rprod_add, Rmult_comm; apply Rmult_le_compat_r.
    apply Rprod_nneg_compat_w; intros i; apply pos_INR.
  apply Rprod_nneg_le_compat_w; intros i; split ; [apply pos_INR |].
  now apply le_INR; apply ->Nat.succ_le_mono; apply Nat.add_le_mono_r.
Qed.

Lemma C_maj : forall N k:nat, (k <= 2 * N)%nat -> C (2 * N) k <= C (2 * N) N.
Proof.
  intros N k Hk; unfold C; apply Rdiv_nneg_le_contravar_l; [now apply pos_INR |].
  split; [now apply Rmult_pos_pos; apply INR_fact_lt_0 |].
  rewrite <-Nat.double_twice at 1; unfold Nat.double; rewrite Nat.add_sub.
  now rewrite <-Rsqr_def, Rmult_comm; apply RfactN_fact2N_factk.
Qed.

(** **** Legacy part with prod_f_R0 f N = (f 0) + (f 1) + ... + (f N) *)
(* Notice that prod_f_R0 = f 0, there is no empty product. *)

Fixpoint prod_f_R0 (f:nat -> R) (N:nat) : R :=
  match N with
    | O => f O
    | S p => prod_f_R0 f p * f (S p)
  end.

Lemma prod_f_R0_Rprod : forall f n, prod_f_R0 f n = Rprod f (S n).
Proof.
  intros f n; induction n as [| n IH].
  - now simpl prod_f_R0; rewrite Rprod_1.
  - now simpl prod_f_R0; rewrite Rprod_succ_r, IH.
Qed.

Lemma prod_SO_split :
  forall (An:nat -> R) (n k:nat),
    (k < n)%nat ->
    prod_f_R0 An n =
    prod_f_R0 An k * prod_f_R0 (fun l:nat => An (k +1+l)%nat) (n - k -1).
Proof.
  intros f n k Hk; rewrite !prod_f_R0_Rprod.
  rewrite <-(Arith_prebase.le_plus_minus_r_stt (S k) (S n)) by
    now apply ->Nat.succ_le_mono; apply Nat.lt_le_incl.
  rewrite Rprod_add; f_equal.
  now rewrite <-Nat.sub_add_distr, Nat.add_1_r, Nat.sub_succ_l by
    now apply Nat.le_succ_l.
Qed.

Lemma prod_SO_pos :
  forall (An:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> 0 <= An n) -> 0 <= prod_f_R0 An N.
Proof.
  intros f n Hf; rewrite prod_f_R0_Rprod; apply Rprod_nneg_compat.
  now intros i Hi; apply Hf, Nat.succ_le_mono.
Qed.

Lemma prod_SO_Rle :
  forall (An Bn:nat -> R) (N:nat),
    (forall n:nat, (n <= N)%nat -> 0 <= An n <= Bn n) ->
    prod_f_R0 An N <= prod_f_R0 Bn N.
Proof.
  intros f g n Hfg; rewrite !prod_f_R0_Rprod; apply Rprod_nneg_le_compat.
  now intros i Hi; apply Hfg, Nat.succ_le_mono.
Qed.

Lemma fact_prodSO :
  forall n:nat, INR (fact n) = prod_f_R0 (fun k:nat =>
     (match (eq_nat_dec k 0) with
          | left   _ => 1%R
          | right _ => INR k
                        end)) n.
Proof.
  intros n; rewrite prod_f_R0_Rprod, fact_Rprod, Rprod_succ_l.
  now rewrite Rmult_1_l; apply Rprod_eq_compat_w; intros i.
Qed.

(* Compatibility *)
Notation prod_f_SO := (fun An N => prod_f_R0 (fun n => An (S n)) N).

(* REMAINS *)

Lemma GP_infinite :
  forall x:R, Rabs x < 1 -> Pser (fun n:nat => 1) x (/ (1 - x)).
Proof.
  intros x Hx; intros eps Heps.
  assert (fact0 : x - 1 <> 0) by now apply Rminus_eq_contra;
    intros contra; rewrite contra, Rabs_1 in Hx; apply Rlt_irrefl in Hx.
  assert (fact1 : Rabs (x - 1) > 0) by now apply Rabs_pos_lt.
  destruct (pow_lt_1_zero x Hx (eps * Rabs (x - 1))) as [N HN].
    now apply Rmult_pos_pos.
  exists N; intros n Hn.
  replace (fun n0 : nat => 1 * x ^ n0) with (fun n0 : nat => x ^ n0) by
    now apply FunctionalExtensionality.functional_extensionality_dep;
    intros k; rewrite Rmult_1_l.
  apply (Rmult_lt_reg_l (Rabs (x - 1))); [assumption |].
  rewrite <-Rdist_mult_l, Rmult_comm, GP_finite, <-(Ropp_minus_distr x 1).
  rewrite Rinv_opp, <-Ropp_mult_distr_r, <-Rdiv_def, Rdiv_diag by easy.
  rewrite Rdist_def, Rminus_opp_r, Rminus_plus_r, Rmult_comm; apply HN.
  now rewrite Nat.add_1_r; apply Nat.le_trans with (1 := Hn);
    apply Nat.le_succ_diag_r.
Qed.

(* TODO: rename and why < and <= ? *)
Lemma tech4 :
  forall (An:nat -> R) (k:R) (N:nat),
    0 <= k -> (forall i:nat, An (S i) < k * An i) -> An N <= An 0%nat * k ^ N.
Proof.
  intros An k N Hk HA; induction  N as [| N HrecN].
  - now rewrite pow_0_r, Rmult_1_r; apply Rle_refl.
  - apply (Rle_trans _ (k * (An N))); [left; apply HA |].
    rewrite pow_succ, <-Rmult_assoc, Rmult_3perm_mlr, Rmult_assoc.
    now apply Rmult_le_compat_l.
Qed.

Lemma tech6 :
  forall (An:nat -> R) (k:R) (N:nat),
    0 <= k ->
    (forall i:nat, An (S i) < k * An i) ->
    sum_f_R0 An N <= An 0%nat * sum_f_R0 (fun i:nat => k ^ i) N.
Proof.
  intros An k N Hk HA; induction N as [| N HrecN].
  - now rewrite 2sum_f_R0_0, pow_0_r, Rmult_1_r; apply Rle_refl.
  - rewrite 2sum_f_R0_succ; apply (Rplus_le_compat_r (An (S N))) in HrecN.
    apply Rle_trans with (1 := HrecN).
    now rewrite Rmult_plus_distr_l; apply Rplus_le_compat_l, tech4.
Qed.

Definition SP (fn:nat -> R -> R) (N:nat) (x:R) : R :=
  sum_f_R0 (fun k:nat => fn k x) N.

Lemma tech12 :
  forall (An:nat -> R) (x l:R),
    Un_cv (fun N:nat => sum_f_R0 (fun i:nat => An i * x ^ i) N) l ->
    Pser An x l.
Proof. now intros An x l HAl. Qed.

(* TODO: deprecate, the inequality is nice and useful but it does not depend
   on the fact that we have a series of functions *)
Lemma sum_maj1 :
  forall (fn:nat -> R -> R) (An:nat -> R) (x l1 l2:R) (N:nat),
    Un_cv (fun n:nat => SP fn n x) l1 ->
    Un_cv (fun n:nat => sum_f_R0 An n) l2 ->
    (forall n:nat, Rabs (fn n x) <= An n) ->
    Rabs (l1 - SP fn N x) <= l2 - sum_f_R0 An N.
Proof.
  intros fn An x l1 l2 N Hf HA I.
  unfold SP; rewrite 2sum_f_R0_Rsum; generalize (S N); clear N; intros N.
  apply Rseries_dominated.
  - now apply Rseries_cv_infinite_sum, infinite_sum_Un_cv, Hf.
  - now apply Rseries_cv_infinite_sum, infinite_sum_Un_cv, HA.
  - assumption.
Qed.

(** Comparaison of convergence for series *)
Lemma Rseries_CV_comp :
  forall An Bn:nat -> R,
    (forall n:nat, 0 <= An n <= Bn n) ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 Bn N) l } ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros An Bn I [l Hbl].
  pose proof (sum_le_compat_nneg An Bn l I Hbl) as [l' [Hal' _]].
  now exists l'.
Qed.

(** Cesaro's theorem *)
Lemma Cesaro :
  forall (An Bn:nat -> R) (l:R),
    Un_cv Bn l ->
    (forall n:nat, 0 < An n) ->
    cv_infty (fun n:nat => sum_f_R0 An n) ->
    Un_cv (fun n:nat => sum_f_R0 (fun k => An k * Bn k) n / sum_f_R0 An n) l.
Proof.
  intros An Bn l B_cv A_gt0 sumA_dv.
  apply (cv_infty_eq_compat _ _ (Rsum_sum_f_R0 _)) in sumA_dv.
  remember (fun i => Rsum (fun k => An k * Bn k) i / Rsum An i) as h eqn:h_def.
  apply (Un_cv_eq_compat (fun n => h (S n)));
    [now intros n; rewrite 2sum_f_R0_Rsum, h_def |].
  apply CV_shift_succ'; rewrite h_def; apply Cesaro_summation;
    [assumption | now intros n; left |].
  intros A; destruct (sumA_dv A) as [N HN]; exists (S N); intros [| n] Hn.
  - now apply Nat.nle_succ_0 in Hn.
  - now apply HN, Nat.succ_le_mono.
Qed.

(* NEW ?? *)
Lemma INR_sum_ones : forall n, sum_f_R0 (fun _ => 1) n = INR (S n).
Proof.
  induction n as [| n IH].
  - now rewrite sum_f_R0_0; rewrite INR_IZR_INZ.
  - now rewrite sum_f_R0_succ, IH, <-S_INR.
Qed.

Lemma Cesaro_1 :
  forall (An:nat -> R) (l:R),
    Un_cv An l -> Un_cv (fun n:nat => sum_f_R0 An (pred n) / INR n) l.
Proof.
  intros Bn l H; apply (CV_shift _ 1).
  apply (Un_cv_eq_compat
    (fun n => sum_f_R0 (fun i => 1 * Bn i) n / sum_f_R0 (fun _ => 1) n)).
    intros n; rewrite INR_sum_ones, Nat.add_1_r; apply Rdiv_eq_compat_r.
    now apply sum_eq; intros i _; rewrite Rmult_1_l.
  apply Cesaro; [easy | now intros _; apply Rlt_0_1 |].
  intros M; destruct (INR_cv_infty M) as [N HN]; exists N; intros n Hn.
  now rewrite INR_sum_ones; apply HN, Nat.le_le_succ_r.
Qed.

(* CANDIDATES for deprecation *)

Lemma not_Rlt : forall r1 r2:R, ~ r1 < r2 -> r1 >= r2.
Proof. exact Rnot_lt_ge. Qed.

Lemma tech13 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    exists k0 : R,
      k < k0 < 1 /\
      (exists N : nat,
        (forall n:nat, (N <= n)%nat -> Rabs (An (S n) / An n) < k0)).
Proof.
  intros An k [_ [k0 [H1 H2]]%Rexists_between] HA; exists k0; split.
    split; assumption.
  assert (fact: k0 - k > 0) by now apply Rgt_minus.
  destruct (HA _ fact) as [N HN]; exists N; intros n Hn.
  apply (Rminus_lt_reg_r k).
  now apply Rle_lt_trans with (1 := Rle_abs _); apply HN.
Qed.

Lemma tech5 :
  forall (An:nat -> R) (N:nat), sum_f_R0 An (S N) = sum_f_R0 An N + An (S N).
Proof. exact sum_f_R0_succ. Qed.

Lemma Rsum_abs :
  forall (An:nat -> R) (N:nat),
    Rabs (sum_f_R0 An N) <= sum_f_R0 (fun l:nat => Rabs (An l)) N.
Proof. exact sum_f_R0_triangle. Qed.

Lemma sum_cv_maj :
  forall (An:nat -> R) (fn:nat -> R -> R) (x l1 l2:R),
    Un_cv (fun n:nat => SP fn n x) l1 ->
    Un_cv (fun n:nat => sum_f_R0 An n) l2 ->
    (forall n:nat, Rabs (fn n x) <= An n) -> Rabs l1 <= l2.
Proof.
  intros An fn x l1 l2 H1%cv_cvabs H2 I.
  assert ({l | infinite_sum (fun n => Rabs (fn n x)) l /\ l <= l2})
    as [l [Hl Il]] by
    now apply (sum_le_compat_nneg _ An); [| assumption]; intros i; split;
      [apply Rabs_pos |].
  apply Rle_trans with (2 := Il).
  apply Un_cv_le_compat with (3 := Hl) (2 := H1).
  now apply sum_f_R0_triangle.
Qed.

Lemma tech11 :
  forall (An Bn Cn:nat -> R) (N:nat),
    (forall i:nat, An i = Bn i - Cn i) ->
    sum_f_R0 An N = sum_f_R0 Bn N - sum_f_R0 Cn N.
Proof.
  intros An Bn Cn; unfold Rminus; intros N H.
  rewrite (sum_eq An (fun n => Bn n + - Cn n)) by now intros i _; apply H.
  now rewrite plus_sum, sum_f_R0_opp.
Qed.

Lemma Rabs_triang_gen :
  forall (An:nat -> R) (N:nat),
    Rabs (sum_f_R0 An N) <= sum_f_R0 (fun i:nat => Rabs (An i)) N.
Proof. exact sum_f_R0_triangle. Qed.

Lemma sum_plus :
  forall (An Bn:nat -> R) (N:nat),
    sum_f_R0 (fun l:nat => An l + Bn l) N = sum_f_R0 An N + sum_f_R0 Bn N.
Proof. exact plus_sum. Qed.

Lemma Alembert_C4 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    (forall n:nat, 0 < An n) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros An k Hk Apos.
  assert (A_neq0 : forall n, An n <> 0) by now intros n; apply Rgt_not_eq, Apos.
  now apply Alembert_C5.
Qed.

Lemma Alembert_C1 :
  forall An:nat -> R,
    (forall n:nat, 0 < An n) ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) 0 ->
    { l:R | Un_cv (fun N:nat => sum_f_R0 An N) l }.
Proof.
  intros An A_gt_0 HA.
  assert (A_neq0 : forall n, An n <> 0) by
    now intros n; apply not_eq_sym, Rlt_not_eq, A_gt_0.
  now apply Alembert_C2.
Qed.

Lemma Alembert_C2_aux_positivity :
  forall Xn : nat -> R,
    let Yn i := (2 * Rabs (Xn i) + Xn i) / 2 in
    (forall n, Xn n <> 0) ->
    forall n, 0 < Yn n.
Proof.
  intros Xn Yn Hx n; unfold Yn; apply Rdiv_pos_pos; [| apply Rlt_0_2].
  apply Rgt_plus_chsd_rr; rewrite Rminus_0_l, <-Rplus_diag.
  apply (Rge_gt_trans _ (Rabs (Xn n) + - (Xn n))).
  + now apply Rplus_ge_compat_l, Rle_ge; rewrite <-Rabs_Ropp; apply Rle_abs.
  + now rewrite Rplus_comm; apply Rplus_pos_gt, Rabs_pos_lt.
Qed.

Lemma Alembert_C2_aux_Un_cv :
  forall Xn : nat -> R,
    let Yn i := (2 * Rabs (Xn i) + Xn i) / 2 in
    (forall n, Xn n <> 0) ->
    Un_cv (fun n:nat => Rabs (Xn (S n) / Xn n)) 0 ->
    Un_cv (fun n => Rabs (Yn (S n) / Yn n)) 0.
Proof.
  intros Xn Yn X_neq0 HX; unfold Yn; intros eps Heps.
  assert (forall n, (0 < 2 * Rabs (Xn n) + Xn n)) as pos by
    now intros n; apply (Rdiv_lt_reg_r 2); [apply Rlt_0_2 |];
      now rewrite Rdiv_0_l; apply Alembert_C2_aux_positivity.
  destruct (HX (eps / 3)) as [N HN].
    now apply Rdiv_pos_pos; [| apply IZR_lt].
  exists N; intros n Hn; rewrite 2(Rdiv_def _ 2), Rdiv_mult_r_r by
    now apply Rinv_neq_0_compat, Rgt_not_eq, Rlt_0_2.
  rewrite Rdist_0_r, Rabs_nneg_id by now apply Rabs_pos.
  rewrite Rabs_nneg_id by now apply Rdiv_nneg_nneg; left.
  assert (I : 2 * Rabs (Xn (S n)) + Xn (S n) <= 3 * Rabs (Xn (S n))). {
    replace 3 with (2 + 1) by now rewrite <-plus_IZR.
    rewrite Rmult_plus_distr_r, Rmult_1_l; apply Rplus_le_compat_l.
    now apply Rle_abs.
  }
  assert (J : Rabs (Xn n) <= 2 * Rabs (Xn n) + Xn n). {
    rewrite <-Rplus_diag; apply Rge_le; rewrite Rplus_assoc; apply Rplus_nneg_ge.
    now apply Rge_plus_chsd_rr; rewrite Rminus_0_l, <-Rabs_Ropp;
      apply Rle_ge, Rle_abs.
  }
  rewrite Rdiv_def; apply Rinv_le_contravar in J; [| now apply Rabs_pos_lt].
  apply (Rle_lt_trans _ ((3 * Rabs (Xn (S n))) * / (Rabs (Xn n)))).
    apply Rmult_le_compat;
      [now left | now left; apply Rinv_pos, pos | easy | easy].
  rewrite Rmult_assoc; apply Rlt_mult_chsd_lr; [now apply IZR_lt |].
  rewrite <-Rdiv_def.
  specialize (HN n Hn); rewrite Rdist_0_r, Rabs_nneg_id in HN
    by now apply Rabs_pos.
  now rewrite <-Rabs_div; apply HN.
Qed.

(* Compatibility *)

Notation maj_sup := ub_to_lub (only parsing).
Notation min_inf := lb_to_glb (only parsing).
Notation majorant := lub (only parsing).
Notation minorant := glb (only parsing).
Notation sequence_majorant := sequence_ub (only parsing).
Notation sequence_minorant := sequence_lb (only parsing).

Lemma cv_infty_cv_R0_depr :
  forall Un:nat -> R,
    (forall n:nat, Un n <> 0) -> cv_infty Un -> Un_cv (fun n:nat => / Un n) 0.
Proof. now intros Un _; apply cv_infty_cv_0. Qed.
#[deprecated(since="8.16",note="Use cv_infty_cv_0.")]
Notation cv_infty_cv_R0 := cv_infty_cv_R0_depr.

(* TODO #14736 for compatibility only, should be removed after deprecation *)
Require Import Max.
