(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import BinNat.

Attributes deprecated(since="8.19", note="Require BinNat instead.").
(** Obsolete file, see [BinNat] now,
    only compatibility notations remain here. *)

Notation Nsqrt_spec := (fun n => N.sqrt_spec n (N.le_0_l n)) (only parsing).
