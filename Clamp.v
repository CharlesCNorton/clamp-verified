(******************************************************************************)
(*                                                                            *)
(*                         Clamp: Bounded Value Utility                       *)
(*                                                                            *)
(*     clamp(x, lo, hi) returns x bounded to [lo, hi]. Proves result is       *)
(*     within bounds, handles lo > hi case, and satisfies idempotence:        *)
(*     clamp(clamp(x, lo, hi), lo, hi) = clamp(x, lo, hi).                    *)
(*                                                                            *)
(*     Precondition: none. Postcondition: lo <= result <= hi when lo <= hi;   *)
(*     hi <= result <= lo when hi < lo. Totality and termination proven.      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 7, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

(** * Definition *)

Definition clamp (x lo hi : Z) : Z :=
  let lo' := Z.min lo hi in
  let hi' := Z.max lo hi in
  if x <? lo' then lo'
  else if x >? hi' then hi'
  else x.

(** * Bounds Theorems *)

Theorem clamp_lower_bound : forall x lo hi,
  Z.min lo hi <= clamp x lo hi.
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - lia.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + apply Z.ltb_ge in E1. lia.
    + apply Z.ltb_ge in E1. lia.
Qed.

Theorem clamp_upper_bound : forall x lo hi,
  clamp x lo hi <= Z.max lo hi.
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - lia.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + lia.
    + rewrite Z.gtb_ltb in E2. apply Z.ltb_ge in E2. lia.
Qed.

Theorem clamp_in_bounds : forall x lo hi,
  Z.min lo hi <= clamp x lo hi <= Z.max lo hi.
Proof.
  intros. split.
  - apply clamp_lower_bound.
  - apply clamp_upper_bound.
Qed.

(** * Idempotence *)

Lemma clamp_cases : forall x lo hi,
  clamp x lo hi = Z.min lo hi \/ clamp x lo hi = Z.max lo hi \/ clamp x lo hi = x.
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - left. reflexivity.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + right. left. reflexivity.
    + right. right. reflexivity.
Qed.

Theorem clamp_idempotent : forall x lo hi,
  clamp (clamp x lo hi) lo hi = clamp x lo hi.
Proof.
  intros x lo hi.
  assert (Hbounds: Z.min lo hi <= clamp x lo hi <= Z.max lo hi)
    by apply clamp_in_bounds.
  unfold clamp at 1.
  destruct (clamp x lo hi <? Z.min lo hi) eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (clamp x lo hi >? Z.max lo hi) eqn:E2.
    + rewrite Z.gtb_ltb in E2. apply Z.ltb_lt in E2. lia.
    + reflexivity.
Qed.

(** * Extraction *)

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlZInt.

Extraction Language OCaml.

Extraction "clamp.ml" clamp.
