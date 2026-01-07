(******************************************************************************)
(*                                                                            *)
(*                         Clamp: Bounded Value Utility                       *)
(*                                                                            *)
(*     clamp(x, lo, hi) returns x bounded to [lo, hi]. Proves result is       *)
(*     within bounds, handles lo > hi case, and satisfies idempotence:        *)
(*     clamp(clamp(x, lo, hi), lo, hi) = clamp(x, lo, hi).                    *)
(*                                                                            *)
(*     Precondition: none. Postcondition: min(lo,hi) <= result <= max(lo,hi). *)
(*     Totality, termination, idempotence, monotonicity, and symmetry proven. *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 7, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import ZArith.
Require Import Lia.
Require Import Morphisms.

Open Scope Z_scope.

(** * Definition

    The clamp function bounds a value x to the interval [lo, hi].
    We normalize the bounds using min/max to handle the case where
    lo > hi, ensuring the function is total and symmetric. *)

Definition clamp (x lo hi : Z) : Z :=
  let lo' := Z.min lo hi in
  let hi' := Z.max lo hi in
  if x <? lo' then lo'
  else if x >? hi' then hi'
  else x.

(** * Auxiliary Lemmas

    These lemmas about Z.min, Z.max, and boolean comparisons
    simplify the main proofs. *)

Lemma min_max_relation : forall a b, Z.min a b <= Z.max a b.
Proof. intros. lia. Qed.

Lemma ltb_reflect : forall x y, x <? y = true <-> x < y.
Proof. intros. apply Z.ltb_lt. Qed.

Lemma ltb_reflect_false : forall x y, x <? y = false <-> y <= x.
Proof. intros. apply Z.ltb_ge. Qed.

Lemma gtb_reflect : forall x y, x >? y = true <-> x > y.
Proof.
  intros. rewrite Z.gtb_ltb. rewrite Z.ltb_lt. lia.
Qed.

Lemma gtb_reflect_false : forall x y, x >? y = false <-> x <= y.
Proof.
  intros. rewrite Z.gtb_ltb. rewrite Z.ltb_ge. lia.
Qed.

(** * Core Bounds Theorems

    The fundamental guarantee: clamp always returns a value
    within the normalized bounds [min(lo,hi), max(lo,hi)]. *)

Theorem clamp_lower_bound : forall x lo hi,
  Z.min lo hi <= clamp x lo hi.
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - (* x < min: return min *)
    lia.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + (* x > max: return max, which >= min *)
      apply ltb_reflect_false in E1. lia.
    + (* min <= x <= max: return x *)
      apply ltb_reflect_false in E1. lia.
Qed.

Theorem clamp_upper_bound : forall x lo hi,
  clamp x lo hi <= Z.max lo hi.
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - (* x < min: return min, which <= max *)
    lia.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + (* x > max: return max *)
      lia.
    + (* min <= x <= max: return x *)
      apply gtb_reflect_false in E2. lia.
Qed.

Theorem clamp_in_bounds : forall x lo hi,
  Z.min lo hi <= clamp x lo hi <= Z.max lo hi.
Proof.
  intros. split.
  - apply clamp_lower_bound.
  - apply clamp_upper_bound.
Qed.

(** * Trichotomy: The Three Cases

    clamp returns exactly one of: min, max, or x unchanged.
    This characterizes the function completely. *)

Inductive clamp_result (x lo hi : Z) : Z -> Prop :=
  | clamp_at_min : x < Z.min lo hi -> clamp_result x lo hi (Z.min lo hi)
  | clamp_at_max : x > Z.max lo hi -> clamp_result x lo hi (Z.max lo hi)
  | clamp_identity : Z.min lo hi <= x <= Z.max lo hi -> clamp_result x lo hi x.

Theorem clamp_trichotomy : forall x lo hi,
  clamp_result x lo hi (clamp x lo hi).
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1. apply clamp_at_min. exact E1.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. apply clamp_at_max. exact E2.
    + apply ltb_reflect_false in E1. apply gtb_reflect_false in E2.
      apply clamp_identity. lia.
Qed.

(** * Idempotence

    Clamping an already-clamped value has no effect.
    This is essential for compositional reasoning. *)

Theorem clamp_idempotent : forall x lo hi,
  clamp (clamp x lo hi) lo hi = clamp x lo hi.
Proof.
  intros x lo hi.
  pose proof (clamp_in_bounds x lo hi) as [Hlo Hhi].
  unfold clamp at 1.
  destruct (clamp x lo hi <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1. lia.
  - destruct (clamp x lo hi >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. lia.
    + reflexivity.
Qed.

(** * Fixpoints at Bounds

    Values at the bounds are unchanged by clamping. *)

Theorem clamp_fixpoint_min : forall lo hi,
  clamp (Z.min lo hi) lo hi = Z.min lo hi.
Proof.
  intros lo hi.
  unfold clamp.
  destruct (Z.min lo hi <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1. lia.
  - destruct (Z.min lo hi >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. lia.
    + reflexivity.
Qed.

Theorem clamp_fixpoint_max : forall lo hi,
  clamp (Z.max lo hi) lo hi = Z.max lo hi.
Proof.
  intros lo hi.
  unfold clamp.
  destruct (Z.max lo hi <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1. lia.
  - destruct (Z.max lo hi >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. lia.
    + reflexivity.
Qed.

Theorem clamp_fixpoint_interior : forall x lo hi,
  Z.min lo hi <= x <= Z.max lo hi ->
  clamp x lo hi = x.
Proof.
  intros x lo hi [Hlo Hhi].
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1. lia.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. lia.
    + reflexivity.
Qed.

(** * Symmetry Under Bound Swap

    Swapping lo and hi does not change the result. *)

Theorem clamp_symmetric : forall x lo hi,
  clamp x lo hi = clamp x hi lo.
Proof.
  intros x lo hi.
  unfold clamp.
  replace (Z.min hi lo) with (Z.min lo hi) by lia.
  replace (Z.max hi lo) with (Z.max lo hi) by lia.
  reflexivity.
Qed.

(** * Monotonicity

    clamp preserves order: if x <= y, then clamp x <= clamp y.
    This is crucial for reasoning about sequences and intervals. *)

Theorem clamp_monotone : forall x y lo hi,
  x <= y -> clamp x lo hi <= clamp y lo hi.
Proof.
  intros x y lo hi Hxy.
  pose proof (clamp_in_bounds x lo hi) as [HxLo HxHi].
  pose proof (clamp_in_bounds y lo hi) as [HyLo HyHi].
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:Ex1;
  destruct (y <? Z.min lo hi) eqn:Ey1.
  - (* both below min *)
    lia.
  - (* x below, y not below *)
    destruct (y >? Z.max lo hi) eqn:Ey2.
    + lia.
    + apply ltb_reflect_false in Ey1. lia.
  - (* x not below, y below: contradiction *)
    apply ltb_reflect in Ey1. apply ltb_reflect_false in Ex1. lia.
  - (* both not below min *)
    destruct (x >? Z.max lo hi) eqn:Ex2;
    destruct (y >? Z.max lo hi) eqn:Ey2.
    + (* both above max *)
      lia.
    + (* x above, y not above: contradiction *)
      apply gtb_reflect in Ex2. apply gtb_reflect_false in Ey2. lia.
    + (* x not above, y above *)
      apply gtb_reflect_false in Ex2. lia.
    + (* both in range *)
      apply gtb_reflect_false in Ex2. apply gtb_reflect_false in Ey2. lia.
Qed.

(** * Proper Instance for Setoid Reasoning *)

#[global]
Instance clamp_proper : Proper (eq ==> eq ==> eq ==> eq) clamp.
Proof.
  intros x1 x2 Hx y1 y2 Hy z1 z2 Hz.
  subst. reflexivity.
Qed.

(** * Composition Theorem

    Clamping to tighter bounds then to looser bounds equals
    clamping to the tighter bounds alone. *)

Theorem clamp_nested_tighter : forall x lo1 hi1 lo2 hi2,
  Z.min lo2 hi2 <= Z.min lo1 hi1 ->
  Z.max lo1 hi1 <= Z.max lo2 hi2 ->
  clamp (clamp x lo1 hi1) lo2 hi2 = clamp x lo1 hi1.
Proof.
  intros x lo1 hi1 lo2 hi2 HloLoose HhiLoose.
  apply clamp_fixpoint_interior.
  pose proof (clamp_in_bounds x lo1 hi1) as [Hlo Hhi].
  lia.
Qed.

(** * Termination Certificate

    clamp is structurally terminating (non-recursive).
    We make this explicit via a fuel-based equivalent. *)

Fixpoint clamp_fuel (fuel : nat) (x lo hi : Z) : option Z :=
  match fuel with
  | O => None
  | S _ => Some (clamp x lo hi)
  end.

Theorem clamp_terminates : forall x lo hi,
  exists result, clamp_fuel 1 x lo hi = Some result /\ result = clamp x lo hi.
Proof.
  intros. exists (clamp x lo hi). split; reflexivity.
Qed.

(** * Extraction

    We extract to OCaml. Note: Z is mapped to OCaml int, which has
    finite precision. The proofs hold for mathematical integers;
    overflow behavior in OCaml may differ. For production use with
    arbitrary precision, use the Zarith library. *)

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlZInt.

Extraction Language OCaml.

Extraction "clamp.ml" clamp.
