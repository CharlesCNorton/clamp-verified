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

(** * Bounded Integer Variant

    For finite-precision targets, we define a bounded integer type
    and prove clamp is closed over any interval. This ensures no
    overflow when inputs and bounds are within machine range. *)

Section BoundedIntegers.

  (** A bounded integer is a Z with proof it lies in [lo, hi]. *)

  Variable BOUND_LO : Z.
  Variable BOUND_HI : Z.
  Hypothesis BOUNDS_VALID : BOUND_LO <= BOUND_HI.

  Definition in_bounds (z : Z) : Prop := BOUND_LO <= z <= BOUND_HI.

  Definition bounded := { z : Z | in_bounds z }.

  Definition bounded_val (b : bounded) : Z := proj1_sig b.

  (** Construct a bounded integer from a Z with proof. *)
  Definition mk_bounded (z : Z) (H : in_bounds z) : bounded :=
    exist _ z H.

  (** clamp is closed: if lo, hi are in bounds, result is in bounds. *)
  Theorem clamp_closed : forall x lo hi,
    in_bounds lo -> in_bounds hi ->
    in_bounds (clamp x lo hi).
  Proof.
    intros x lo hi [HloL HloH] [HhiL HhiH].
    unfold in_bounds.
    pose proof (clamp_in_bounds x lo hi) as [Hmin Hmax].
    split.
    - (* BOUND_LO <= clamp x lo hi *)
      assert (BOUND_LO <= Z.min lo hi) by lia.
      lia.
    - (* clamp x lo hi <= BOUND_HI *)
      assert (Z.max lo hi <= BOUND_HI) by lia.
      lia.
  Qed.

  (** Bounded clamp: takes bounded inputs, returns bounded output. *)
  Definition clamp_bounded (x : Z) (lo hi : bounded) : bounded :=
    let lo_z := bounded_val lo in
    let hi_z := bounded_val hi in
    mk_bounded (clamp x lo_z hi_z)
      (clamp_closed x lo_z hi_z (proj2_sig lo) (proj2_sig hi)).

  (** The bounded version extracts the same value as unbounded. *)
  Theorem clamp_bounded_correct : forall x lo hi,
    bounded_val (clamp_bounded x lo hi) = clamp x (bounded_val lo) (bounded_val hi).
  Proof.
    intros. unfold clamp_bounded, bounded_val, mk_bounded. simpl. reflexivity.
  Qed.

  (** All properties lift to the bounded variant. *)

  Theorem clamp_bounded_idempotent : forall x lo hi,
    clamp x (bounded_val lo) (bounded_val hi) =
    clamp (clamp x (bounded_val lo) (bounded_val hi)) (bounded_val lo) (bounded_val hi).
  Proof.
    intros. symmetry. apply clamp_idempotent.
  Qed.

  Theorem clamp_bounded_monotone : forall x y lo hi,
    x <= y ->
    clamp x (bounded_val lo) (bounded_val hi) <=
    clamp y (bounded_val lo) (bounded_val hi).
  Proof.
    intros. apply clamp_monotone. assumption.
  Qed.

End BoundedIntegers.

(** * Machine Integer Instantiation

    Instantiate for 63-bit signed integers (OCaml int on 64-bit). *)

Definition INT63_MIN : Z := -(2^62).
Definition INT63_MAX : Z := 2^62 - 1.

Lemma int63_bounds_valid : INT63_MIN <= INT63_MAX.
Proof. unfold INT63_MIN, INT63_MAX. lia. Qed.

Definition int63_in_bounds := in_bounds INT63_MIN INT63_MAX.
Definition int63 := bounded INT63_MIN INT63_MAX.

(** If all inputs are valid int63, clamp produces valid int63. *)
Theorem clamp_int63_safe : forall x lo hi,
  int63_in_bounds lo -> int63_in_bounds hi ->
  int63_in_bounds (clamp x lo hi).
Proof.
  intros. apply clamp_closed; assumption.
Qed.

(** * No-Overflow Guarantee

    The critical theorem: clamp never produces a value outside the
    range of its bounds, so if bounds fit in machine integers, the
    result fits in machine integers. No overflow possible. *)

Theorem clamp_no_overflow : forall x lo hi MIN MAX,
  MIN <= MAX ->
  MIN <= lo <= MAX ->
  MIN <= hi <= MAX ->
  MIN <= clamp x lo hi <= MAX.
Proof.
  intros x lo hi MIN MAX Hvalid [HloMin HloMax] [HhiMin HhiMax].
  pose proof (clamp_in_bounds x lo hi) as [Hmin Hmax].
  split.
  - assert (MIN <= Z.min lo hi) by lia. lia.
  - assert (Z.max lo hi <= MAX) by lia. lia.
Qed.

(** * Extraction *)

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlZInt.

Extraction Language OCaml.

(** Extract both unbounded and the closure proof components. *)
Extraction "clamp.ml" clamp clamp_in_bounds clamp_no_overflow.
