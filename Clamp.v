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

    Reflection lemmas for boolean comparisons. *)

Lemma ltb_reflect : forall x y, x <? y = true <-> x < y.
Proof. intros. apply Z.ltb_lt. Qed.

Lemma ltb_reflect_false : forall x y, x <? y = false <-> y <= x.
Proof. intros. apply Z.ltb_ge. Qed.

Lemma gtb_reflect : forall x y, x >? y = true <-> x > y.
Proof.
  intros. rewrite Z.gtb_ltb, Z.ltb_lt. lia.
Qed.

Lemma gtb_reflect_false : forall x y, x >? y = false <-> x <= y.
Proof.
  intros. rewrite Z.gtb_ltb, Z.ltb_ge. lia.
Qed.

(** Key min/max ordering fact, proved via library lemmas. *)
Lemma min_le_max : forall a b, Z.min a b <= Z.max a b.
Proof.
  intros.
  apply Z.le_trans with a.
  - apply Z.le_min_l.
  - apply Z.le_max_l.
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
    apply Z.le_refl.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + (* x > max: return max >= min *)
      apply min_le_max.
    + (* min <= x <= max: return x *)
      apply ltb_reflect_false in E1. exact E1.
Qed.

Theorem clamp_upper_bound : forall x lo hi,
  clamp x lo hi <= Z.max lo hi.
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - (* x < min: return min <= max *)
    apply min_le_max.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + (* x > max: return max *)
      apply Z.le_refl.
    + (* min <= x <= max: return x *)
      apply gtb_reflect_false in E2. exact E2.
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
      apply clamp_identity. split; assumption.
Qed.

(** * Algebraic Equivalence

    clamp can be expressed purely in terms of Z.min and Z.max.
    This equivalence simplifies reasoning about algebraic properties. *)

Theorem clamp_algebraic : forall x lo hi,
  clamp x lo hi = Z.max (Z.min lo hi) (Z.min x (Z.max lo hi)).
Proof.
  intros x lo hi.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - (* x < min lo hi *)
    apply ltb_reflect in E1.
    assert (Hxmax: x <= Z.max lo hi) by
      (apply Z.le_trans with (Z.min lo hi); [apply Z.lt_le_incl; exact E1 | apply min_le_max]).
    replace (Z.min x (Z.max lo hi)) with x by (symmetry; apply Z.min_l; exact Hxmax).
    replace (Z.max (Z.min lo hi) x) with (Z.min lo hi) by (symmetry; apply Z.max_l; apply Z.lt_le_incl; exact E1).
    reflexivity.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + (* x > max lo hi *)
      apply gtb_reflect in E2.
      assert (Hmaxlex: Z.max lo hi <= x) by (apply Z.gt_lt_iff in E2; apply Z.lt_le_incl; exact E2).
      replace (Z.min x (Z.max lo hi)) with (Z.max lo hi) by (symmetry; apply Z.min_r; exact Hmaxlex).
      replace (Z.max (Z.min lo hi) (Z.max lo hi)) with (Z.max lo hi) by (symmetry; apply Z.max_r; apply min_le_max).
      reflexivity.
    + (* min lo hi <= x <= max lo hi *)
      apply ltb_reflect_false in E1.
      apply gtb_reflect_false in E2.
      replace (Z.min x (Z.max lo hi)) with x by (symmetry; apply Z.min_l; exact E2).
      replace (Z.max (Z.min lo hi) x) with x by (symmetry; apply Z.max_r; exact E1).
      reflexivity.
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
  - apply ltb_reflect in E1.
    exfalso. apply (Z.lt_irrefl (Z.min lo hi)).
    apply Z.le_lt_trans with (clamp x lo hi); assumption.
  - destruct (clamp x lo hi >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. apply Z.gt_lt_iff in E2.
      exfalso. apply (Z.lt_irrefl (Z.max lo hi)).
      apply Z.lt_le_trans with (clamp x lo hi); assumption.
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
  - apply ltb_reflect in E1. exfalso. apply (Z.lt_irrefl _ E1).
  - destruct (Z.min lo hi >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. apply Z.gt_lt_iff in E2.
      exfalso. apply (Z.lt_irrefl (Z.min lo hi)).
      apply Z.le_lt_trans with (Z.max lo hi); [apply min_le_max | exact E2].
    + reflexivity.
Qed.

Theorem clamp_fixpoint_max : forall lo hi,
  clamp (Z.max lo hi) lo hi = Z.max lo hi.
Proof.
  intros lo hi.
  unfold clamp.
  destruct (Z.max lo hi <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1.
    exfalso. apply (Z.lt_irrefl (Z.min lo hi)).
    apply Z.le_lt_trans with (Z.max lo hi); [apply min_le_max | exact E1].
  - destruct (Z.max lo hi >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. apply Z.gt_lt_iff in E2.
      exfalso. apply (Z.lt_irrefl _ E2).
    + reflexivity.
Qed.

Theorem clamp_fixpoint_interior : forall x lo hi,
  Z.min lo hi <= x <= Z.max lo hi ->
  clamp x lo hi = x.
Proof.
  intros x lo hi [Hlo Hhi].
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:E1.
  - apply ltb_reflect in E1.
    exfalso. apply (Z.lt_irrefl x).
    apply Z.lt_le_trans with (Z.min lo hi); assumption.
  - destruct (x >? Z.max lo hi) eqn:E2.
    + apply gtb_reflect in E2. apply Z.gt_lt_iff in E2.
      exfalso. apply (Z.lt_irrefl x).
      apply Z.le_lt_trans with (Z.max lo hi); [assumption | exact E2].
    + reflexivity.
Qed.

(** * Symmetry Under Bound Swap

    Swapping lo and hi does not change the result. *)

Theorem clamp_symmetric : forall x lo hi,
  clamp x lo hi = clamp x hi lo.
Proof.
  intros x lo hi.
  unfold clamp.
  rewrite Z.min_comm.
  rewrite Z.max_comm.
  reflexivity.
Qed.

(** * Monotonicity

    clamp preserves order: if x <= y, then clamp x <= clamp y.
    Proved via the algebraic equivalence using monotonicity of min/max. *)

Theorem clamp_monotone : forall x y lo hi,
  x <= y -> clamp x lo hi <= clamp y lo hi.
Proof.
  intros x y lo hi Hxy.
  rewrite !clamp_algebraic.
  apply Z.max_le_compat_l.
  apply Z.min_le_compat_r.
  exact Hxy.
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
  split.
  - apply Z.le_trans with (Z.min lo1 hi1); assumption.
  - apply Z.le_trans with (Z.max lo1 hi1); assumption.
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

  (** A bounded integer is a Z with proof it lies in [BOUND_LO, BOUND_HI]. *)

  Variable BOUND_LO : Z.
  Variable BOUND_HI : Z.

  Definition in_bounds (z : Z) : Prop := BOUND_LO <= z <= BOUND_HI.

  Definition bounded := { z : Z | in_bounds z }.

  Definition bounded_val (b : bounded) : Z := proj1_sig b.

  (** Construct a bounded integer from a Z with proof. *)
  Definition mk_bounded (z : Z) (H : in_bounds z) : bounded :=
    exist _ z H.

  (** clamp is closed: if lo, hi are in bounds, result is in bounds.
      This is the key theorem for overflow safety. *)
  Theorem clamp_closed : forall x lo hi,
    in_bounds lo -> in_bounds hi ->
    in_bounds (clamp x lo hi).
  Proof.
    intros x lo hi [HloL HloH] [HhiL HhiH].
    unfold in_bounds.
    pose proof (clamp_in_bounds x lo hi) as [Hmin Hmax].
    split.
    - apply Z.le_trans with (Z.min lo hi).
      + apply Z.min_glb; assumption.
      + exact Hmin.
    - apply Z.le_trans with (Z.max lo hi).
      + exact Hmax.
      + apply Z.max_lub; assumption.
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

  (** Properties lift to the bounded variant via the unbounded proofs. *)

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

    Instantiate for 63-bit signed integers (OCaml int on 64-bit).
    Note: These constants are for specification only; the clamp function
    itself operates on mathematical integers. *)

Definition INT63_MIN : Z := -(2^62).
Definition INT63_MAX : Z := 2^62 - 1.

Definition int63_in_bounds := in_bounds INT63_MIN INT63_MAX.

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
    result fits in machine integers. *)

Theorem clamp_no_overflow : forall x lo hi MIN MAX,
  MIN <= lo -> lo <= MAX ->
  MIN <= hi -> hi <= MAX ->
  MIN <= clamp x lo hi <= MAX.
Proof.
  intros x lo hi MIN MAX HloMin HloMax HhiMin HhiMax.
  pose proof (clamp_in_bounds x lo hi) as [Hmin Hmax].
  split.
  - apply Z.le_trans with (Z.min lo hi).
    + apply Z.min_glb; assumption.
    + exact Hmin.
  - apply Z.le_trans with (Z.max lo hi).
    + exact Hmax.
    + apply Z.max_lub; assumption.
Qed.

(** * Extraction

    We extract to OCaml. The clamp function extracts to executable code.
    Proof terms (clamp_in_bounds, clamp_no_overflow, etc.) are in Prop
    and erase during extraction; they exist for Coq-side verification
    only, not as runtime checks. *)

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlZInt.

Extraction Language OCaml.

Extraction "clamp.ml" clamp.
