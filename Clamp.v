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

(* TODO:
   - Fix make_safe obligation: use exact H instead of split; assumption.
   - Fix clamp_verified obligation: destruct safe_int_in_bounds conjunction.
   - Make clamp_R computable: replace Rle_dec with Rle_lt_dec.
   - Add clamp_safe : Z -> Z -> Z -> option Z with runtime bounds check.
   - Add Hint database for downstream proof automation.
   - Add composition law for overlapping intervals.
   - Add concrete witnesses (Example and Compute on specific values).
   - Add negative tests demonstrating rejection of invalid inputs.
*)

Require Import ZArith.
Require Import Lia.
Require Import Morphisms.
Require Import Reals.
Require Import Lra.

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

(** Use trichotomy to prove clamp either changes value or preserves it. *)
Theorem clamp_change_iff : forall x lo hi,
  clamp x lo hi <> x <-> (x < Z.min lo hi \/ x > Z.max lo hi).
Proof.
  intros x lo hi. split.
  - intros Hne.
    pose proof (clamp_trichotomy x lo hi) as Htri.
    destruct Htri as [Hlt | Hgt | [Hlo Hhi]].
    + left. exact Hlt.
    + right. exact Hgt.
    + exfalso. apply Hne.
      unfold clamp.
      destruct (x <? Z.min lo hi) eqn:E1.
      * apply ltb_reflect in E1. lia.
      * destruct (x >? Z.max lo hi) eqn:E2.
        -- apply gtb_reflect in E2. lia.
        -- reflexivity.
  - intros [Hlt | Hgt].
    + unfold clamp.
      apply Z.ltb_lt in Hlt. rewrite Hlt.
      lia.
    + unfold clamp.
      destruct (x <? Z.min lo hi) eqn:E1.
      * apply ltb_reflect in E1. lia.
      * assert (Hgtb: (x >? Z.max lo hi) = true) by (apply Z.gtb_lt; lia).
        rewrite Hgtb. lia.
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

(** * Idempotence

    Clamping an already-clamped value has no effect.
    This is essential for compositional reasoning. *)

Theorem clamp_idempotent : forall x lo hi,
  clamp (clamp x lo hi) lo hi = clamp x lo hi.
Proof.
  intros. apply clamp_fixpoint_interior. apply clamp_in_bounds.
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

(** Alternative direct proof via case analysis. *)

Theorem clamp_monotone_direct : forall x y lo hi,
  x <= y -> clamp x lo hi <= clamp y lo hi.
Proof.
  intros x y lo hi Hxy.
  unfold clamp.
  destruct (x <? Z.min lo hi) eqn:Ex1;
  destruct (y <? Z.min lo hi) eqn:Ey1;
  destruct (x >? Z.max lo hi) eqn:Ex2;
  destruct (y >? Z.max lo hi) eqn:Ey2;
  try apply Z.le_refl;
  try apply min_le_max;
  apply ltb_reflect in Ex1 || apply ltb_reflect_false in Ex1;
  apply ltb_reflect in Ey1 || apply ltb_reflect_false in Ey1;
  apply gtb_reflect in Ex2 || apply gtb_reflect_false in Ex2;
  apply gtb_reflect in Ey2 || apply gtb_reflect_false in Ey2;
  lia.
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

  (** clamp is closed: if lo, hi are in bounds, result is in bounds. *)
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
      + assumption.
    - apply Z.le_trans with (Z.max lo hi).
      + assumption.
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

    Instantiate for OCaml int on 64-bit systems: 63 bits total,
    1 sign bit + 62 magnitude bits, giving range [-(2^62), 2^62 - 1].
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

(** * Real Number Variant

    Clamp for real numbers. Identical structure to the integer version.
    NOTE: Uses classical [Rle_dec], so this is for specification/proofs
    only—not extracted to executable code. *)

Open Scope R_scope.

Definition clamp_R (x lo hi : R) : R :=
  let lo' := Rmin lo hi in
  let hi' := Rmax lo hi in
  if Rle_dec x lo' then lo'
  else if Rle_dec hi' x then hi'
  else x.

Lemma Rmin_le_Rmax : forall a b, Rmin a b <= Rmax a b.
Proof.
  intros.
  apply Rle_trans with a.
  - apply Rmin_l.
  - apply RmaxLess1.
Qed.

Theorem clamp_R_lower_bound : forall x lo hi,
  Rmin lo hi <= clamp_R x lo hi.
Proof.
  intros x lo hi.
  unfold clamp_R.
  destruct (Rle_dec x (Rmin lo hi)) as [Hlt|Hge].
  - apply Rle_refl.
  - destruct (Rle_dec (Rmax lo hi) x) as [Hgt|Hle].
    + apply Rmin_le_Rmax.
    + apply Rnot_le_gt in Hge. lra.
Qed.

Theorem clamp_R_upper_bound : forall x lo hi,
  clamp_R x lo hi <= Rmax lo hi.
Proof.
  intros x lo hi.
  unfold clamp_R.
  destruct (Rle_dec x (Rmin lo hi)) as [Hlt|Hge].
  - apply Rmin_le_Rmax.
  - destruct (Rle_dec (Rmax lo hi) x) as [Hgt|Hle].
    + apply Rle_refl.
    + apply Rnot_le_gt in Hle. lra.
Qed.

Theorem clamp_R_in_bounds : forall x lo hi,
  Rmin lo hi <= clamp_R x lo hi <= Rmax lo hi.
Proof.
  intros. split.
  - apply clamp_R_lower_bound.
  - apply clamp_R_upper_bound.
Qed.

Theorem clamp_R_symmetric : forall x lo hi,
  clamp_R x lo hi = clamp_R x hi lo.
Proof.
  intros x lo hi.
  unfold clamp_R.
  rewrite Rmin_comm.
  rewrite Rmax_comm.
  reflexivity.
Qed.

Close Scope R_scope.
Open Scope Z_scope.

(** * Vectorized Variant

    Apply clamp to each element of a list. *)

Require Import List.
Import ListNotations.

Definition clamp_list (xs : list Z) (lo hi : Z) : list Z :=
  map (fun x => clamp x lo hi) xs.

Theorem clamp_list_length : forall xs lo hi,
  length (clamp_list xs lo hi) = length xs.
Proof.
  intros. unfold clamp_list. apply map_length.
Qed.

Theorem clamp_list_in_bounds : forall xs lo hi,
  Forall (fun x => Z.min lo hi <= x <= Z.max lo hi) (clamp_list xs lo hi).
Proof.
  intros xs lo hi.
  unfold clamp_list.
  apply Forall_map.
  apply Forall_forall.
  intros x _. apply clamp_in_bounds.
Qed.

Theorem clamp_list_idempotent : forall xs lo hi,
  clamp_list (clamp_list xs lo hi) lo hi = clamp_list xs lo hi.
Proof.
  intros xs lo hi.
  unfold clamp_list.
  rewrite map_map.
  apply map_ext.
  intros a. apply clamp_idempotent.
Qed.

Theorem clamp_list_app : forall xs ys lo hi,
  clamp_list (xs ++ ys) lo hi = clamp_list xs lo hi ++ clamp_list ys lo hi.
Proof.
  intros. unfold clamp_list. apply map_app.
Qed.

(** * No-Overflow Guarantee

    The canonical overflow-safety theorem: if bounds fit in [MIN, MAX],
    the result fits in [MIN, MAX]. Used by [clamp_verified] in sections
    and by extraction-time safety proofs. *)

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
    + assumption.
  - apply Z.le_trans with (Z.max lo hi).
    + assumption.
    + apply Z.max_lub; assumption.
Qed.

(** * Verified Clamp for Coq-Level Reasoning

    This section provides a dependent type [safe_int] that bundles
    a value with a proof of bounds. This is useful for Coq-level
    reasoning and type-driven development.

    NOTE: The proof field [safe_evidence] lives in Prop and erases
    during extraction. The extracted [safe_int] becomes just [int].
    For actual runtime bounds checking, use [check_bounds] directly
    or [clamp_checked] which returns [(value, bool)] pairs. *)

Section VerifiedClamp.

  Variable MIN MAX : Z.

  (** Decidable bounds check - computes and extracts to OCaml. *)
  Definition check_bounds (z : Z) : bool :=
    (MIN <=? z) && (z <=? MAX).

  (** Correctness of the check. *)
  Lemma check_bounds_correct : forall z,
    check_bounds z = true <-> MIN <= z <= MAX.
  Proof.
    intros z. unfold check_bounds.
    rewrite Bool.andb_true_iff.
    rewrite Z.leb_le. rewrite Z.leb_le.
    reflexivity.
  Qed.

  (** A safe integer: value plus proof it's in bounds.
      The proof erases during extraction; use for Coq reasoning only. *)
  Record safe_int := mk_safe_int {
    safe_val : Z;
    safe_evidence : check_bounds safe_val = true
  }.

  (** Extract the proof from evidence. *)
  Lemma safe_int_in_bounds : forall s, MIN <= safe_val s <= MAX.
  Proof.
    intros [v e]. simpl. apply check_bounds_correct. exact e.
  Qed.

  (** Build a safe_int from a value known to be in bounds. *)
  Program Definition make_safe (z : Z) (H : MIN <= z <= MAX) : safe_int :=
    mk_safe_int z _.
  Next Obligation.
    apply check_bounds_correct. split; assumption.
  Defined.

  (** clamp with verified bounds - returns safe_int. *)
  Program Definition clamp_verified (x : Z) (lo hi : safe_int) : safe_int :=
    mk_safe_int (clamp x (safe_val lo) (safe_val hi)) _.
  Next Obligation.
    apply check_bounds_correct.
    apply clamp_no_overflow.
    - apply safe_int_in_bounds.
    - apply safe_int_in_bounds.
    - apply safe_int_in_bounds.
    - apply safe_int_in_bounds.
  Defined.

  (** The verified version computes the same value. *)
  Theorem clamp_verified_correct : forall x lo hi,
    safe_val (clamp_verified x lo hi) = clamp x (safe_val lo) (safe_val hi).
  Proof.
    intros. unfold clamp_verified. simpl. reflexivity.
  Qed.

  (** Runtime bounds checking: returns (result, is_valid) pair.
      This DOES survive extraction and provides actual runtime checking. *)
  Definition clamp_checked (x lo hi : Z) : Z * bool :=
    let result := clamp x lo hi in
    (result, andb (andb (check_bounds lo) (check_bounds hi)) (check_bounds result)).

  (** The bool is true iff lo, hi, and result are all in [MIN, MAX]. *)
  Theorem clamp_checked_true_iff : forall x lo hi,
    snd (clamp_checked x lo hi) = true <->
    (check_bounds lo = true /\ check_bounds hi = true /\ check_bounds (clamp x lo hi) = true).
  Proof.
    intros x lo hi. unfold clamp_checked. simpl.
    rewrite !Bool.andb_true_iff. tauto.
  Qed.

  (** If bounds are valid, the result check always succeeds. *)
  Theorem clamp_checked_correct : forall x lo hi,
    check_bounds lo = true ->
    check_bounds hi = true ->
    snd (clamp_checked x lo hi) = true.
  Proof.
    intros x lo hi Hlo Hhi.
    apply clamp_checked_true_iff. repeat split; auto.
    apply check_bounds_correct.
    apply check_bounds_correct in Hlo.
    apply check_bounds_correct in Hhi.
    apply clamp_no_overflow; tauto.
  Qed.

End VerifiedClamp.

(** * Extraction

    - clamp: the core function, no runtime checks
    - clamp_list: vectorized clamp over lists
    - check_bounds: runtime bounds test, extracts to bool-returning function
    - clamp_checked: returns (result, valid) pair for runtime validation
    - safe_int: extracts to just [int] (proof field erases)
    - clamp_verified: extracts to same as [clamp] (proofs erase)

    NOTE: clamp_R is NOT extracted. It uses classical [Rle_dec] which
    is non-computational. Use clamp_R for specification/proofs only. *)

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlZInt.

Extraction Language OCaml.

Extraction "clamp.ml" clamp clamp_list check_bounds clamp_checked safe_int clamp_verified.
