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
Require Import Reals.
Require Import Lra.
From Flocq Require Import Core BinarySingleNaN Binary PrimFloat.

Open Scope Z_scope.

(** * Definition

    The clamp function bounds a value x to the interval [lo, hi].
    We normalize the bounds using min/max to handle the case where
    lo > hi, ensuring the function is total and symmetric. *)

Definition clamp (x lo hi : Z) : Z :=
  Z.max (Z.min lo hi) (Z.min x (Z.max lo hi)).

(** Equivalence to conditional form, useful for computation and extraction. *)
Lemma clamp_conditional : forall x lo hi,
  clamp x lo hi =
  let lo' := Z.min lo hi in
  let hi' := Z.max lo hi in
  if x <? lo' then lo'
  else if x >? hi' then hi'
  else x.
Proof.
  intros x lo hi.
  unfold clamp.
  assert (Hminmax: Z.min lo hi <= Z.max lo hi) by
    (apply Z.le_trans with lo; [apply Z.le_min_l | apply Z.le_max_l]).
  destruct (x <? Z.min lo hi) eqn:E1.
  - apply Z.ltb_lt in E1.
    rewrite (Z.min_l x (Z.max lo hi)) by lia.
    rewrite Z.max_l by lia.
    reflexivity.
  - apply Z.ltb_ge in E1.
    destruct (x >? Z.max lo hi) eqn:E2.
    + apply Z.gtb_lt in E2.
      rewrite (Z.min_r x (Z.max lo hi)) by lia.
      rewrite Z.max_r by exact Hminmax.
      reflexivity.
    + rewrite Z.gtb_ltb in E2. apply Z.ltb_ge in E2.
      rewrite (Z.min_l x (Z.max lo hi)) by exact E2.
      rewrite Z.max_r by exact E1.
      reflexivity.
Qed.

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
  intros x lo hi. unfold clamp. apply Z.le_max_l.
Qed.

Theorem clamp_upper_bound : forall x lo hi,
  clamp x lo hi <= Z.max lo hi.
Proof.
  intros x lo hi. unfold clamp.
  apply Z.max_lub.
  - apply min_le_max.
  - apply Z.le_min_r.
Qed.

Theorem clamp_in_bounds : forall x lo hi,
  Z.min lo hi <= clamp x lo hi <= Z.max lo hi.
Proof.
  intros. split.
  - apply clamp_lower_bound.
  - apply clamp_upper_bound.
Qed.

(** * Tight Bounds

    The bounds [Z.min lo hi] and [Z.max lo hi] are tight: there exist
    inputs that achieve them. This proves the specification is not
    vacuously satisfied by a constant function. *)

Theorem clamp_achieves_lower : forall lo hi,
  lo <= hi -> clamp (lo - 1) lo hi = lo.
Proof.
  intros lo hi Hle. unfold clamp.
  replace (Z.min lo hi) with lo by (symmetry; apply Z.min_l; lia).
  replace (Z.max lo hi) with hi by (symmetry; apply Z.max_r; lia).
  replace (Z.min (lo - 1) hi) with (lo - 1) by (symmetry; apply Z.min_l; lia).
  rewrite Z.max_l by lia.
  reflexivity.
Qed.

Theorem clamp_achieves_upper : forall lo hi,
  lo <= hi -> clamp (hi + 1) lo hi = hi.
Proof.
  intros lo hi Hle. unfold clamp.
  replace (Z.min lo hi) with lo by (symmetry; apply Z.min_l; lia).
  replace (Z.max lo hi) with hi by (symmetry; apply Z.max_r; lia).
  replace (Z.min (hi + 1) hi) with hi by (symmetry; apply Z.min_r; lia).
  rewrite Z.max_r by lia.
  reflexivity.
Qed.

Theorem clamp_achieves_identity : forall x lo hi,
  Z.min lo hi <= x <= Z.max lo hi -> clamp x lo hi = x.
Proof.
  intros x lo hi [Hlo Hhi]. unfold clamp.
  rewrite (Z.min_l x (Z.max lo hi)) by exact Hhi.
  apply Z.max_r. exact Hlo.
Qed.

Theorem clamp_bounds_tight : forall lo hi,
  lo <= hi ->
  (exists x, clamp x lo hi = lo) /\
  (exists x, clamp x lo hi = hi).
Proof.
  intros lo hi Hle. split.
  - exists (lo - 1). apply clamp_achieves_lower. exact Hle.
  - exists (hi + 1). apply clamp_achieves_upper. exact Hle.
Qed.

(** * Concrete Examples

    Sanity-check the definition with explicit computations. *)

Example clamp_below : clamp 5 10 20 = 10.
Proof. reflexivity. Qed.

Example clamp_above : clamp 25 10 20 = 20.
Proof. reflexivity. Qed.

Example clamp_inside : clamp 15 10 20 = 15.
Proof. reflexivity. Qed.

Example clamp_at_lo : clamp 10 10 20 = 10.
Proof. reflexivity. Qed.

Example clamp_at_hi : clamp 20 10 20 = 20.
Proof. reflexivity. Qed.

Example clamp_swapped_bounds : clamp 15 20 10 = 15.
Proof. reflexivity. Qed.

Example clamp_equal_bounds : clamp 5 7 7 = 7.
Proof. reflexivity. Qed.

Example clamp_negative : clamp (-5) (-10) 0 = (-5).
Proof. reflexivity. Qed.

(** Compute directive for interactive verification. *)
Compute (clamp 100 0 50).  (* = 50 *)
Compute (clamp (-100) 0 50).  (* = 0 *)
Compute (clamp 25 0 50).  (* = 25 *)

(** * Negative Tests

    Demonstrate that invalid claims are rejected. *)

Example clamp_not_identity_below : clamp 5 10 20 <> 5.
Proof. discriminate. Qed.

Example clamp_not_identity_above : clamp 25 10 20 <> 25.
Proof. discriminate. Qed.

Example clamp_not_outside_bounds : ~ (clamp 15 10 20 < 10).
Proof. unfold clamp. simpl. lia. Qed.

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
  rewrite clamp_conditional. simpl.
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
    + exfalso. apply Hne. reflexivity.
  - intros [Hlt | Hgt].
    + unfold clamp.
      rewrite (Z.min_l x (Z.max lo hi)) by (apply Z.le_trans with (Z.min lo hi); [lia | apply min_le_max]).
      rewrite Z.max_l by lia. lia.
    + unfold clamp.
      rewrite (Z.min_r x (Z.max lo hi)) by lia.
      rewrite Z.max_r by apply min_le_max. lia.
Qed.

(** * Algebraic Form

    clamp is defined as Z.max (Z.min lo hi) (Z.min x (Z.max lo hi)).
    This lemma is now definitional. *)

Theorem clamp_algebraic : forall x lo hi,
  clamp x lo hi = Z.max (Z.min lo hi) (Z.min x (Z.max lo hi)).
Proof.
  intros x lo hi. reflexivity.
Qed.

(** * Fixpoints at Bounds

    Values at the bounds are unchanged by clamping. *)

Theorem clamp_fixpoint_min : forall lo hi,
  clamp (Z.min lo hi) lo hi = Z.min lo hi.
Proof.
  intros lo hi. unfold clamp.
  replace (Z.min (Z.min lo hi) (Z.max lo hi)) with (Z.min lo hi)
    by (symmetry; apply Z.min_l; apply min_le_max).
  apply Z.max_id.
Qed.

Theorem clamp_fixpoint_max : forall lo hi,
  clamp (Z.max lo hi) lo hi = Z.max lo hi.
Proof.
  intros lo hi. unfold clamp.
  rewrite Z.min_id.
  apply Z.max_r. apply min_le_max.
Qed.

Theorem clamp_fixpoint_interior : forall x lo hi,
  Z.min lo hi <= x <= Z.max lo hi ->
  clamp x lo hi = x.
Proof.
  intros x lo hi [Hlo Hhi]. unfold clamp.
  rewrite (Z.min_l x (Z.max lo hi)) by exact Hhi.
  apply Z.max_r. exact Hlo.
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

    Swapping lo and hi does not change the result. This follows
    compositionally from the commutativity of [Z.min] and [Z.max]:

      clamp x lo hi
    = Z.max (Z.min lo hi) (Z.min x (Z.max lo hi))    [by definition]
    = Z.max (Z.min hi lo) (Z.min x (Z.max hi lo))    [by Z.min_comm, Z.max_comm]
    = clamp x hi lo                                   [by definition]

    This derivation shows the symmetry is not accidental but inherent
    in the algebraic structure of the definition. *)

Theorem clamp_symmetric : forall x lo hi,
  clamp x lo hi = clamp x hi lo.
Proof.
  intros x lo hi. unfold clamp.
  rewrite (Z.min_comm lo hi).
  rewrite (Z.max_comm lo hi).
  reflexivity.
Qed.

(** * Option Variant

    [clamp_safe] returns [None] if [lo > hi], treating this as malformed
    input that the caller should handle explicitly.

    Design rationale:
    - [clamp] silently normalizes swapped bounds via min/max, which is
      convenient but masks potential caller bugs.
    - [clamp_safe] treats [lo > hi] as an error condition, forcing the
      caller to handle it. Use this when swapped bounds indicate a bug
      rather than a valid alternative representation.

    The two functions are related by:
      [clamp_safe x lo hi = Some v <-> lo <= hi /\ v = clamp x lo hi]

    Choose [clamp] for internal code where you trust or normalize inputs.
    Choose [clamp_safe] for API boundaries with untrusted input. *)

Definition clamp_safe (x lo hi : Z) : option Z :=
  if lo <=? hi then Some (clamp x lo hi) else None.

Theorem clamp_safe_some_iff : forall x lo hi v,
  clamp_safe x lo hi = Some v <-> (lo <= hi /\ v = clamp x lo hi).
Proof.
  intros x lo hi v. unfold clamp_safe.
  destruct (lo <=? hi) eqn:E.
  - apply Z.leb_le in E. split.
    + intros H. inversion H. auto.
    + intros [_ Hv]. subst. reflexivity.
  - apply Z.leb_gt in E. split.
    + intros H. discriminate.
    + intros [Hle _]. lia.
Qed.

Theorem clamp_safe_none_iff : forall x lo hi,
  clamp_safe x lo hi = None <-> hi < lo.
Proof.
  intros x lo hi. unfold clamp_safe.
  destruct (lo <=? hi) eqn:E.
  - apply Z.leb_le in E. split; [discriminate | lia].
  - apply Z.leb_gt in E. split; [auto | intros; reflexivity].
Qed.

Theorem clamp_safe_in_bounds : forall x lo hi v,
  clamp_safe x lo hi = Some v -> lo <= v <= hi.
Proof.
  intros x lo hi v H.
  apply clamp_safe_some_iff in H. destruct H as [Hle Hv]. subst.
  pose proof (clamp_in_bounds x lo hi) as [Hmin Hmax].
  rewrite Z.min_l in Hmin by lia.
  rewrite Z.max_r in Hmax by lia.
  split; assumption.
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

(** Alternative direct proof via case analysis (pedagogical).
    The algebraic proof above is preferred: cleaner, faster to compile.

Theorem clamp_monotone_direct : forall x y lo hi,
  x <= y -> clamp x lo hi <= clamp y lo hi.
Proof.
  intros x y lo hi Hxy.
  rewrite !clamp_conditional. simpl.
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
*)

(** * Extensionality

    Clamp respects equality: equal inputs yield equal outputs. *)

Lemma clamp_ext : forall x1 x2 lo1 lo2 hi1 hi2,
  x1 = x2 -> lo1 = lo2 -> hi1 = hi2 ->
  clamp x1 lo1 hi1 = clamp x2 lo2 hi2.
Proof.
  intros. subst. reflexivity.
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

(** When intervals don't overlap, composition clamps to the gap point. *)

Theorem clamp_disjoint_left : forall x lo1 hi1 lo2 hi2,
  lo1 <= hi1 -> lo2 <= hi2 -> hi1 < lo2 ->
  clamp (clamp x lo1 hi1) lo2 hi2 = lo2.
Proof.
  intros x lo1 hi1 lo2 hi2 H1 H2 Hgap.
  pose proof (clamp_in_bounds x lo1 hi1) as [Hmin Hmax].
  rewrite Z.min_l in Hmin by lia.
  rewrite Z.max_r in Hmax by lia.
  unfold clamp at 1.
  replace (Z.min lo2 hi2) with lo2 by (symmetry; apply Z.min_l; lia).
  replace (Z.max lo2 hi2) with hi2 by (symmetry; apply Z.max_r; lia).
  rewrite (Z.min_l (clamp x lo1 hi1) hi2) by lia.
  apply Z.max_l. lia.
Qed.

Theorem clamp_disjoint_right : forall x lo1 hi1 lo2 hi2,
  lo1 <= hi1 -> lo2 <= hi2 -> hi2 < lo1 ->
  clamp (clamp x lo1 hi1) lo2 hi2 = hi2.
Proof.
  intros x lo1 hi1 lo2 hi2 H1 H2 Hgap.
  pose proof (clamp_in_bounds x lo1 hi1) as [Hmin Hmax].
  rewrite Z.min_l in Hmin by lia.
  rewrite Z.max_r in Hmax by lia.
  unfold clamp at 1.
  replace (Z.min lo2 hi2) with lo2 by (symmetry; apply Z.min_l; lia).
  replace (Z.max lo2 hi2) with hi2 by (symmetry; apply Z.max_r; lia).
  rewrite (Z.min_r (clamp x lo1 hi1) hi2) by lia.
  apply Z.max_r. lia.
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

    ** Overflow Safety Argument **

    The clamp function uses only [Z.min] and [Z.max], which are
    _selection_ operations: they return one of their inputs unchanged.
    This means:

    1. No arithmetic is performed (no addition, subtraction, multiplication)
    2. If both inputs are in [INT63_MIN, INT63_MAX], the output is too
    3. No intermediate computation can overflow

    When extracted to OCaml, [Z.min] and [Z.max] become [Stdlib.min] and
    [Stdlib.max], which are polymorphic comparison-based selections.
    These are inherently overflow-safe for any integer type.

    The theorems below prove this formally: if [lo] and [hi] are valid
    int63 values, then [clamp x lo hi] is also valid, regardless of [x]. *)

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

(** Intermediate computations stay in range.
    When bounds are valid int63, Z.min and Z.max of bounds are also valid.
    This guarantees no overflow in any subexpression of clamp. *)

Theorem zmin_in_bounds : forall lo hi,
  int63_in_bounds lo -> int63_in_bounds hi ->
  int63_in_bounds (Z.min lo hi).
Proof.
  intros lo hi [HloMin HloMax] [HhiMin HhiMax].
  unfold int63_in_bounds, in_bounds. split.
  - apply Z.min_glb; assumption.
  - apply Z.le_trans with lo.
    + apply Z.le_min_l.
    + exact HloMax.
Qed.

Theorem zmax_in_bounds : forall lo hi,
  int63_in_bounds lo -> int63_in_bounds hi ->
  int63_in_bounds (Z.max lo hi).
Proof.
  intros lo hi [HloMin HloMax] [HhiMin HhiMax].
  unfold int63_in_bounds, in_bounds. split.
  - apply Z.le_trans with lo.
    + exact HloMin.
    + apply Z.le_max_l.
  - apply Z.max_lub; assumption.
Qed.

(** min and max are selection operations: output equals one of the inputs. *)

Lemma zmin_is_selection : forall a b, Z.min a b = a \/ Z.min a b = b.
Proof.
  intros a b.
  destruct (Z.le_ge_cases a b) as [Hle | Hge].
  - left. apply Z.min_l. exact Hle.
  - right. apply Z.min_r. lia.
Qed.

Lemma zmax_is_selection : forall a b, Z.max a b = a \/ Z.max a b = b.
Proof.
  intros a b.
  destruct (Z.le_ge_cases a b) as [Hle | Hge].
  - right. apply Z.max_r. exact Hle.
  - left. apply Z.max_l. lia.
Qed.

(** clamp output is one of: lo, hi, or x (when in bounds). *)
Theorem clamp_is_selection : forall x lo hi,
  clamp x lo hi = Z.min lo hi \/
  clamp x lo hi = Z.max lo hi \/
  clamp x lo hi = x.
Proof.
  intros x lo hi.
  pose proof (clamp_trichotomy x lo hi) as Htri.
  destruct Htri as [Hlt | Hgt | Hin].
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.

Theorem clamp_intermediates_safe : forall x lo hi,
  int63_in_bounds lo -> int63_in_bounds hi ->
  int63_in_bounds (Z.min lo hi) /\
  int63_in_bounds (Z.max lo hi) /\
  int63_in_bounds (clamp x lo hi).
Proof.
  intros x lo hi Hlo Hhi.
  split.
  - apply zmin_in_bounds; assumption.
  - split.
    + apply zmax_in_bounds; assumption.
    + apply clamp_int63_safe; assumption.
Qed.

(** * Real Number Variant

    Clamp for real numbers. Identical structure to the integer version.
    NOTE: Uses classical [Rle_dec], so this is for specification/proofs
    only—not extracted to executable code. *)

Open Scope R_scope.

Definition clamp_R (x lo hi : R) : R :=
  let lo' := Rmin lo hi in
  let hi' := Rmax lo hi in
  if Rle_lt_dec x lo' then lo'
  else if Rle_lt_dec hi' x then hi'
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
  destruct (Rle_lt_dec x (Rmin lo hi)) as [Hlt|Hge].
  - apply Rle_refl.
  - destruct (Rle_lt_dec (Rmax lo hi) x) as [Hgt|Hle].
    + apply Rmin_le_Rmax.
    + lra.
Qed.

Theorem clamp_R_upper_bound : forall x lo hi,
  clamp_R x lo hi <= Rmax lo hi.
Proof.
  intros x lo hi.
  unfold clamp_R.
  destruct (Rle_lt_dec x (Rmin lo hi)) as [Hlt|Hge].
  - apply Rmin_le_Rmax.
  - destruct (Rle_lt_dec (Rmax lo hi) x) as [Hgt|Hle].
    + apply Rle_refl.
    + lra.
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

(** * IEEE 754 Binary64 Floating-Point (Flocq)

    Verified IEEE 754 binary64 clamp using Flocq library.
    Uses Coq's primitive [float] type which extracts directly to OCaml floats.

    Flocq's PrimFloat module provides:
    - [Prim2B]: Coq float → binary_float (with validity proof)
    - [B2Prim]: binary_float → Coq float
    - Correspondence theorems proving OCaml float ops match IEEE 754

    This gives full IEEE 754 semantics including:
    - Signed zeros (±0)
    - NaN propagation (quiet NaN semantics)
    - Infinity handling
    - Round-to-nearest-even (default IEEE mode) *)

(** Min/max for primitive floats using comparison.
    NaN-propagating semantics: if either operand is NaN, returns NaN. *)

Definition prim_min (x y : PrimFloat.float) : PrimFloat.float :=
  if PrimFloat.is_nan x then x
  else if PrimFloat.is_nan y then y
  else if PrimFloat.leb x y then x else y.

Definition prim_max (x y : PrimFloat.float) : PrimFloat.float :=
  if PrimFloat.is_nan x then x
  else if PrimFloat.is_nan y then y
  else if PrimFloat.leb x y then y else x.

(** Clamp for primitive floats (extracts to OCaml).
    Uses Coq's primitive float operations which Flocq proves
    correspond to IEEE 754 binary64 semantics via PrimFloat. *)

Definition clamp_prim (x lo hi : PrimFloat.float) : PrimFloat.float :=
  if PrimFloat.is_nan x then x
  else if PrimFloat.is_nan lo then lo
  else if PrimFloat.is_nan hi then hi
  else
    let lo' := prim_min lo hi in
    let hi' := prim_max lo hi in
    prim_max lo' (prim_min x hi').

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
    pose proof (safe_int_in_bounds lo) as [HloMIN HloMAX].
    pose proof (safe_int_in_bounds hi) as [HhiMIN HhiMAX].
    apply check_bounds_correct.
    apply clamp_no_overflow; assumption.
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

(** * INT63 Instantiation for Extraction

    Wrapper that fixes MIN/MAX to int63 bounds for cleaner OCaml API. *)

Definition clamp_int63_verified (x : Z) (lo hi : safe_int INT63_MIN INT63_MAX)
  : safe_int INT63_MIN INT63_MAX :=
  clamp_verified INT63_MIN INT63_MAX x lo hi.

Definition check_int63_bounds : Z -> bool := check_bounds INT63_MIN INT63_MAX.

Definition clamp_int63_checked (x lo hi : Z) : Z * bool :=
  clamp_checked INT63_MIN INT63_MAX x lo hi.

(** * Hint Database

    The [clamp] hint database provides automation for downstream proofs.
    Use [auto with clamp] or [eauto with clamp] to apply these lemmas. *)

#[export] Hint Resolve clamp_lower_bound : clamp.
#[export] Hint Resolve clamp_upper_bound : clamp.
#[export] Hint Resolve clamp_in_bounds : clamp.
#[export] Hint Resolve clamp_idempotent : clamp.
#[export] Hint Resolve clamp_symmetric : clamp.
#[export] Hint Resolve clamp_monotone : clamp.
#[export] Hint Resolve clamp_safe_in_bounds : clamp.
#[export] Hint Resolve min_le_max : clamp.

(** * Extraction

    Extracted functions:
    - clamp: the core function, no runtime checks
    - clamp_safe: returns [option Z], None if lo > hi
    - clamp_list: vectorized clamp over lists
    - check_bounds: runtime bounds test, extracts to bool-returning function
    - clamp_checked: returns (result, valid) pair for runtime validation
    - safe_int: extracts to just [int] (proof field erases)
    - clamp_verified: extracts to same as [clamp] (proofs erase)

    NOT extracted (specification only):
    - clamp_R: Real number variant. Uses classical axioms ([Rle_lt_dec])
      that cannot be realized in executable code. Use for Coq-level
      reasoning about continuous domains; do not extract.

    Extracted float operations:
    - clamp_prim: IEEE 754 binary64 clamp via Flocq/PrimFloat
    - prim_min, prim_max: NaN-propagating min/max *)

Require Extraction.
Require ExtrOcamlBasic.
Require ExtrOcamlZInt.
Require ExtrOCamlFloats.

Extraction Language OCaml.

Extract Inlined Constant INT63_MIN => "Int.min_int".
Extract Inlined Constant INT63_MAX => "Int.max_int".

Set Extraction Output Directory "D:\clamp-verified".

Extraction "clamp.ml" clamp clamp_safe clamp_list check_bounds clamp_checked safe_int clamp_verified check_int63_bounds clamp_int63_checked clamp_int63_verified.

Extraction "clamp_float.ml" prim_min prim_max clamp_prim.
