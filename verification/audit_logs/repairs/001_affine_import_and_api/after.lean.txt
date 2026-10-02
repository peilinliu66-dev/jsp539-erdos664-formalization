/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original finite-field proofs. The random-restriction application is motivated
by Jiaxi Nie, arXiv:2609.07736. No third-party Erdős 664 source is imported.
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic
import LicensedContainers.Hypergraph

open scoped BigOperators

namespace JSP539
namespace Affine

/-- The affine plane has actual finite-field points, not postulated incidence data. -/
abbrev Point (q : ℕ) := ZMod q × ZMod q

/-- `none` denotes a vertical line; `some m` denotes slope `m`.
The second coordinate is the intercept. -/
abbrev Line (q : ℕ) := Option (ZMod q) × ZMod q

variable {q : ℕ} [Fact q.Prime]

/-- An explicit parametrization of the points of a line. -/
def linePoint (l : Line q) (t : ZMod q) : Point q :=
  match l.1 with
  | none => (l.2, t)
  | some m => (t, m * t + l.2)

/-- Each line is represented by its finite set of points. -/
def points (l : Line q) : Finset (Point q) :=
  Finset.univ.image (linePoint l)

@[simp] theorem mem_points_none (b : ZMod q) (p : Point q) :
    p ∈ points (none, b) ↔ p.1 = b := by
  rcases p with ⟨x, y⟩
  simp only [points, Finset.mem_image, Finset.mem_univ, true_and, linePoint,
    Prod.mk.injEq]
  constructor
  · rintro ⟨t, h, _⟩
    exact h.symm
  · intro h
    exact ⟨y, h.symm, rfl⟩

@[simp] theorem mem_points_some (m b : ZMod q) (p : Point q) :
    p ∈ points (some m, b) ↔ p.2 = m * p.1 + b := by
  rcases p with ⟨x, y⟩
  simp only [points, Finset.mem_image, Finset.mem_univ, true_and, linePoint,
    Prod.mk.injEq]
  constructor
  · rintro ⟨t, rfl, h⟩
    exact h.symm
  · intro h
    exact ⟨x, rfl, h.symm⟩

theorem linePoint_injective (l : Line q) : Function.Injective (linePoint l) := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
    intro x y h
    exact congrArg Prod.snd h
  | some m =>
    intro x y h
    exact congrArg Prod.fst h

@[simp] theorem point_card : Fintype.card (Point q) = q ^ 2 := by
  simp [Point, Fintype.card_prod, ZMod.card, pow_two]

@[simp] theorem line_card : Fintype.card (Line q) = q * (q + 1) := by
  simp [Line, Fintype.card_prod, Fintype.card_option, ZMod.card, Nat.mul_comm]

@[simp] theorem points_card (l : Line q) : (points l).card = q := by
  rw [points, Finset.card_image_of_injective _ (linePoint_injective l)]
  simp [ZMod.card]

/-- The unique line of a specified direction passing through a point. -/
def lineThrough (p : Point q) (d : Option (ZMod q)) : Line q :=
  (d, match d with
    | none => p.1
    | some m => p.2 - m * p.1)

def linesThrough (p : Point q) : Finset (Line q) :=
  Finset.univ.image (lineThrough p)

theorem lineThrough_injective (p : Point q) : Function.Injective (lineThrough p) := by
  intro d e h
  exact congrArg Prod.fst h

@[simp] theorem mem_linesThrough (p : Point q) (l : Line q) :
    l ∈ linesThrough p ↔ p ∈ points l := by
  rcases l with ⟨d, b⟩
  cases d with
  | none =>
    simp only [linesThrough, Finset.mem_image, Finset.mem_univ, true_and,
      mem_points_none]
    constructor
    · rintro ⟨e, he⟩
      have hdir : e = none := congrArg Prod.fst he
      subst e
      exact congrArg Prod.snd he
    · intro h
      exact ⟨none, by simpa [lineThrough] using h⟩
  | some m =>
    simp only [linesThrough, Finset.mem_image, Finset.mem_univ, true_and,
      mem_points_some]
    constructor
    · rintro ⟨e, he⟩
      have hdir : e = some m := congrArg Prod.fst he
      subst e
      have hb : p.2 - m * p.1 = b := congrArg Prod.snd he
      linear_combination hb
    · intro h
      refine ⟨some m, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [lineThrough]
        linear_combination h

@[simp] theorem linesThrough_card (p : Point q) :
    (linesThrough p).card = q + 1 := by
  rw [linesThrough, Finset.card_image_of_injective _ (lineThrough_injective p)]
  simp [Fintype.card_option, ZMod.card]

/-- Two different points determine at most one affine line. -/
theorem line_eq_of_two_points {p r : Point q} (hpr : p ≠ r)
    {l m : Line q} (hpl : p ∈ points l) (hrl : r ∈ points l)
    (hpm : p ∈ points m) (hrm : r ∈ points m) : l = m := by
  rcases l with ⟨d, b⟩
  rcases m with ⟨e, c⟩
  cases d with
  | none =>
    simp only [mem_points_none] at hpl hrl
    cases e with
    | none =>
      simp only [mem_points_none] at hpm hrm
      have : b = c := hpl.symm.trans hpm
      simp [this]
    | some a =>
      simp only [mem_points_some] at hpm hrm
      exfalso
      apply hpr
      apply Prod.ext (hpl.trans hrl.symm)
      calc
        p.2 = a * p.1 + c := hpm
        _ = a * r.1 + c := by rw [hpl, hrl]
        _ = r.2 := hrm.symm
  | some a =>
    simp only [mem_points_some] at hpl hrl
    cases e with
    | none =>
      simp only [mem_points_none] at hpm hrm
      exfalso
      apply hpr
      apply Prod.ext (hpm.trans hrm.symm)
      calc
        p.2 = a * p.1 + b := hpl
        _ = a * r.1 + b := by rw [hpm, hrm]
        _ = r.2 := hrl.symm
    | some a' =>
      simp only [mem_points_some] at hpm hrm
      have hprod : (a - a') * (p.1 - r.1) = 0 := by
        linear_combination -hpl + hrl + hpm - hrm
      rcases mul_eq_zero.mp hprod with haa | hxx
      · have ha : a = a' := sub_eq_zero.mp haa
        subst a'
        have hb : b = c := by linear_combination -hpl + hpm
        subst c
        rfl
      · exfalso
        apply hpr
        have hx : p.1 = r.1 := sub_eq_zero.mp hxx
        apply Prod.ext hx
        calc
          p.2 = a * p.1 + b := hpl
          _ = a * r.1 + b := by rw [hx]
          _ = r.2 := hrl.symm

/-- Existence is proved by the elementary slope/intercept formula. -/
theorem exists_line (p r : Point q) :
    ∃ l : Line q, p ∈ points l ∧ r ∈ points l := by
  by_cases hx : p.1 = r.1
  · exact ⟨(none, p.1), by simp, by simpa using hx.symm⟩
  · let a : ZMod q := (r.2 - p.2) / (r.1 - p.1)
    have hden : r.1 - p.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have ha : a * (r.1 - p.1) = r.2 - p.2 := by
      dsimp [a]
      exact div_mul_cancel₀ _ hden
    refine ⟨(some a, p.2 - a * p.1), ?_, ?_⟩
    · simp only [mem_points_some]
      ring
    · simp only [mem_points_some]
      linear_combination -ha

/-- Every distinct pair belongs to exactly one line. -/
theorem existsUnique_line (p r : Point q) (hpr : p ≠ r) :
    ∃! l : Line q, p ∈ points l ∧ r ∈ points l := by
  obtain ⟨l, hpl, hrl⟩ := exists_line p r
  refine ⟨l, ⟨hpl, hrl⟩, ?_⟩
  intro m hm
  exact line_eq_of_two_points hpr hm.1 hm.2 hpl hrl

/-- Distinct lines share at most one point. -/
theorem intersection_card_le_one {l m : Line q} (hlm : l ≠ m) :
    (points l ∩ points m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  by_contra hpr
  exact hlm (line_eq_of_two_points hpr
    (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hr).1
    (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hr).2)

/-- Count point-line incidences over a finite set of points. -/
theorem sum_trace_card (X : Finset (Point q)) :
    ∑ l : Line q, (points l ∩ X).card = (q + 1) * X.card := by
  classical
  calc
    ∑ l : Line q, (points l ∩ X).card =
        ∑ l : Line q, ∑ p ∈ X, if p ∈ points l then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      have hfilter : points l ∩ X = X.filter (fun p => p ∈ points l) := by
        ext p
        simp [and_comm]
      rw [hfilter, Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ p ∈ X, ∑ l : Line q, if p ∈ points l then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _p ∈ X, (q + 1) := by
      apply Finset.sum_congr rfl
      intro p _
      have h : Finset.univ.filter (fun l : Line q => p ∈ points l) =
          linesThrough p := by
        ext l
        simp
      have hcard : (Finset.univ.filter (fun l : Line q => p ∈ points l)).card =
          q + 1 := by rw [h, linesThrough_card]
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using hcard
    _ = (q + 1) * X.card := by simp [Nat.mul_comm]

/-- A genuine exact pairwise-balanced design; the blocks are sets, and
`pair_exactly_once` quantifies over distinct points of the actual ground set. -/
structure ExactPairwiseDesign (V : Type*) [DecidableEq V] where
  ground : Finset V
  blocks : Finset (Finset V)
  block_subset : ∀ B ∈ blocks, B ⊆ ground
  block_card_ge_two : ∀ B ∈ blocks, 2 ≤ B.card
  pair_exactly_once : ∀ x ∈ ground, ∀ y ∈ ground, x ≠ y →
    ∃! B, B ∈ blocks ∧ x ∈ B ∧ y ∈ B

/-- Traces on a retained point set. Empty and singleton traces are excluded
by the hypothesis of the eventual design construction, not silently removed. -/
def traces (R : Finset (Point q)) : Finset (Finset (Point q)) :=
  Finset.univ.image (fun l : Line q => points l ∩ R)

/-- A trace containing at least two points remembers its unique ambient line. -/
theorem trace_injective (R : Finset (Point q))
    (hR : ∀ l : Line q, 2 ≤ (points l ∩ R).card) :
    Function.Injective (fun l : Line q => points l ∩ R) := by
  intro l m hlm
  change points l ∩ R = points m ∩ R at hlm
  by_contra hne
  have hsub : points l ∩ R ⊆ points l ∩ points m := by
    intro p hp
    refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1, ?_⟩
    have hp' : p ∈ points m ∩ R := by rw [← hlm]; exact hp
    exact (Finset.mem_inter.mp hp').1
  have hle := (Finset.card_le_card hsub).trans (intersection_card_le_one hne)
  have := hR l
  omega

@[simp] theorem traces_card (R : Finset (Point q))
    (hR : ∀ l : Line q, 2 ≤ (points l ∩ R).card) :
    (traces R).card = q * (q + 1) := by
  rw [traces, Finset.card_image_of_injective _ (trace_injective R hR)]
  simp [Nat.mul_comm]

/-- The retained construction is exact, including uniqueness among actual
blocks, with no multiset multiplicities or duplicate trace blocks. -/
def exact_pairwise_design (R : Finset (Point q))
    (hR : ∀ l : Line q, 2 ≤ (points l ∩ R).card) :
    ExactPairwiseDesign (Point q) where
  ground := R
  blocks := traces R
  block_subset := by
    intro B hB
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.inter_subset_right
  block_card_ge_two := by
    intro B hB
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
    exact hR l
  pair_exactly_once := by
    intro x hx y hy hxy
    obtain ⟨l, hl, huniq⟩ := existsUnique_line x y hxy
    refine ⟨points l ∩ R, ?_, ?_⟩
    · exact ⟨Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩,
        Finset.mem_inter.mpr ⟨hl.1, hx⟩, Finset.mem_inter.mpr ⟨hl.2, hy⟩⟩
    · intro B hB
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hB.1
      have hm : m = l := huniq m
        ⟨(Finset.mem_inter.mp hB.2.1).1, (Finset.mem_inter.mp hB.2.2).1⟩
      rw [hm]

/-- The retained ground set has at most the number of ambient points. -/
theorem retained_card_le (R : Finset (Point q)) : R.card ≤ q ^ 2 := by
  simpa only [point_card] using Finset.card_le_univ R

/-- Lower bounds on ambient traces are exactly lower bounds on every actual
block of the retained exact design. -/
theorem traces_card_lower (R : Finset (Point q)) (b : ℕ)
    (hR : ∀ l : Line q, b ≤ (points l ∩ R).card)
    {B : Finset (Point q)} (hB : B ∈ traces R) : b ≤ B.card := by
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hB
  exact hR l

/-- No line contains `k` members of a `k`-arc. -/
def IsArc (k : ℕ) (A : Finset (Point q)) : Prop :=
  ∀ l : Line q, (A ∩ points l).card < k

/-- The final contradiction uses precisely k=K+2, for arbitrary K. -/
theorem arc_of_trace_intersection_bound (R Q : Finset (Point q)) (K : ℕ)
    (hQR : Q ⊆ R)
    (hbound : ∀ B ∈ traces R, (Q ∩ B).card ≤ K) : IsArc (K + 2) Q := by
  intro l
  have hB : points l ∩ R ∈ traces R :=
    Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  have hQ : Q ∩ (points l ∩ R) = Q ∩ points l := by
    ext p
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hpQ, hpL, _⟩
      exact ⟨hpQ, hpL⟩
    · rintro ⟨hpQ, hpL⟩
      exact ⟨hpQ, hpL, hQR hpQ⟩
  have h := hbound _ hB
  rw [hQ] at h
  omega

end Affine
end JSP539
