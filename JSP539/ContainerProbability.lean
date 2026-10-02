/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

All container events live on one uniform point-retention experiment. The
exponential bound is obtained from actual disjoint traces, not an independence
assumption about arbitrary lines. Proof source; pinned execution records are in VERIFICATION.md..
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import JSP539.ShortTraces
import JSP539.UniformBits

open scoped BigOperators Classical

namespace JSP539.Affine

open FiniteProbability UniformBits

variable {q : ℕ} [Fact q.Prime]

/-- A positive constant depending only on the proposed transversal bound. -/
noncomputable def hittingRate (k : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (4 * k) / (16 * k)

theorem hittingRate_pos (k : ℕ) (hk : 2 ≤ k) : 0 < hittingRate k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  unfold hittingRate
  positivity

/-- Retain each actual point according to its own fair coordinate. -/
def retained (f : Sample (Point q)) : Finset (Point q) :=
  Finset.univ.filter (fun p => f p = true)

@[simp] theorem mem_retained (f : Sample (Point q)) (p : Point q) :
    p ∈ retained f ↔ f p = true := by simp [retained]

/-- The retained part of the deterministic container meets every ambient line. -/
def ContainerHits (C : Finset (Point q)) (f : Sample (Point q)) : Prop :=
  ∀ l : Line q, hits (shortTrace C l) f

theorem half_pow_antitone {a b : ℕ} (hab : a ≤ b) :
    (1 / 2 : ℝ) ^ b ≤ (1 / 2 : ℝ) ^ a := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hd : (1 / 2 : ℝ) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha : 0 ≤ (1 / 2 : ℝ) ^ a := by positivity
  nlinarith

/-- Exact fair-coordinate independence plus the finite geometric packing
gives a bound for every one of the containers, uniformly over its shape. -/
theorem fraction_containerHits_le (C : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hC : C.card ≤ 2 * k * q) :
    fraction (ContainerHits C) ≤ Real.exp (-hittingRate k * q) := by
  rcases short_traces_or_packing C k hk hC with hempty | hpacking
  · obtain ⟨l, hl⟩ := hempty
    have hzero : ContainerHits C = (fun _ => False) := by
      funext f
      apply propext
      constructor
      · intro hf
        have h := hf l
        simpa [hits, hl] using h
      · exact False.elim
    rw [hzero, fraction_false]
    exact (Real.exp_pos _).le
  · obtain ⟨I, hsep, hsize, hcard⟩ := hpacking
    let a : ℝ := (1 / 2 : ℝ) ^ (4 * k)
    have ha : 0 < a := by dsimp [a]; positivity
    have hfactor (l : Line q) (hl : l ∈ I) :
        1 - (1 / 2 : ℝ) ^ (shortTrace C l).card ≤ Real.exp (-a) := by
      have hpower : a ≤ (1 / 2 : ℝ) ^ (shortTrace C l).card :=
        half_pow_antitone (hsize l hl).2
      have hexp := Real.add_one_le_exp (-a)
      linarith
    have hfactor_nonneg (l : Line q) (_hl : l ∈ I) :
        0 ≤ 1 - (1 / 2 : ℝ) ^ (shortTrace C l).card := by
      have hp : (1 / 2 : ℝ) ^ (shortTrace C l).card ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hcardR : (q : ℝ) ≤ 16 * (k : ℝ) * I.card := by exact_mod_cast hcard
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hscale : hittingRate k * q ≤ a * I.card := by
      dsimp [hittingRate]
      change a / (16 * (k : ℝ)) * q ≤ a * I.card
      have hdiv : (q : ℝ) / (16 * (k : ℝ)) ≤ I.card :=
        (div_le_iff₀ (by positivity)).mpr (by nlinarith [hcardR])
      calc
        a / (16 * (k : ℝ)) * q = a * ((q : ℝ) / (16 * (k : ℝ))) := by ring
        _ ≤ a * I.card := mul_le_mul_of_nonneg_left hdiv ha.le
    calc
      fraction (ContainerHits C) ≤ fraction (fun f => ∀ l ∈ I,
          hits (shortTrace C l) f) :=
        fraction_mono _ _ (fun f hf l _ => hf l)
      _ = ∏ l ∈ I, (1 - (1 / 2 : ℝ) ^ (shortTrace C l).card) :=
        fraction_hits_all (shortTrace C) I hsep
      _ ≤ ∏ _l ∈ I, Real.exp (-a) :=
        Finset.prod_le_prod₀ hfactor_nonneg hfactor
      _ = Real.exp (-(a * I.card)) := by
        simp only [Finset.prod_const]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ Real.exp (-hittingRate k * q) := by
        apply Real.exp_le_exp.mpr
        linarith

/-- The union bound is over the entire finite container family. -/
theorem fraction_any_containerHits_le (Cs : Finset (Finset (Point q))) (k : ℕ)
    (hk : 2 ≤ k) (hsize : ∀ C ∈ Cs, C.card ≤ 2 * k * q) :
    fraction (fun f => ∃ C ∈ Cs, ContainerHits C f) ≤
      (Cs.card : ℝ) * Real.exp (-hittingRate k * q) := by
  calc
    _ ≤ ∑ C ∈ Cs, fraction (ContainerHits C) :=
      fraction_le_sum_of_cover Cs _ ContainerHits (by
        intro f hf
        exact hf)
    _ ≤ ∑ _C ∈ Cs, Real.exp (-hittingRate k * q) :=
      Finset.sum_le_sum (fun C hC => fraction_containerHits_le C k hk (hsize C hC))
    _ = _ := by simp

theorem fraction_any_containerHits_le_exp (Cs : Finset (Finset (Point q)))
    (k : ℕ) (hk : 2 ≤ k) (hsize : ∀ C ∈ Cs, C.card ≤ 2 * k * q)
    (hcount : (Cs.card : ℝ) ≤ Real.exp ((hittingRate k / 2) * q)) :
    fraction (fun f => ∃ C ∈ Cs, ContainerHits C f) ≤
      Real.exp (-(hittingRate k / 2) * q) := by
  calc
    _ ≤ (Cs.card : ℝ) * Real.exp (-hittingRate k * q) :=
      fraction_any_containerHits_le Cs k hk hsize
    _ ≤ Real.exp ((hittingRate k / 2) * q) * Real.exp (-hittingRate k * q) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = Real.exp (-(hittingRate k / 2) * q) := by
      rw [← Real.exp_add]
      congr 1
      ring

end JSP539.Affine
