/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

An elementary lower-tail estimate on the common finite fair-bit sample space.
The product formula is obtained by finite distributivity, and the tail bound
uses the finite Markov inequality. No concentration theorem is assumed.

Proof source; pinned execution records are in VERIFICATION.md., targeting Lean 4.35.0-rc3 and Mathlib
2a885768dae569d938bb9ff3474da6a8753bb90a.
-/
import JSP539.UniformBits

open scoped BigOperators Classical

namespace JSP539.FairBitTail

open FiniteProbability UniformBits

/-- Finite coordinate factorization for real-valued functions. This is an
identity of normalized sums on the full function space. -/
theorem average_prod_eq_prod_average
    {J A : Type*} [Fintype J] [DecidableEq J]
    [Fintype A] [DecidableEq A] (w : J → A → ℝ) :
    average (fun f : J → A => ∏ j : J, w j (f j)) =
      ∏ j : J, average (w j) := by
  unfold average
  rw [← Fintype.prod_sum]
  simp only [Fintype.card_fun, Nat.cast_pow, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact probability generating function of the number of retained
coordinates in a fixed finite set. Coordinates outside `S` have weight one. -/
theorem average_retainedCount_pow (S : Finset V) (r : ℝ) :
    average (fun f : Sample V => r ^ (S.filter (fun v => f v = true)).card) =
      ((1 + r) / 2) ^ S.card := by
  let w : V → Bool → ℝ :=
    fun v b => if v ∈ S then (if b = true then r else 1) else 1
  have hprod (f : Sample V) :
      (∏ v : V, w v (f v)) = r ^ (S.filter (fun v => f v = true)).card := by
    calc
      (∏ v : V, w v (f v)) =
          ∏ v ∈ S, if f v = true then r else 1 := by
        dsimp only [w]
        rw [Finset.prod_ite_mem_eq]
      _ = ∏ _v ∈ S.filter (fun v => f v = true), r := by
        rw [Finset.prod_filter]
      _ = r ^ (S.filter (fun v => f v = true)).card := by
        rw [Finset.prod_const]
  have hmean (v : V) :
      average (w v) = if v ∈ S then (1 + r) / 2 else 1 := by
    by_cases hv : v ∈ S <;>
      norm_num [average, w, hv, Fintype.univ_bool, add_comm]
  have h := average_prod_eq_prod_average w
  simp_rw [hprod, hmean] at h
  simpa only [Finset.prod_ite_mem_eq, Finset.prod_const] using h

/-- Exact finite moment-generating function, with no condition on the real
parameter. This average is over precisely `Sample V = V → Bool`. -/
theorem average_exp_neg_retainedCount (S : Finset V) (t : ℝ) :
    average (fun f : Sample V =>
      Real.exp (-t * ((S.filter (fun v => f v = true)).card : ℝ))) =
      ((1 + Real.exp (-t)) / 2) ^ S.card := by
  have hpoint (f : Sample V) :
      Real.exp (-t * ((S.filter (fun v => f v = true)).card : ℝ)) =
        Real.exp (-t) ^ (S.filter (fun v => f v = true)).card := by
    rw [mul_comm, Real.exp_nat_mul]
  simp_rw [hpoint]
  exact average_retainedCount_pow S (Real.exp (-t))

/-- The elementary exponential Markov bound for any nonnegative tilt and any
real cutoff. All probabilities refer to the common full finite sample space. -/
theorem fraction_retainedCount_le_markov (S : Finset V) {t : ℝ}
    (ht : 0 ≤ t) (a : ℝ) :
    fraction (fun f : Sample V =>
      ((S.filter (fun v => f v = true)).card : ℝ) ≤ a) ≤
      ((1 + Real.exp (-t)) / 2) ^ S.card / Real.exp (-t * a) := by
  let X : Sample V → ℝ := fun f =>
    Real.exp (-t * ((S.filter (fun v => f v = true)).card : ℝ))
  have hcover :
      fraction (fun f : Sample V =>
        ((S.filter (fun v => f v = true)).card : ℝ) ≤ a) ≤
      fraction (fun f : Sample V => Real.exp (-t * a) ≤ X f) := by
    apply fraction_mono
    intro f hf
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hf (neg_nonpos.mpr ht)
  have hmark := fraction_ge_le_average_div X
    (fun f => (Real.exp_pos _).le) (Real.exp_pos (-t * a))
  have hmoment : average X = ((1 + Real.exp (-t)) / 2) ^ S.card := by
    exact average_exp_neg_retainedCount S t
  rw [hmoment] at hmark
  exact hcover.trans hmark

/-- Under uniformly sampled independent fair bits on all of `V`, the chance
that at most two fifths of `S` survive is at most `exp (-|S| / 200)`.

The tilt is `log (11/10)`. Its one-coordinate moment is `21/22`, and the two
inequalities `log (11/10) ≤ 1/10` and `log (21/22) ≤ -1/22` give an exponent
at most `-3|S|/550 ≤ -|S|/200`. The statement includes the empty set. -/
theorem fraction_retainedCount_le_two_fifths (S : Finset V) :
    fraction (fun f : Sample V =>
      ((S.filter (fun v => f v = true)).card : ℝ) ≤
        (2 / 5 : ℝ) * (S.card : ℝ)) ≤
      Real.exp (-(S.card : ℝ) / 200) := by
  let t : ℝ := Real.log (11 / 10 : ℝ)
  have ht : 0 < t := by
    dsimp only [t]
    exact Real.log_pos (by norm_num)
  have ht_upper : t ≤ (1 / 10 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11 / 10)
    norm_num at h
    exact h
  have hlog : Real.log (21 / 22 : ℝ) ≤ -(1 / 22 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 21 / 22)
    norm_num at h
    exact h
  have htilt : Real.exp (-t) = (10 / 11 : ℝ) := by
    dsimp only [t]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 11 / 10)]
    norm_num
  have hmoment : (1 + Real.exp (-t)) / 2 = (21 / 22 : ℝ) := by
    rw [htilt]
    norm_num
  have hpow : (21 / 22 : ℝ) ^ S.card =
      Real.exp ((S.card : ℝ) * Real.log (21 / 22 : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 21 / 22)]
  have hn : (0 : ℝ) ≤ S.card := by positivity
  have hlog_mul := mul_le_mul_of_nonneg_left hlog hn
  have ht_mul := mul_le_mul_of_nonneg_right ht_upper hn
  calc
    fraction (fun f : Sample V =>
        ((S.filter (fun v => f v = true)).card : ℝ) ≤
          (2 / 5 : ℝ) * (S.card : ℝ)) ≤
        ((1 + Real.exp (-t)) / 2) ^ S.card /
          Real.exp (-t * ((2 / 5 : ℝ) * (S.card : ℝ))) :=
      fraction_retainedCount_le_markov S ht.le _
    _ = Real.exp ((S.card : ℝ) * Real.log (21 / 22 : ℝ) -
          (-t * ((2 / 5 : ℝ) * (S.card : ℝ)))) := by
      rw [hmoment, hpow, Real.exp_sub]
    _ ≤ Real.exp (-(S.card : ℝ) / 200) := by
      apply Real.exp_le_exp.mpr
      nlinarith

end JSP539.FairBitTail
