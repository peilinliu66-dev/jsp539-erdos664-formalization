/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

The full random restriction construction. Both bad-event families are counted
on the same space of fair point bits. Every numerical/container/probability
premise is discharged before the public existence theorem. Proof source; pinned execution records are in VERIFICATION.md..
-/
import JSP539.ArcContainerGrowth
import JSP539.FairBitTail
import JSP539.ProbabilityBudget

open Filter
open scoped BigOperators Classical Topology

namespace JSP539.Affine

open FiniteProbability UniformBits

variable {q : ℕ} [Fact q.Prime]

theorem points_inter_retained (l : Line q) (f : Sample (Point q)) :
    points l ∩ retained f = (points l).filter (fun p => f p = true) := by
  ext p
  simp

def SomeSmallLine (f : Sample (Point q)) : Prop :=
  ∃ l : Line q, ((points l ∩ retained f).card : ℝ) ≤ (2 / 5 : ℝ) * q

theorem fraction_someSmallLine_le :
    fraction (SomeSmallLine (q := q)) ≤ lineFailureBudget q := by
  calc
    _ ≤ ∑ l : Line q, fraction (fun f : Sample (Point q) =>
        ((points l ∩ retained f).card : ℝ) ≤ (2 / 5 : ℝ) * q) :=
      fraction_exists_le_sum _
    _ ≤ ∑ _l : Line q, Real.exp (-(q : ℝ) / 200) := by
      apply Finset.sum_le_sum
      intro l _
      simpa only [points_inter_retained, points_card] using
        FairBitTail.fraction_retainedCount_le_two_fifths (points l)
    _ = lineFailureBudget q := by
      simp [lineFailureBudget, line_card, Nat.cast_mul, Nat.cast_add, mul_comm]

/-- For an actual deterministic container family, both obstructions can be
avoided at once. No conditioning or inter-family independence is required. -/
theorem exists_good_retention (Cs : Finset (Finset (Point q))) (k : ℕ)
    (hk : 2 ≤ k) (hsize : ∀ C ∈ Cs, C.card ≤ 2 * k * q)
    (hcount : (Cs.card : ℝ) ≤ Real.exp ((hittingRate k / 2) * q))
    (hbudget : totalFailureBudget k q < 1) :
    ∃ f : Sample (Point q),
      (∀ l : Line q, (2 / 5 : ℝ) * q < ((points l ∩ retained f).card : ℝ)) ∧
      ¬ ∃ C ∈ Cs, ContainerHits C f := by
  obtain ⟨f, hC, hL⟩ := exists_neither_of_add_lt_one
    (fun f => ∃ C ∈ Cs, ContainerHits C f) SomeSmallLine
    (Real.exp (-(hittingRate k / 2) * q)) (lineFailureBudget q)
    (fraction_any_containerHits_le_exp Cs k hk hsize hcount)
    fraction_someSmallLine_le hbudget
  refine ⟨f, ?_, hC⟩
  intro l
  exact lt_of_not_ge (fun hl => hL ⟨l, hl⟩)

/-- A transversal with all block intersections bounded by K would be a
K+2-arc and force one of the excluded container events. -/
theorem retention_forces_large_intersection (Cs : Finset (Finset (Point q)))
    (K : ℕ)
    (hcover : ∀ Y : Finset (Point q), IsArc (K + 2) Y →
      ∃ C ∈ Cs, Y ⊆ C)
    (f : Sample (Point q)) (havoid : ¬ ∃ C ∈ Cs, ContainerHits C f)
    (Q : Finset (Point q)) (hQR : Q ⊆ retained f)
    (hQhit : ∀ B ∈ traces (retained f), (Q ∩ B).Nonempty) :
    ∃ B ∈ traces (retained f), K < (Q ∩ B).card := by
  by_contra hnot
  have hbound : ∀ B ∈ traces (retained f), (Q ∩ B).card ≤ K := by
    intro B hB
    exact Nat.le_of_not_gt (fun h => hnot ⟨B, hB, h⟩)
  have harc := arc_of_trace_intersection_bound (retained f) Q K hQR hbound
  obtain ⟨C, hC, hQC⟩ := hcover Q harc
  apply havoid
  refine ⟨C, hC, ?_⟩
  intro l
  have hB : points l ∩ retained f ∈ traces (retained f) :=
    Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  obtain ⟨v, hv⟩ := hQhit _ hB
  obtain ⟨hvQ, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨hvl, hvR⟩ := Finset.mem_inter.mp hvB
  exact ⟨v, Finset.mem_inter.mpr ⟨hQC hvQ, hvl⟩,
    (mem_retained f v).mp hvR⟩

/-- Unconditional finite construction for every proposed bound K, with
arbitrarily large ground sets. All lines are retained as blocks. -/
theorem exists_bad_exact_design (K n0 : ℕ) :
    ∃ q : ℕ, ∃ hp : q.Prime,
      letI : Fact q.Prime := ⟨hp⟩
      ∃ R : Finset (Point q),
        5 ≤ q ∧ n0 ≤ R.card ∧
        (∀ l : Line q, (2 / 5 : ℝ) * q < ((points l ∩ R).card : ℝ)) ∧
        (∀ Q : Finset (Point q), Q ⊆ R →
          (∀ B ∈ traces R, (Q ∩ B).Nonempty) →
          ∃ B ∈ traces R, K < (Q ∩ B).card) := by
  let k := K + 2
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hr : 0 < hittingRate k / 2 :=
    div_pos (hittingRate_pos k hk) (by norm_num)
  obtain ⟨qC, hqC⟩ := exists_arc_container_threshold k hk (hittingRate k / 2) hr
  obtain ⟨qP, hqP⟩ := eventually_atTop.1 (eventually_totalFailureBudget_lt_one k hk)
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (max qC (max qP (3 * n0 + 5)))
  have hqC' : qC ≤ q := (le_max_left _ _).trans hq
  have hqP' : qP ≤ q := (le_max_left _ _).trans ((le_max_right _ _).trans hq)
  have hq0 : 3 * n0 + 5 ≤ q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hq)
  letI : Fact q.Prime := ⟨hp⟩
  obtain ⟨Cs, hcover, hsize, hcount⟩ := hqC q hqC' hp
  obtain ⟨f, hline, havoid⟩ := exists_good_retention Cs k hk hsize hcount (hqP q hqP')
  refine ⟨q, hp, retained f, (by omega), ?_, hline, ?_⟩
  · have htrace := hline (none, 0)
    have hsub : points (none, (0 : ZMod q)) ∩ retained f ⊆ retained f :=
      Finset.inter_subset_right
    have hcard : ((points (none, (0 : ZMod q)) ∩ retained f).card : ℝ) ≤
        (retained f).card := by exact_mod_cast Finset.card_le_card hsub
    have hq0R : (3 : ℝ) * n0 + 5 ≤ q := by exact_mod_cast hq0
    have hnR : (n0 : ℝ) ≤ (retained f).card := by
      nlinarith [show (0 : ℝ) ≤ n0 by positivity]
    exact_mod_cast hnR
  · intro Q hQR hQhit
    exact retention_forces_large_intersection Cs K hcover f havoid Q hQR hQhit

end JSP539.Affine
