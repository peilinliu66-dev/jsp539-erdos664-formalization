/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original proofs of the fully quantified finite statements. The problem scope
was checked against the public Erdős 664 statement; its source is not imported.
-/
import JSP539.RandomRestriction
import JSP539.FiniteDesignTransport

namespace JSP539

/-- For every proposed intersection bound, and every requested minimum ground
size, there is an actual indexed finite family violating the bound. The family
has strict two-fifths square-root block size, exact distinct-pair coverage, and
pairwise intersections at most one. -/
theorem exists_bad_fin_design (K n0 : ℕ) :
    ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      n0 ≤ n ∧
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) ∧
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) ∧
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) ∧
      (∀ Q : Finset (Fin n), (∀ i, (Q ∩ A i).Nonempty) →
        ∃ i, K < (Q ∩ A i).card) := by
  classical
  obtain ⟨q, hp, hretained⟩ := Affine.exists_bad_exact_design K n0
  letI : Fact q.Prime := ⟨hp⟩
  obtain ⟨R, hq, hn0, hlarge, hbad⟩ := hretained
  have hge : ∀ l : Affine.Line q, 2 ≤ (Affine.points l ∩ R).card := by
    intro l
    have hqR : (5 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have htwo : (2 : ℝ) < ((Affine.points l ∩ R).card : ℝ) := by
      nlinarith [hlarge l]
    have htwoNat : 2 < (Affine.points l ∩ R).card := by exact_mod_cast htwo
    omega
  have hsqrt : Real.sqrt (R.card : ℝ) ≤ (q : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    exact_mod_cast Affine.retained_card_le R
  let D : Affine.ExactPairwiseDesign (Affine.Point q) :=
    Affine.exact_pairwise_design R hge
  have hlargeD : ∀ B ∈ D.blocks,
      (2 / 5 : ℝ) * Real.sqrt (D.ground.card : ℝ) < (B.card : ℝ) := by
    intro B hB
    change B ∈ Affine.traces R at hB
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hB
    change (2 / 5 : ℝ) * Real.sqrt (R.card : ℝ) <
      ((Affine.points l ∩ R).card : ℝ)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (hlarge l)
  obtain ⟨n, m, A, hn, hm, hsize, hpairs, hinter, hobstruction⟩ :=
    D.exists_fin_indexed (2 / 5) K hlargeD hbad
  refine ⟨n, m, A, ?_, hsize, hpairs, hinter, hobstruction⟩
  rw [hn]
  exact hn0

namespace OriginalScope

/-- The explicit c = 2/5 version of the original linear-family question has a
negative answer. Every natural-number bound K is ruled out. -/
theorem two_fifths :
    ¬ ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
      ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
        ∀ i, (B ∩ A i).card ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨n, m, A, hn, hlarge, hpairs, hinter, hbad⟩ := exists_bad_fin_design K 0
  obtain ⟨B, hmeet, hbound⟩ := hK n m A hlarge hinter
  obtain ⟨i, hi⟩ := hbad B hmeet
  exact (not_lt_of_ge (hbound i)) hi

/-- The original question, with 0 < c < 1, is false in its full quantifier scope. -/
theorem erdos_664 :
    ¬ (∀ c : ℝ, 0 < c → c < 1 → ∃ K : ℕ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K) := by
  intro h
  exact two_fifths (h (2 / 5) (by norm_num) (by norm_num))

/-- The same explicit constant rules out a bound even when every distinct
point pair is contained in exactly one indexed block. -/
theorem two_fifths_exact_pairs :
    ¬ ∃ K : ℕ, ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
      ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
        ∀ i, (B ∩ A i).card ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨n, m, A, hn, hlarge, hpairs, hinter, hbad⟩ := exists_bad_fin_design K 0
  obtain ⟨B, hmeet, hbound⟩ := hK n m A hlarge hpairs
  obtain ⟨i, hi⟩ := hbad B hmeet
  exact (not_lt_of_ge (hbound i)) hi

/-- The exact-pair block-design question is false with its original quantifiers,
including the absence of an upper restriction on c. -/
theorem block_design :
    ¬ (∀ c : ℝ, 0 < c → ∃ K : ℕ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, (B ∩ A i).card ≤ K) := by
  intro h
  exact two_fifths_exact_pairs (h (2 / 5) (by norm_num))

end OriginalScope
end JSP539
