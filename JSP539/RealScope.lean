/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Explicit real-valued bound adapters for the two original formulations.
The only new step is ceiling a proposed real intersection bound.
Pinned compilation and verification records are in VERIFICATION.md.
-/
import JSP539.OriginalScope

namespace JSP539

/-- The counterexample excludes every real bound, with arbitrarily large
ground sets. The ceiling conversion is part of the source theorem. -/
theorem exists_bad_fin_design_real (K : ℝ) (n0 : ℕ) :
    ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      n0 ≤ n ∧
      (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) ∧
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) ∧
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) ∧
      (∀ Q : Finset (Fin n), (∀ i, (Q ∩ A i).Nonempty) →
        ∃ i, K < ((Q ∩ A i).card : ℝ)) := by
  obtain ⟨n, m, A, hn, hs, hp, hl, hb⟩ := exists_bad_fin_design ⌈K⌉₊ n0
  refine ⟨n, m, A, hn, hs, hp, hl, ?_⟩
  intro Q hQ
  obtain ⟨i, hi⟩ := hb Q hQ
  refine ⟨i, ?_⟩
  exact (Nat.le_ceil K).trans_lt (by exact_mod_cast hi)

namespace OriginalScope

/-- The at-most-once formulation, with the proposed universal bound in ℝ. -/
theorem erdos_664_real :
    ¬ (∀ c : ℝ, 0 < c → c < 1 → ∃ K : ℝ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, ((B ∩ A i).card : ℝ) ≤ K) := by
  intro h
  obtain ⟨K, hK⟩ := h (2 / 5) (by norm_num) (by norm_num)
  obtain ⟨n, m, A, hn, hs, hp, hl, hb⟩ := exists_bad_fin_design_real K 1
  obtain ⟨B, hmeet, hbound⟩ := hK n m A hs hl
  obtain ⟨i, hi⟩ := hb B hmeet
  exact (not_lt_of_ge (hbound i)) hi

/-- The exact-pair 1981 formulation, with the proposed universal bound in ℝ. -/
theorem block_design_real :
    ¬ (∀ c : ℝ, 0 < c → ∃ K : ℝ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, ((B ∩ A i).card : ℝ) ≤ K) := by
  intro h
  obtain ⟨K, hK⟩ := h (2 / 5) (by norm_num)
  obtain ⟨n, m, A, hn, hs, hp, hl, hb⟩ := exists_bad_fin_design_real K 1
  obtain ⟨B, hmeet, hbound⟩ := hK n m A hs hp
  obtain ⟨i, hi⟩ := hb B hmeet
  exact (not_lt_of_ge (hbound i)) hi

end OriginalScope
end JSP539
