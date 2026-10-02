import JSP539

/-!
Literal checks of the exact finite design and the two original uniform-bound
formulations. These declarations use the actual real-valued exported theorems.
They introduce no sample, container, external counterexample or axiom.
Actual execution records for this verification entry are in VERIFICATION.md.
-/

set_option pp.universes true
set_option pp.explicit true

theorem audit_literal_exact_design_unbounded_real :
    ∀ (K : ℝ) (n0 : ℕ),
      ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        n0 ≤ n ∧
        (∀ i, (2 / 5 : ℝ) * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) ∧
        (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) ∧
        (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) ∧
        (∀ Q : Finset (Fin n), (∀ i, (Q ∩ A i).Nonempty) →
          ∃ i, K < ((Q ∩ A i).card : ℝ)) := by
  intro K n0
  exact JSP539.exists_bad_fin_design_real K n0

theorem audit_literal_original_block_design_real :
    ¬ (∀ c : ℝ, 0 < c → ∃ K : ℝ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, ((B ∩ A i).card : ℝ) ≤ K) := by
  exact JSP539.OriginalScope.block_design_real

theorem audit_literal_family_formulation_real :
    ¬ (∀ c : ℝ, 0 < c → c < 1 → ∃ K : ℝ,
      ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
        (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) →
        (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) →
        ∃ B : Finset (Fin n), (∀ i, (B ∩ A i).Nonempty) ∧
          ∀ i, ((B ∩ A i).card : ℝ) ≤ K) := by
  exact JSP539.OriginalScope.erdos_664_real

#check audit_literal_exact_design_unbounded_real
#check audit_literal_original_block_design_real
#check audit_literal_family_formulation_real

#print axioms audit_literal_exact_design_unbounded_real
#print axioms audit_literal_original_block_design_real
#print axioms audit_literal_family_formulation_real
