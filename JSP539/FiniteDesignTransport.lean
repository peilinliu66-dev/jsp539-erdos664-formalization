/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original finite reindexing proofs. No external problem formalization is imported.
-/
import JSP539.AffinePlane

namespace JSP539
namespace Affine
namespace ExactPairwiseDesign

variable {V : Type*} [DecidableEq V] (D : ExactPairwiseDesign V)

/-- The actual point represented by a finite label. -/
noncomputable def point (x : Fin D.ground.card) : V :=
  (D.ground.equivFin.symm x).val

theorem point_mem (x : Fin D.ground.card) : D.point x ∈ D.ground :=
  (D.ground.equivFin.symm x).property

theorem point_injective : Function.Injective D.point := by
  intro x y h
  exact D.ground.equivFin.symm.injective (Subtype.ext h)

@[simp] theorem point_label (x : V) (hx : x ∈ D.ground) :
    D.point (D.ground.equivFin ⟨x, hx⟩) = x := by
  simp [point]

/-- The block represented by a finite index. The enumeration has no duplicates. -/
noncomputable def originalBlock (i : Fin D.blocks.card) : Finset V :=
  (D.blocks.equivFin.symm i).val

theorem originalBlock_mem (i : Fin D.blocks.card) : D.originalBlock i ∈ D.blocks :=
  (D.blocks.equivFin.symm i).property

theorem originalBlock_injective : Function.Injective D.originalBlock := by
  intro i j h
  exact D.blocks.equivFin.symm.injective (Subtype.ext h)

theorem exists_index {B : Finset V} (hB : B ∈ D.blocks) :
    ∃ i : Fin D.blocks.card, D.originalBlock i = B := by
  refine ⟨D.blocks.equivFin ⟨B, hB⟩, ?_⟩
  simp [originalBlock]

/-- Pull a set back along the actual bijection from finite labels to points. -/
noncomputable def relabel (B : Finset V) : Finset (Fin D.ground.card) :=
  Finset.univ.filter (fun x => D.point x ∈ B)

@[simp] theorem mem_relabel (B : Finset V) (x : Fin D.ground.card) :
    x ∈ D.relabel B ↔ D.point x ∈ B := by
  simp [relabel]

theorem relabel_card (B : Finset V) (hB : B ⊆ D.ground) :
    (D.relabel B).card = B.card := by
  classical
  refine Finset.card_bij (fun x _ => D.point x) ?_ ?_ ?_
  · intro x hx
    exact (D.mem_relabel B x).mp hx
  · intro x hx y hy hxy
    exact D.point_injective hxy
  · intro x hx
    refine ⟨D.ground.equivFin ⟨x, hB hx⟩, ?_, ?_⟩
    · exact (D.mem_relabel B _).mpr (by simpa using hx)
    · simp

/-- The indexed family on `Fin ground.card` required by the original question. -/
noncomputable def indexedBlock (i : Fin D.blocks.card) : Finset (Fin D.ground.card) :=
  D.relabel (D.originalBlock i)

@[simp] theorem mem_indexedBlock (i : Fin D.blocks.card) (x : Fin D.ground.card) :
    x ∈ D.indexedBlock i ↔ D.point x ∈ D.originalBlock i := by
  exact D.mem_relabel _ _

theorem indexedBlock_card (i : Fin D.blocks.card) :
    (D.indexedBlock i).card = (D.originalBlock i).card :=
  D.relabel_card _ (D.block_subset _ (D.originalBlock_mem i))

theorem indexedBlock_card_ge_two (i : Fin D.blocks.card) :
    2 ≤ (D.indexedBlock i).card := by
  rw [D.indexedBlock_card]
  exact D.block_card_ge_two _ (D.originalBlock_mem i)

/-- Send a candidate transversal back to the original ground set. -/
noncomputable def lift (Q : Finset (Fin D.ground.card)) : Finset V :=
  Q.image D.point

theorem lift_subset (Q : Finset (Fin D.ground.card)) : D.lift Q ⊆ D.ground := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact D.point_mem y

theorem lift_card (Q : Finset (Fin D.ground.card)) : (D.lift Q).card = Q.card := by
  exact Finset.card_image_of_injective _ D.point_injective

theorem lift_inter (Q : Finset (Fin D.ground.card)) (B : Finset V) :
    D.lift (Q ∩ D.relabel B) = D.lift Q ∩ B := by
  classical
  ext x
  simp only [lift, Finset.mem_image, Finset.mem_inter, mem_relabel]
  constructor
  · rintro ⟨y, ⟨hy, hyB⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, hyB⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyB⟩
    exact ⟨y, ⟨hy, hyB⟩, rfl⟩

theorem lift_inter_card (Q : Finset (Fin D.ground.card)) (B : Finset V) :
    (D.lift Q ∩ B).card = (Q ∩ D.relabel B).card := by
  rw [← D.lift_inter, D.lift_card]

/-- Exact incidence is transported to uniqueness of an index, not merely of a set. -/
theorem indexed_pair_exactly_once (x y : Fin D.ground.card) (hxy : x ≠ y) :
    ∃! i : Fin D.blocks.card, x ∈ D.indexedBlock i ∧ y ∈ D.indexedBlock i := by
  have hpoints : D.point x ≠ D.point y := fun h => hxy (D.point_injective h)
  obtain ⟨B, hB, huniq⟩ :=
    D.pair_exactly_once _ (D.point_mem x) _ (D.point_mem y) hpoints
  obtain ⟨i, hi⟩ := D.exists_index hB.1
  refine ⟨i, ?_, ?_⟩
  · constructor
    · exact (D.mem_indexedBlock i x).mpr (hi.symm ▸ hB.2.1)
    · exact (D.mem_indexedBlock i y).mpr (hi.symm ▸ hB.2.2)
  · intro j hj
    apply D.originalBlock_injective
    exact (huniq _ ⟨D.originalBlock_mem j,
      (D.mem_indexedBlock j x).mp hj.1,
      (D.mem_indexedBlock j y).mp hj.2⟩).trans hi.symm

/-- Exact pair uniqueness itself forces two distinct actual blocks to meet in at
most one point; the minimum block size is not needed for this implication. -/
theorem block_intersection_card_le_one {B C : Finset V}
    (hB : B ∈ D.blocks) (hC : C ∈ D.blocks) (hBC : B ≠ C) :
    (B ∩ C).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨E, hE, huniq⟩ := D.pair_exactly_once x
    (D.block_subset B hB (Finset.mem_inter.mp hx).1) y
    (D.block_subset B hB (Finset.mem_inter.mp hy).1) hxy
  apply hBC
  exact (huniq B ⟨hB, (Finset.mem_inter.mp hx).1,
    (Finset.mem_inter.mp hy).1⟩).trans
    (huniq C ⟨hC, (Finset.mem_inter.mp hx).2,
      (Finset.mem_inter.mp hy).2⟩).symm

theorem indexed_intersection_card_le_one (i j : Fin D.blocks.card) (hij : i ≠ j) :
    (D.indexedBlock i ∩ D.indexedBlock j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  obtain ⟨k, hk, huniq⟩ := D.indexed_pair_exactly_once x y hxy
  apply hij
  exact (huniq i ⟨(Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hy).1⟩).trans
    (huniq j ⟨(Finset.mem_inter.mp hx).2, (Finset.mem_inter.mp hy).2⟩).symm

/-- Fully finite transport, preserving sizes, exact pair coverage, linearity,
and the obstruction for every candidate transversal. Both finite enumerations
are constructed with `Finset.equivFin`; no isomorphism is assumed. -/
theorem exists_fin_indexed (c : ℝ) (K : ℕ)
    (hlarge : ∀ B ∈ D.blocks, c * Real.sqrt (D.ground.card : ℝ) < (B.card : ℝ))
    (hbad : ∀ Q : Finset V, Q ⊆ D.ground →
      (∀ B ∈ D.blocks, (Q ∩ B).Nonempty) → ∃ B ∈ D.blocks, K < (Q ∩ B).card) :
    ∃ (n m : ℕ) (A : Fin m → Finset (Fin n)),
      n = D.ground.card ∧ m = D.blocks.card ∧
      (∀ i, c * Real.sqrt (n : ℝ) < ((A i).card : ℝ)) ∧
      (∀ x y : Fin n, x ≠ y → ∃! i, x ∈ A i ∧ y ∈ A i) ∧
      (∀ i j, i ≠ j → (A i ∩ A j).card ≤ 1) ∧
      (∀ Q : Finset (Fin n), (∀ i, (Q ∩ A i).Nonempty) →
        ∃ i, K < (Q ∩ A i).card) := by
  classical
  refine ⟨D.ground.card, D.blocks.card, D.indexedBlock, rfl, rfl, ?_,
    D.indexed_pair_exactly_once, D.indexed_intersection_card_le_one, ?_⟩
  · intro i
    rw [D.indexedBlock_card]
    exact hlarge _ (D.originalBlock_mem i)
  · intro Q hQ
    have hmeet : ∀ B ∈ D.blocks, (D.lift Q ∩ B).Nonempty := by
      intro B hB
      obtain ⟨i, hi⟩ := D.exists_index hB
      apply Finset.card_pos.mp
      rw [D.lift_inter_card, ← hi]
      exact Finset.card_pos.mpr (hQ i)
    obtain ⟨B, hB, hbig⟩ := hbad (D.lift Q) (D.lift_subset Q) hmeet
    obtain ⟨i, hi⟩ := D.exists_index hB
    refine ⟨i, ?_⟩
    change K < (Q ∩ D.relabel (D.originalBlock i)).card
    rw [hi, ← D.lift_inter_card Q B]
    exact hbig

end ExactPairwiseDesign
end Affine
end JSP539
