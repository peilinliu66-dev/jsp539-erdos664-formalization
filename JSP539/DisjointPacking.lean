/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

A finite maximal-packing argument. This is the elementary replacement for
Janson's inequality in the fixed-K specialization. No compilation has run.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open scoped BigOperators Classical

namespace JSP539.DisjointPacking

variable {L V : Type*} [DecidableEq L] [DecidableEq V]

def PairwiseDisjoint (A : L → Finset V) (I : Finset L) : Prop :=
  ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)

noncomputable def neighbours (A : L → Finset V) (T : Finset L) (i : L) : Finset L :=
  T.filter fun j => ¬ Disjoint (A i) (A j)

/-- The intersection graph of sets of size at most s, with point multiplicity
at most d, has closed-neighbourhood sizes at most s*d. -/
theorem neighbours_card_le (A : L → Finset V) (T : Finset L) (i : L)
    (s d : ℕ) (hsize : (A i).card ≤ s)
    (hdegree : ∀ x ∈ A i, (T.filter fun j => x ∈ A j).card ≤ d) :
    (neighbours A T i).card ≤ s * d := by
  have hcover : neighbours A T i ⊆
      (A i).biUnion (fun x => T.filter fun j => x ∈ A j) := by
    intro j hj
    obtain ⟨hjT, hnot⟩ := Finset.mem_filter.mp hj
    have hex : ∃ x, x ∈ A i ∧ x ∈ A j := by
      by_contra hn
      apply hnot
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      exact hn ⟨x, hxi, hxj⟩
    obtain ⟨x, hxi, hxj⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨x, hxi, Finset.mem_filter.mpr ⟨hjT, hxj⟩⟩
  calc
    (neighbours A T i).card ≤
        ((A i).biUnion (fun x => T.filter fun j => x ∈ A j)).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ x ∈ A i, (T.filter fun j => x ∈ A j).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ A i, d := Finset.sum_le_sum fun x hx => hdegree x hx
    _ = (A i).card * d := by simp
    _ ≤ s * d := Nat.mul_le_mul_right d hsize

/-- A maximum pairwise-disjoint subfamily covers every nonempty input set by
intersection. Counting those intersection neighbourhoods gives the bound. -/
theorem exists_packing_of_neighbour_bound (A : L → Finset V) (T : Finset L)
    (B : ℕ) (hne : ∀ i ∈ T, (A i).Nonempty)
    (hbound : ∀ i ∈ T, (neighbours A T i).card ≤ B) :
    ∃ I : Finset L, I ⊆ T ∧ PairwiseDisjoint A I ∧ T.card ≤ I.card * B := by
  let choices := T.powerset.filter (PairwiseDisjoint A)
  have hempty : (∅ : Finset L) ∈ choices := by
    simp [choices, PairwiseDisjoint]
  obtain ⟨I, hI, hmax⟩ :=
    Finset.exists_max_image choices Finset.card ⟨∅, hempty⟩
  have hIT : I ⊆ T := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  have hIsep : PairwiseDisjoint A I := (Finset.mem_filter.mp hI).2
  have hcovered : ∀ j ∈ T, ∃ i ∈ I, ¬ Disjoint (A i) (A j) := by
    intro j hjT
    by_contra hn
    have hjdis : ∀ i ∈ I, Disjoint (A i) (A j) := by
      intro i hi
      by_contra hdis
      exact hn ⟨i, hi, hdis⟩
    have hjI : j ∉ I := by
      intro hj
      obtain ⟨x, hx⟩ := hne j hjT
      exact (Finset.disjoint_left.mp (hjdis j hj)) hx hx
    have hinsertT : insert j I ⊆ T := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hjT
      · exact hIT hz
    have hinsertSep : PairwiseDisjoint A (insert j I) := by
      intro i hi z hz hiz
      rcases Finset.mem_insert.mp hi with rfl | hiI
      · have hzI : z ∈ I := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hiz)
        exact (hjdis z hzI).symm
      · rcases Finset.mem_insert.mp hz with rfl | hzI
        · exact hjdis i hiI
        · exact hIsep i hiI z hzI hiz
    have hinsert : insert j I ∈ choices :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hinsertT, hinsertSep⟩
    have hcard := hmax (insert j I) hinsert
    rw [Finset.card_insert_of_notMem hjI] at hcard
    omega
  have hcover : T ⊆ I.biUnion (neighbours A T) := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := hcovered j hj
    exact Finset.mem_biUnion.mpr
      ⟨i, hi, Finset.mem_filter.mpr ⟨hj, hij⟩⟩
  refine ⟨I, hIT, hIsep, ?_⟩
  calc
    T.card ≤ (I.biUnion (neighbours A T)).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ I, (neighbours A T i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum fun i hi => hbound i (hIT hi)
    _ = I.card * B := by simp

/-- The version used for short traces of affine lines. -/
theorem exists_disjoint_packing (A : L → Finset V) (T : Finset L) (s d : ℕ)
    (hne : ∀ i ∈ T, (A i).Nonempty)
    (hsize : ∀ i ∈ T, (A i).card ≤ s)
    (hdegree : ∀ x : V, (T.filter fun j => x ∈ A j).card ≤ d) :
    ∃ I : Finset L, I ⊆ T ∧ PairwiseDisjoint A I ∧ T.card ≤ I.card * (s * d) := by
  apply exists_packing_of_neighbour_bound A T (s * d) hne
  intro i hi
  exact neighbours_card_le A T i s d (hsize i hi) (fun x _ => hdegree x)

end JSP539.DisjointPacking
