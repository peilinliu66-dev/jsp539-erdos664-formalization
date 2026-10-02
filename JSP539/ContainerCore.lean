/-
Copyright 2026 JSP539 formalization contributors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy at http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.
-/
import JSP539.ContainerAlgorithm

/-!
# Finite hypergraph containers with deterministic reconstruction

This file packages the finite algorithm proved in `ContainerAlgorithm` into
Theorem A of Campos--Samotij, “Towards an optimal hypergraph container lemma”,
https://arxiv.org/abs/2408.06617 , Section 3. The reconstruction proof below is
independently written: every positive query lies in the final fingerprint, so
replaying that fingerprint gives exactly the original state at each round.

The public theorem `theoremA` assumes only finite uniformity, positive rank,
and the stated numerical density range. In particular, neither existence of
containers nor consistency of their reconstruction is an input hypothesis.
Pinned compilation and verification records are in VERIFICATION.md.
-/

namespace JSP539.ContainerCore

open Erdos565 Erdos565.Hypergraph Erdos565.ContainerSelector

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Replaying any intermediate set between the final fingerprint and the
original input produces the same state. This statement also applies to inputs
which are not independent. -/
lemma run_replay {q : Parameters} (I J : Finset V) (n : ℕ) (s : State q V)
    (hJI : J ⊆ I) (hout : (run I n s).fingerprint ⊆ J) :
    run J n s = run I n s := by
  classical
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    by_cases hstop : Stop q.density s.family
    · rw [run_succ_stop J n s hstop, run_succ_stop I n s hstop]
    · rw [run_succ_active I n s hstop] at hout
      have hnext : next J s = next I s := by
        by_cases hseed : (choice s hstop).seed ⊆ I
        · have hseed_next : (choice s hstop).seed ⊆ (next I s).fingerprint := by
            rw [next_of_accept I s hstop hseed]
            exact Finset.subset_union_right
          have hseedJ : (choice s hstop).seed ⊆ J :=
            (hseed_next.trans (run_fingerprint_mono I n (next I s))).trans hout
          rw [next_of_accept J s hstop hseedJ, next_of_accept I s hstop hseed]
        · have hseedJ : ¬ (choice s hstop).seed ⊆ J :=
            fun h => hseed (h.trans hJI)
          rw [next_of_reject J s hstop hseedJ, next_of_reject I s hstop hseed]
      rw [run_succ_active J n s hstop, run_succ_active I n s hstop, hnext]
      exact ih (next I s) hout

/-- A fixed fuel exceeding the number of possible members of an upset. -/
def fuel (V : Type*) [Fintype V] : ℕ := 2 ^ Fintype.card V + 1

noncomputable def output (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) : State q V :=
  run I (fuel V) (initial q H hH)

lemma output_terminal (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    Stop q.density (output q H hH I).family :=
  run_terminal I (initial q H hH)

lemma output_fingerprint_subset (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    (output q H hH I).fingerprint ⊆ I :=
  run_fingerprint_subset I (fuel V) (initial q H hH) (Finset.empty_subset I)

lemma output_independent (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) (hI : H.IsIndependent I) :
    (output q H hH I).family.IsIndependent I :=
  run_independent I (fuel V) (initial q H hH) hI

lemma output_upClosure (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    H.upClosure ⊆ (output q H hH I).family.upClosure :=
  run_upClosure_mono I (fuel V) (initial q H hH)

/-- The full output, including its final hypergraph, is reconstructed from its
fingerprint alone. -/
lemma output_reconstruct (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    output q H hH (output q H hH I).fingerprint = output q H hH I := by
  apply run_replay
  · exact output_fingerprint_subset q H hH I
  · exact Finset.Subset.rfl

lemma output_consistent (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) {I J : Finset V}
    (hS : (output q H hH I).fingerprint = (output q H hH J).fingerprint) :
    output q H hH I = output q H hH J := by
  calc
    output q H hH I = output q H hH (output q H hH I).fingerprint :=
      (output_reconstruct q H hH I).symm
    _ = output q H hH (output q H hH J).fingerprint := congrArg _ hS
    _ = output q H hH J := output_reconstruct q H hH J

lemma output_fingerprint_bound (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (I : Finset V) :
    ((output q H hH I).fingerprint.card : ℝ) ≤
      8 * (q.rank : ℝ) ^ 2 * q.density * Fintype.card V := by
  have hb := (output q H hH I).budget
  have ht := terminal_potential_le q.density_pos.le
    (output q H hH I).nonempty_edges (output_terminal q H hH I) q.rank
  have hm := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ 8 * (q.rank : ℝ) ^ 2)
  calc
    ((output q H hH I).fingerprint.card : ℝ) ≤
        8 * (q.rank : ℝ) ^ 2 * potential (output q H hH I).family q.density q.rank := hb
    _ ≤ 8 * (q.rank : ℝ) ^ 2 * (q.density * Fintype.card V) := hm
    _ = 8 * (q.rank : ℝ) ^ 2 * q.density * Fintype.card V := by ring

/-- A container is reconstructed by feeding the fingerprint into the same
canonical algorithm. This total definition also accepts unattained seeds. -/
noncomputable def containerMap (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) (S : Finset V) : Finset V :=
  (output q H hH S).family.containerVertices

noncomputable def fingerprints (q : Parameters) (H : Hypergraph V)
    (hH : H.IsUniform q.rank) : Finset (Finset V) := by
  classical
  exact (Finset.univ.filter H.IsIndependent).image
    (fun I => (output q H hH I).fingerprint)

lemma mem_fingerprints {q : Parameters} {H : Hypergraph V}
    {hH : H.IsUniform q.rank} {S : Finset V} :
    S ∈ fingerprints q H hH ↔
      ∃ I : Finset V, H.IsIndependent I ∧ (output q H hH I).fingerprint = S := by
  classical
  simp [fingerprints]

/-- The finite Campos--Samotij container theorem, with its actual fingerprint
family and total deterministic reconstruction map. No container theorem is
assumed anywhere in its proof. -/
theorem theoremA (H : Hypergraph V) (r : ℕ) (p : ℝ)
    (hr : 0 < r) (hH : H.IsUniform r) (hp : 0 < p)
    (hsmall : p ≤ 1 / (8 * (r : ℝ) ^ 2)) :
    ∃ (S : Finset (Finset V)) (C : Finset V → Finset V),
      (∀ I : Finset V, H.IsIndependent I →
        ∃ s ∈ S, s ⊆ I ∧ I ⊆ C s) ∧
      (∀ s ∈ S, (s.card : ℝ) ≤ 8 * (r : ℝ) ^ 2 * p * Fintype.card V) ∧
      (∀ s ∈ S, ∃ F : Hypergraph V,
        (∀ E ∈ F, E ⊆ C s ∧ 2 ≤ E.card) ∧
        F.Covers (H.restrict (C s)) ∧ F.pWeight p ≤ p * (C s).card) := by
  classical
  let q : Parameters := ⟨r, p, hr, hp, hsmall⟩
  let C := containerMap q H hH
  refine ⟨fingerprints q H hH, C, ?_, ?_, ?_⟩
  · intro I hI
    let s := (output q H hH I).fingerprint
    refine ⟨s, mem_fingerprints.mpr ⟨I, hI, rfl⟩,
      output_fingerprint_subset q H hH I, ?_⟩
    have hIC := (output_independent q H hH I hI).subset_containerVertices
    change I ⊆ (output q H hH s).family.containerVertices
    rw [show output q H hH s = output q H hH I from output_reconstruct q H hH I]
    exact hIC
  · intro s hs
    obtain ⟨I, hI, rfl⟩ := mem_fingerprints.mp hs
    exact output_fingerprint_bound q H hH I
  · intro s hs
    let T := output q H hH s
    refine ⟨T.family.aboveOne, ?_, ?_, ?_⟩
    · intro E hE
      exact ⟨T.antichain.aboveOne_subset_containerVertices hE,
        (mem_aboveOne.mp hE).2⟩
    · exact cover_restrict_by_aboveOne (output_upClosure q H hH s) T.nonempty_edges
    · exact output_terminal q H hH s

end JSP539.ContainerCore
