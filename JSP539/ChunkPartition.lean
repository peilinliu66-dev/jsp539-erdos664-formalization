/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

An original finite-set partition construction.  This file has not been
compiler-checked; the source package deliberately leaves compilation to its
recipient.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Union
import Mathlib.Tactic

namespace JSP539

variable {V : Type*} [DecidableEq V]

/-- A finite set split into disjoint chunks of prescribed cardinality and a
strictly smaller remainder.  The counting identities are consequences of
these fields, rather than additional assumptions. -/
structure ChunkPartition (X : Finset V) (gamma : ℕ) where
  chunks : Finset (Finset V)
  remainder : Finset V
  chunk_card : ∀ C ∈ chunks, C.card = gamma
  chunk_subset : ∀ C ∈ chunks, C ⊆ X
  pairwise_disjoint : (chunks : Set (Finset V)).Pairwise Disjoint
  remainder_subset : remainder ⊆ X
  remainder_disjoint : ∀ C ∈ chunks, Disjoint C remainder
  cover : chunks.biUnion id ∪ remainder = X
  remainder_card_lt : remainder.card < gamma

/-- Every finite set admits a partition into chunks of any positive size.
The induction removes an actual subset of size `gamma` at every nonterminal
step, so no selection or partition oracle is assumed. -/
theorem exists_chunkPartition (X : Finset V) {gamma : ℕ}
    (hgamma : 0 < gamma) : Nonempty (ChunkPartition X gamma) := by
  classical
  have aux : ∀ n : ℕ, ∀ Y : Finset V, Y.card = n →
      Nonempty (ChunkPartition Y gamma) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro Y hY
        by_cases hsmall : Y.card < gamma
        · exact ⟨{
            chunks := ∅
            remainder := Y
            chunk_card := by simp
            chunk_subset := by simp
            pairwise_disjoint := by simp
            remainder_subset := by intro x hx; exact hx
            remainder_disjoint := by simp
            cover := by simp
            remainder_card_lt := hsmall
          }⟩
        · have hlarge : gamma ≤ Y.card := by omega
          obtain ⟨C, hCY, hCcard⟩ := Finset.exists_subset_card_eq hlarge
          have hsmaller : (Y \ C).card < n := by
            rw [Finset.card_sdiff_of_subset hCY, hCcard]
            omega
          obtain ⟨P⟩ := ih (Y \ C).card hsmaller (Y \ C) rfl
          refine ⟨{
            chunks := insert C P.chunks
            remainder := P.remainder
            chunk_card := ?_
            chunk_subset := ?_
            pairwise_disjoint := ?_
            remainder_subset := ?_
            remainder_disjoint := ?_
            cover := ?_
            remainder_card_lt := P.remainder_card_lt
          }⟩
          · intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · exact hCcard
            · exact P.chunk_card D hD
          · intro D hD x hx
            rcases Finset.mem_insert.mp hD with rfl | hD
            · exact hCY hx
            · exact (Finset.mem_sdiff.mp (P.chunk_subset D hD hx)).1
          · intro A hA B hB hAB
            rcases Finset.mem_insert.mp hA with rfl | hA
            · rcases Finset.mem_insert.mp hB with rfl | hB
              · exact (hAB rfl).elim
              · apply Finset.disjoint_left.mpr
                intro x hxC hxB
                exact (Finset.mem_sdiff.mp
                  (P.chunk_subset B hB hxB)).2 hxC
            · rcases Finset.mem_insert.mp hB with rfl | hB
              · apply Finset.disjoint_left.mpr
                intro x hxA hxC
                exact (Finset.mem_sdiff.mp
                  (P.chunk_subset A hA hxA)).2 hxC
              · exact P.pairwise_disjoint hA hB hAB
          · intro x hx
            exact (Finset.mem_sdiff.mp (P.remainder_subset hx)).1
          · intro D hD
            rcases Finset.mem_insert.mp hD with rfl | hD
            · apply Finset.disjoint_left.mpr
              intro x hxC hxR
              exact (Finset.mem_sdiff.mp (P.remainder_subset hxR)).2 hxC
            · exact P.remainder_disjoint D hD
          · rw [Finset.biUnion_insert, id_eq, Finset.union_assoc, P.cover]
            ext x
            simp only [Finset.mem_union, Finset.mem_sdiff]
            constructor
            · rintro (hx | ⟨hx, _⟩)
              · exact hCY hx
              · exact hx
            · intro hx
              by_cases hxC : x ∈ C
              · exact Or.inl hxC
              · exact Or.inr ⟨hx, hxC⟩
  exact aux X.card X rfl

/-- Choose one of the partitions constructed by `exists_chunkPartition`. -/
noncomputable def chunkPartition (X : Finset V) {gamma : ℕ}
    (hgamma : 0 < gamma) : ChunkPartition X gamma :=
  Classical.choice (exists_chunkPartition X hgamma)

private theorem uniform_disjoint_union_card
    (S : Finset (Finset V)) (gamma : ℕ) :
    (∀ C ∈ S, C.card = gamma) → (S : Set (Finset V)).Pairwise Disjoint →
      (S.biUnion id).card = gamma * S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert C S hCS ih =>
      intro hcard hdisj
      have hcardS : ∀ D ∈ S, D.card = gamma := by
        intro D hD
        exact hcard D (Finset.mem_insert_of_mem hD)
      have hdisjS : (S : Set (Finset V)).Pairwise Disjoint := by
        intro A hA B hB hAB
        exact hdisj (Finset.mem_insert_of_mem hA)
          (Finset.mem_insert_of_mem hB) hAB
      have hCU : Disjoint C (S.biUnion id) := by
        apply Finset.disjoint_left.mpr
        intro x hxC hxU
        obtain ⟨D, hD, hxD⟩ := Finset.mem_biUnion.mp hxU
        have hCD : C ≠ D := by
          intro h
          apply hCS
          simpa only [h] using hD
        exact Finset.disjoint_left.mp
          (hdisj (Finset.mem_insert_self C S)
            (Finset.mem_insert_of_mem hD) hCD) hxC hxD
      have hinsert : (insert C S).card = S.card + 1 := by simp [hCS]
      rw [Finset.biUnion_insert, id_eq,
        Finset.card_union_of_disjoint hCU,
        hcard C (Finset.mem_insert_self C S), ih hcardS hdisjS, hinsert]
      ring

namespace ChunkPartition

variable {X : Finset V} {gamma : ℕ} (P : ChunkPartition X gamma)

/-- The union of all chunks is disjoint from the remainder. -/
theorem union_disjoint_remainder :
    Disjoint (P.chunks.biUnion id) P.remainder := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxU hxR
  obtain ⟨C, hC, hxC⟩ := Finset.mem_biUnion.mp hxU
  exact Finset.disjoint_left.mp (P.remainder_disjoint C hC) hxC hxR

/-- Exact cardinality of all complete chunks. -/
theorem chunks_union_card :
    (P.chunks.biUnion id).card = gamma * P.chunks.card :=
  uniform_disjoint_union_card P.chunks gamma P.chunk_card P.pairwise_disjoint

/-- The exact cardinality decomposition, with no divisibility assumption. -/
theorem card_eq : X.card = gamma * P.chunks.card + P.remainder.card := by
  calc
    X.card = (P.chunks.biUnion id ∪ P.remainder).card :=
      congrArg Finset.card P.cover.symm
    _ = (P.chunks.biUnion id).card + P.remainder.card :=
      Finset.card_union_of_disjoint P.union_disjoint_remainder
    _ = gamma * P.chunks.card + P.remainder.card := by
      rw [P.chunks_union_card]

/-- The number of chunks gives a strict covering bound. -/
theorem card_lt_mul_succ : X.card < gamma * (P.chunks.card + 1) := by
  calc
    X.card = gamma * P.chunks.card + P.remainder.card := P.card_eq
    _ < gamma * P.chunks.card + gamma :=
      Nat.add_lt_add_left P.remainder_card_lt _
    _ = gamma * (P.chunks.card + 1) := by ring

/-- Every chunk partition has exactly the integer quotient number of chunks. -/
theorem chunks_card_eq_div : P.chunks.card = X.card / gamma := by
  have hgamma : 0 < gamma :=
    lt_of_le_of_lt (Nat.zero_le P.remainder.card) P.remainder_card_lt
  calc
    P.chunks.card = P.remainder.card / gamma + P.chunks.card := by
      rw [Nat.div_eq_of_lt P.remainder_card_lt, zero_add]
    _ = (P.remainder.card + gamma * P.chunks.card) / gamma :=
      (Nat.add_mul_div_left _ _ hgamma).symm
    _ = X.card / gamma := by
      rw [Nat.add_comm, ← P.card_eq]

/-- The remainder has the unique Euclidean remainder cardinality. -/
theorem remainder_card_eq_mod : P.remainder.card = X.card % gamma := by
  have hcount := P.card_eq
  have hdiv := P.chunks_card_eq_div
  have hEuclid := Nat.mod_add_div X.card gamma
  rw [hdiv] at hcount
  omega

end ChunkPartition

end JSP539
