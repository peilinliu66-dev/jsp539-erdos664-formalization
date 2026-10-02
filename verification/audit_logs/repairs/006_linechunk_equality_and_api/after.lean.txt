/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Original proofs of finite line chunk hypergraphs. The construction is the
balanced supersaturation construction used in the fixed-k specialization of
Jiaxi Nie, arXiv:2609.07736. Partitions are constructed, not assumed.
-/
import JSP539.AffinePlane
import JSP539.ChunkPartition
import JSP539.GroundHypergraph

open scoped BigOperators
open Erdos565

namespace JSP539

section FiniteSetLemmas

variable {V : Type*} [DecidableEq V]

/-- Removing a fixed subset injects its supersets into a smaller powerset layer. -/
theorem powersetCard_degree_le (C S : Finset V) (k : ℕ) (hSC : S ⊆ C) :
    ((C.powersetCard k).filter (fun e => S ⊆ e)).card ≤
      (C.card - S.card).choose (k - S.card) := by
  classical
  let D := (C.powersetCard k).filter (fun e => S ⊆ e)
  have hinj : Set.InjOn (fun e : Finset V => e \ S) (↑D : Set (Finset V)) := by
    intro e he f hf hef
    change e \ S = f \ S at hef
    have hSe := (Finset.mem_filter.mp he).2
    have hSf := (Finset.mem_filter.mp hf).2
    calc
      e = S ∪ (e \ S) := (Finset.union_sdiff_of_subset hSe).symm
      _ = S ∪ (f \ S) := by rw [hef]
      _ = f := Finset.union_sdiff_of_subset hSf
  have himage : D.image (fun e => e \ S) ⊆
      (C \ S).powersetCard (k - S.card) := by
    intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨heC, hSe⟩ := Finset.mem_filter.mp he
    obtain ⟨heC, hek⟩ := Finset.mem_powersetCard.mp heC
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.sdiff_subset_sdiff heC (Finset.Subset.rfl), ?_⟩
    rw [Finset.card_sdiff_of_subset hSe, hek]
  calc
    D.card = (D.image (fun e => e \ S)).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((C \ S).powersetCard (k - S.card)).card := Finset.card_le_card himage
    _ = (C.card - S.card).choose (k - S.card) := by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hSC]

/-- If the required set is not contained in the chunk, its degree is zero. -/
theorem powersetCard_degree_eq_zero (C S : Finset V) (k : ℕ) (hSC : ¬ S ⊆ C) :
    ((C.powersetCard k).filter (fun e => S ⊆ e)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨heC, hSe⟩ := Finset.mem_filter.mp he
  exact hSC (hSe.trans (Finset.mem_powersetCard.mp heC).1)

/-- A finite union of powerset layers. -/
def chunkHypergraph (chunks : Finset (Finset V)) (k : ℕ) : Hypergraph V :=
  chunks.biUnion (fun C => C.powersetCard k)

@[simp] theorem mem_chunkHypergraph {chunks : Finset (Finset V)} {k : ℕ}
    {e : Finset V} :
    e ∈ chunkHypergraph chunks k ↔ ∃ C ∈ chunks, e ⊆ C ∧ e.card = k := by
  simp [chunkHypergraph, Finset.mem_powersetCard]

theorem chunkHypergraph_uniform (chunks : Finset (Finset V)) (k : ℕ) :
    (chunkHypergraph chunks k).IsUniform k := by
  intro e he
  obtain ⟨C, _, _, hek⟩ := mem_chunkHypergraph.mp he
  exact hek

/-- A union bound on degrees that retains the number of chunks containing S. -/
theorem chunkHypergraph_degree_le (chunks : Finset (Finset V)) (k gamma : ℕ)
    (hcard : ∀ C ∈ chunks, C.card = gamma) (S : Finset V) :
    (chunkHypergraph chunks k).degree S ≤
      (chunks.filter (fun C => S ⊆ C)).card *
        (gamma - S.card).choose (k - S.card) := by
  classical
  let T := chunks.filter (fun C => S ⊆ C)
  have hfilter : (chunkHypergraph chunks k).filter (fun e => S ⊆ e) =
      T.biUnion (fun C => (C.powersetCard k).filter (fun e => S ⊆ e)) := by
    ext e
    constructor
    · intro he
      obtain ⟨heH, hSe⟩ := Finset.mem_filter.mp he
      obtain ⟨C, hC, heC, hek⟩ := mem_chunkHypergraph.mp heH
      apply Finset.mem_biUnion.mpr
      refine ⟨C, Finset.mem_filter.mpr ⟨hC, hSe.trans heC⟩, ?_⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨heC, hek⟩, hSe⟩
    · intro he
      obtain ⟨C, hC, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨heC, hSe⟩ := Finset.mem_filter.mp he
      obtain ⟨heC, hek⟩ := Finset.mem_powersetCard.mp heC
      apply Finset.mem_filter.mpr
      exact ⟨mem_chunkHypergraph.mpr
        ⟨C, (Finset.mem_filter.mp hC).1, heC, hek⟩, hSe⟩
  unfold Hypergraph.degree
  rw [hfilter]
  calc
    (T.biUnion (fun C => (C.powersetCard k).filter (fun e => S ⊆ e))).card ≤
        ∑ C ∈ T, ((C.powersetCard k).filter (fun e => S ⊆ e)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _C ∈ T, (gamma - S.card).choose (k - S.card) := by
      apply Finset.sum_le_sum
      intro C hC
      have hmem := Finset.mem_filter.mp hC
      simpa [hcard C hmem.1] using powersetCard_degree_le C S k hmem.2
    _ = T.card * (gamma - S.card).choose (k - S.card) := by simp

/-- Chunk intersections of size at most one prevent repeated k-edges for k≥2. -/
theorem chunkHypergraph_card (chunks : Finset (Finset V)) (k gamma : ℕ)
    (hk : 2 ≤ k) (hcard : ∀ C ∈ chunks, C.card = gamma)
    (hinter : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → (C ∩ D).card ≤ 1) :
    (chunkHypergraph chunks k).card = chunks.card * gamma.choose k := by
  classical
  have hdis : (↑chunks : Set (Finset V)).Pairwise
      (fun C D => Disjoint (C.powersetCard k) (D.powersetCard k)) := by
    intro C hC D hD hCD
    apply Finset.disjoint_left.mpr
    intro e heC heD
    obtain ⟨heC, hek⟩ := Finset.mem_powersetCard.mp heC
    obtain ⟨heD, _⟩ := Finset.mem_powersetCard.mp heD
    have hle := (Finset.card_le_card (Finset.subset_inter heC heD)).trans
      (hinter C hC D hD hCD)
    omega
  rw [chunkHypergraph, Finset.card_biUnion hdis]
  calc
    ∑ C ∈ chunks, (C.powersetCard k).card = ∑ _C ∈ chunks, gamma.choose k := by
      apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.card_powersetCard, hcard C hC]
    _ = chunks.card * gamma.choose k := by simp

/-- A set of at least two vertices is contained in at most one such chunk. -/
theorem chunks_containing_card_le_one (chunks : Finset (Finset V))
    (hinter : ∀ C ∈ chunks, ∀ D ∈ chunks, C ≠ D → (C ∩ D).card ≤ 1)
    (S : Finset V) (hS : 2 ≤ S.card) :
    (chunks.filter (fun C => S ⊆ C)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro C hC D hD
  obtain ⟨hC, hSC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hD, hSD⟩ := Finset.mem_filter.mp hD
  by_contra hCD
  have hle := (Finset.card_le_card (Finset.subset_inter hSC hSD)).trans
    (hinter C hC D hD hCD)
  omega

end FiniteSetLemmas

namespace Affine

variable {q : ℕ} [Fact q.Prime]
variable {X : Finset (Point q)} {gamma : ℕ}

/-- Each constituent partition is obtained from the proved finite constructor. -/
noncomputable def linePartitions (X : Finset (Point q)) (hgamma : 0 < gamma) :
    ∀ l : Line q, ChunkPartition (points l ∩ X) gamma :=
  fun l => chunkPartition (points l ∩ X) hgamma

/-- The finite collection of all chunks, with duplicate sets collapsed. The
lemmas below prove that collapse never identifies chunks from different lines. -/
def allChunks (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) :
    Finset (Finset (Point q)) :=
  Finset.univ.biUnion (fun l => (P l).chunks)

@[simp] theorem mem_allChunks
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (C : Finset (Point q)) :
    C ∈ allChunks P ↔ ∃ l : Line q, C ∈ (P l).chunks := by
  simp [allChunks]

theorem allChunks_card_each
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    {C : Finset (Point q)} (hC : C ∈ allChunks P) : C.card = gamma := by
  obtain ⟨l, hC⟩ := (mem_allChunks P C).mp hC
  exact (P l).chunk_card C hC

theorem allChunks_subset
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    {C : Finset (Point q)} (hC : C ∈ allChunks P) : C ⊆ X := by
  obtain ⟨l, hC⟩ := (mem_allChunks P C).mp hC
  exact ((P l).chunk_subset C hC).trans Finset.inter_subset_right

/-- Distinct chunks on a line are disjoint, and on different lines they share
at most one point. This is the only geometric input to higher codegrees. -/
theorem allChunks_intersection
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    {C D : Finset (Point q)} (hC : C ∈ allChunks P) (hD : D ∈ allChunks P)
    (hCD : C ≠ D) : (C ∩ D).card ≤ 1 := by
  obtain ⟨l, hCl⟩ := (mem_allChunks P C).mp hC
  obtain ⟨m, hDm⟩ := (mem_allChunks P D).mp hD
  by_cases hlm : l = m
  · subst m
    have hdis := (P l).pairwise_disjoint hCl hDm hCD
    have hemp : C ∩ D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdis
    simp [hemp]
  · have hsub : C ∩ D ⊆ points l ∩ points m := by
      apply Finset.inter_subset_inter
      · exact ((P l).chunk_subset C hCl).trans Finset.inter_subset_left
      · exact ((P m).chunk_subset D hDm).trans Finset.inter_subset_left
    exact (Finset.card_le_card hsub).trans (intersection_card_le_one hlm)

/-- No gamma-chunk with gamma≥2 can belong to two different affine lines. -/
theorem chunk_line_unique
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (hg : 2 ≤ gamma)
    {l m : Line q} {C : Finset (Point q)}
    (hCl : C ∈ (P l).chunks) (hCm : C ∈ (P m).chunks) : l = m := by
  by_contra hlm
  have hsub : C ⊆ points l ∩ points m :=
    Finset.subset_inter
      (((P l).chunk_subset C hCl).trans Finset.inter_subset_left)
      (((P m).chunk_subset C hCm).trans Finset.inter_subset_left)
  have hle := (Finset.card_le_card hsub).trans (intersection_card_le_one hlm)
  rw [(P l).chunk_card C hCl] at hle
  omega

/-- Consequently the number of global chunks is the sum over the lines. -/
theorem allChunks_card
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (hg : 2 ≤ gamma) :
    (allChunks P).card = ∑ l : Line q, (P l).chunks.card := by
  apply Finset.card_biUnion
  intro l _ m _ hlm
  apply Finset.disjoint_left.mpr
  intro C hCl hCm
  exact hlm (chunk_line_unique P hg hCl hCm)

/-- Incidence counting forces at least q² chunks once |X|≥2 gamma q. -/
theorem allChunks_card_lower
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    (hg : 2 ≤ gamma) (hX : 2 * gamma * q ≤ X.card) :
    q ^ 2 ≤ (allChunks P).card := by
  have hsum : ∑ l : Line q, (points l ∩ X).card ≤
      gamma * ((∑ l : Line q, (P l).chunks.card) + q * (q + 1)) := by
    calc
      ∑ l : Line q, (points l ∩ X).card ≤
          ∑ l : Line q, gamma * ((P l).chunks.card + 1) := by
        apply Finset.sum_le_sum
        intro l _
        exact (P l).card_lt_mul_succ.le
      _ = gamma * ((∑ l : Line q, (P l).chunks.card) + q * (q + 1)) := by
        simp [Finset.mul_sum, Finset.sum_add_distrib, Nat.mul_add, Nat.mul_comm,
          Nat.mul_left_comm, Nat.mul_assoc]
  rw [sum_trace_card, ← allChunks_card P hg] at hsum
  have hgamma : 0 < gamma := by omega
  have hinc : (q + 1) * (2 * gamma * q) ≤ (q + 1) * X.card :=
    Nat.mul_le_mul_left _ hX
  have hbase : gamma * (q * (q + 1)) ≤ gamma * (allChunks P).card := by
    nlinarith
  have hmany : q * (q + 1) ≤ (allChunks P).card :=
    Nat.le_of_mul_le_mul_left hbase hgamma
  nlinarith

/-- At most one chunk through a point can occur in each direction. -/
theorem allChunks_point_count
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma) (p : Point q) :
    ((allChunks P).filter (fun C => p ∈ C)).card ≤ q + 1 := by
  classical
  let T := (allChunks P).filter (fun C => p ∈ C)
  have hex : ∀ C : {C // C ∈ T}, ∃ l : Line q, C.1 ∈ (P l).chunks := by
    intro C
    exact (mem_allChunks P C.1).mp (Finset.mem_filter.mp C.2).1
  choose f hf using hex
  have hpf : ∀ C, f C ∈ linesThrough p := by
    intro C
    apply (mem_linesThrough p (f C)).mpr
    exact (Finset.mem_inter.mp (((P (f C)).chunk_subset C.1 (hf C))
      ((Finset.mem_filter.mp C.2).2))).1
  let g : {C // C ∈ T} → {l // l ∈ linesThrough p} :=
    fun C => ⟨f C, hpf C⟩
  have hginj : Function.Injective g := by
    intro C D hCD
    apply Subtype.ext
    have hlines : f C = f D := congrArg Subtype.val hCD
    by_contra hsets
    have hD : D.1 ∈ (P (f C)).chunks := by
      rw [hlines]
      exact hf D
    have hdis := (P (f C)).pairwise_disjoint (hf C) hD hsets
    exact Finset.disjoint_left.mp hdis
      (Finset.mem_filter.mp C.2).2 (Finset.mem_filter.mp D.2).2
  have hcard := Fintype.card_le_of_injective g hginj
  simpa only [Fintype.card_coe, linesThrough_card] using hcard

/-- Every k-arc is independent in the explicitly constructed chunk hypergraph. -/
theorem arc_independent_chunks
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    (k : ℕ) {A : Finset (Point q)} (hA : IsArc k A) :
    (chunkHypergraph (allChunks P) k).IsIndependent A := by
  intro e he heA
  obtain ⟨C, hC, heC, hek⟩ := mem_chunkHypergraph.mp he
  obtain ⟨l, hCl⟩ := (mem_allChunks P C).mp hC
  have heL : e ⊆ points l :=
    heC.trans (((P l).chunk_subset C hCl).trans Finset.inter_subset_left)
  have hle := Finset.card_le_card (Finset.subset_inter heA heL)
  have hlt := hA l
  omega

/-- This record contains actual uniform finite hypergraphs and proved estimates,
with no assumed existence statement for balanced supersaturation. -/
structure BalancedChunkHypergraph (X : Finset (Point q)) (k gamma : ℕ) where
  H : Hypergraph (Point q)
  uniform : H.IsUniform k
  supported : ∀ e ∈ H, e ⊆ X
  edge_lower : q ^ 2 * gamma.choose k ≤ H.card
  degree_one : ∀ p : Point q,
    H.degree {p} ≤ (q + 1) * (gamma - 1).choose (k - 1)
  higher_degree : ∀ S : Finset (Point q), 2 ≤ S.card → S.card ≤ k →
    H.degree S ≤ (gamma - S.card).choose (k - S.card)
  arc_independent : ∀ A : Finset (Point q), IsArc k A → H.IsIndependent A

/-- All counting bounds for any of the constructed line partitions. -/
noncomputable def balancedOfPartitions
    (P : ∀ l : Line q, ChunkPartition (points l ∩ X) gamma)
    (k : ℕ) (hk : 2 ≤ k) (hkg : k ≤ gamma)
    (hX : 2 * gamma * q ≤ X.card) : BalancedChunkHypergraph X k gamma where
  H := chunkHypergraph (allChunks P) k
  uniform := chunkHypergraph_uniform _ _
  supported := by
    intro e he
    obtain ⟨C, hC, heC, _⟩ := mem_chunkHypergraph.mp he
    exact heC.trans (allChunks_subset P hC)
  edge_lower := by
    rw [chunkHypergraph_card _ _ _ hk
      (fun C hC => allChunks_card_each P hC)
      (fun C hC D hD hCD => allChunks_intersection P hC hD hCD)]
    exact Nat.mul_le_mul_right _ (allChunks_card_lower P (hk.trans hkg) hX)
  degree_one := by
    intro p
    have hdegree := chunkHypergraph_degree_le (allChunks P) k gamma
      (fun C hC => allChunks_card_each P hC) {p}
    have hcount : ((allChunks P).filter (fun C => ({p} : Finset (Point q)) ⊆ C)).card ≤
        q + 1 := by simpa using allChunks_point_count P p
    simpa using hdegree.trans (Nat.mul_le_mul_right
      ((gamma - ({p} : Finset (Point q)).card).choose
        (k - ({p} : Finset (Point q)).card)) hcount)
  higher_degree := by
    intro S hS _
    have hdegree := chunkHypergraph_degree_le (allChunks P) k gamma
      (fun C hC => allChunks_card_each P hC) S
    have hcount := chunks_containing_card_le_one (allChunks P)
      (fun C hC D hD hCD => allChunks_intersection P hC hD hCD) S hS
    simpa using hdegree.trans (Nat.mul_le_mul_right
      ((gamma - S.card).choose (k - S.card)) hcount)
  arc_independent := fun _ hA => arc_independent_chunks P k hA

/-- The integer chunk size selected from the current vertex set. -/
def chunkSize (X : Finset (Point q)) : ℕ := X.card / (2 * q)

theorem chunkSize_ge {k : ℕ} (hX : 2 * k * q < X.card) :
    k ≤ chunkSize X := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  unfold chunkSize
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 * q)).mpr
  nlinarith

theorem chunkSize_mul_le : 2 * chunkSize X * q ≤ X.card := by
  have h := Nat.div_mul_le_self X.card (2 * q)
  simpa only [chunkSize, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem card_le_three_chunkSize {k : ℕ} (hk : 2 ≤ k)
    (hX : 2 * k * q < X.card) : X.card ≤ 3 * chunkSize X * q := by
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hg := hk.trans (chunkSize_ge hX)
  have hrem := Nat.mod_lt X.card (by omega : 0 < 2 * q)
  have hdiv := Nat.mod_add_div X.card (2 * q)
  change X.card % (2 * q) + (2 * q) * chunkSize X = X.card at hdiv
  nlinarith

/-- Public endpoint: every sufficiently large X has a fully constructed
balanced hypergraph. No chunk or incidence oracle is an argument. -/
noncomputable def balancedChunkHypergraph (X : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hX : 2 * k * q < X.card) :
    BalancedChunkHypergraph X k (chunkSize X) := by
  have hkg : k ≤ chunkSize X := chunkSize_ge hX
  have hg : 0 < chunkSize X := by omega
  exact balancedOfPartitions (linePartitions X hg) k hk hkg chunkSize_mul_le

/-- The version used by finite-universe container theorems. Its ambient type
is the subtype X, so its ambient cardinality is |X|, not q². -/
structure BalancedGroundHypergraph (X : Finset (Point q)) (k gamma : ℕ) where
  H : Hypergraph (Ground X)
  uniform : H.IsUniform k
  edge_lower : q ^ 2 * gamma.choose k ≤ H.card
  degree_one : ∀ p : Ground X,
    H.degree {p} ≤ (q + 1) * (gamma - 1).choose (k - 1)
  higher_degree : ∀ S : Finset (Ground X), 2 ≤ S.card → S.card ≤ k →
    H.degree S ≤ (gamma - S.card).choose (k - S.card)
  arc_independent : ∀ A : Finset (Ground X),
    IsArc k (A.image Subtype.val) → H.IsIndependent A

/-- Transport the explicit balanced construction, retaining all its estimates. -/
noncomputable def balancedChunkHypergraphOnGround (X : Finset (Point q)) (k : ℕ)
    (hk : 2 ≤ k) (hX : 2 * k * q < X.card) :
    BalancedGroundHypergraph X k (chunkSize X) := by
  let B := balancedChunkHypergraph X k hk hX
  refine {
    H := onGround B.H X
    uniform := onGround_uniform B.H X B.supported B.uniform
    edge_lower := ?_
    degree_one := ?_
    higher_degree := ?_
    arc_independent := ?_
  }
  · rw [onGround_card B.H X B.supported]
    exact B.edge_lower
  · intro p
    rw [onGround_degree B.H X B.supported]
    simpa using B.degree_one p.1
  · intro S hS hSk
    rw [onGround_degree B.H X B.supported]
    have hcard : (S.image Subtype.val).card = S.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    simpa only [hcard] using B.higher_degree (S.image Subtype.val)
      (by simpa only [hcard] using hS) (by simpa only [hcard] using hSk)
  · intro A hA
    exact onGround_independent B.H X B.supported A (B.arc_independent _ hA)

end Affine
end JSP539
