/-
Copyright 2026 The JSP539 Formalization Authors.
Licensed under the Apache License, Version 2.0; see LICENSE.

Finite ground-set transport. All cardinalities and degrees are preserved;
the new ambient type has exactly the prescribed ground-set cardinality.
-/
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import LicensedContainers.Hypergraph

open Erdos565

namespace JSP539

variable {V : Type*} [DecidableEq V]

abbrev Ground (X : Finset V) := {v // v ∈ X}

@[simp] theorem ground_card (X : Finset V) : Fintype.card (Ground X) = X.card := by
  simp [Ground]

/-- Restriction to the actual finite vertex type, before transport of a graph. -/
def liftEdge (X e : Finset V) : Finset (Ground X) :=
  X.attach.filter (fun v => v.1 ∈ e)

@[simp] theorem mem_liftEdge (X e : Finset V) (v : Ground X) :
    v ∈ liftEdge X e ↔ v.1 ∈ e := by
  simp [liftEdge]

@[simp] theorem image_liftEdge (X e : Finset V) :
    (liftEdge X e).image Subtype.val = e ∩ X := by
  ext v
  simp only [Finset.mem_image, mem_liftEdge, Finset.mem_inter]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, x.2⟩
  · rintro ⟨he, hX⟩
    exact ⟨⟨v, hX⟩, he, rfl⟩

theorem image_liftEdge_of_subset (X e : Finset V) (he : e ⊆ X) :
    (liftEdge X e).image Subtype.val = e := by
  rw [image_liftEdge, Finset.inter_eq_left.mpr he]

theorem liftEdge_card (X e : Finset V) (he : e ⊆ X) :
    (liftEdge X e).card = e.card := by
  calc
    (liftEdge X e).card = ((liftEdge X e).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = e.card := congrArg Finset.card (image_liftEdge_of_subset X e he)

theorem liftEdge_injective_on (X : Finset V) {e f : Finset V}
    (he : e ⊆ X) (hf : f ⊆ X) (hef : liftEdge X e = liftEdge X f) : e = f := by
  have h := congrArg (fun s : Finset (Ground X) => s.image Subtype.val) hef
  simpa only [image_liftEdge_of_subset X e he, image_liftEdge_of_subset X f hf] using h

theorem subset_liftEdge_iff (X e : Finset V) (S : Finset (Ground X)) :
    S ⊆ liftEdge X e ↔ S.image Subtype.val ⊆ e := by
  constructor
  · intro h v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact (mem_liftEdge X e x).mp (h hx)
  · intro h x hx
    apply (mem_liftEdge X e x).mpr
    exact h (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

/-- Transport a supported hypergraph to its true ground type. -/
def onGround (H : Hypergraph V) (X : Finset V) : Hypergraph (Ground X) :=
  H.image (liftEdge X)

@[simp] theorem mem_onGround (H : Hypergraph V) (X : Finset V)
    (a : Finset (Ground X)) :
    a ∈ onGround H X ↔ ∃ e ∈ H, liftEdge X e = a := by
  simp [onGround]

theorem onGround_card (H : Hypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) : (onGround H X).card = H.card := by
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  exact liftEdge_injective_on X (hH e he) (hH f hf) hef

theorem onGround_uniform (H : Hypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) {k : ℕ} (hk : H.IsUniform k) :
    (onGround H X).IsUniform k := by
  intro a ha
  obtain ⟨e, he, rfl⟩ := (mem_onGround H X a).mp ha
  rw [liftEdge_card X e (hH e he), hk e he]

/-- Every codegree, including the edge count at the empty set, is preserved. -/
theorem onGround_degree (H : Hypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) (S : Finset (Ground X)) :
    (onGround H X).degree S = H.degree (S.image Subtype.val) := by
  classical
  have heq : (onGround H X).filter (fun e => S ⊆ e) =
      (H.filter (fun e => S.image Subtype.val ⊆ e)).image (liftEdge X) := by
    ext a
    simp only [Finset.mem_filter, mem_onGround, Finset.mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hSe⟩
      exact ⟨e, ⟨he, (subset_liftEdge_iff X e S).mp hSe⟩, rfl⟩
    · rintro ⟨e, ⟨he, hSe⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, (subset_liftEdge_iff X e S).mpr hSe⟩
  unfold Hypergraph.degree
  rw [heq]
  apply Finset.card_image_iff.mpr
  intro e he f hf hef
  exact liftEdge_injective_on X
    (hH e (Finset.mem_filter.mp he).1) (hH f (Finset.mem_filter.mp hf).1) hef

theorem onGround_independent (H : Hypergraph V) (X : Finset V)
    (hH : ∀ e ∈ H, e ⊆ X) (A : Finset (Ground X))
    (hA : H.IsIndependent (A.image Subtype.val)) :
    (onGround H X).IsIndependent A := by
  intro a ha haA
  obtain ⟨e, he, rfl⟩ := (mem_onGround H X a).mp ha
  apply hA e he
  rw [← image_liftEdge_of_subset X e (hH e he)]
  exact Finset.image_subset_image haA

end JSP539
