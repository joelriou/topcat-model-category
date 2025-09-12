import TopCatModelCategory.Convenient.GeneratedBy

universe v v' t u

open Topology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  (Y : Type v) [TopologicalSpace Y]

namespace Topology

instance {α : Type*} {Z : α → Type v} [∀ a, TopologicalSpace (Z a)]
    [∀ a, IsGeneratedBy X (Z a)] :
    IsGeneratedBy X (Σ a, Z a) where
  continuous_equiv_symm := by
    rw [continuous_def]
    intro U hU
    rw [WithGeneratedByTopology.isOpen_iff] at hU
    rw [isOpen_sigma_iff]
    intro a
    rw [IsGeneratedBy.isOpen_iff X]
    intro i f
    exact hU ⟨fun x ↦ ⟨a, f x⟩, by continuity⟩

namespace WithGeneratedByTopology

abbrev fromSigma : (Σ (p : Σ (i : ι), C(X i, Y)), X p.1) → WithGeneratedByTopology X Y :=
  fun ⟨p, x⟩ ↦ p.2 x

lemma isOpen_preimage_fromSigma_iff (U : Set (WithGeneratedByTopology X Y)) :
    IsOpen ((fromSigma X Y) ⁻¹' U) ↔ IsOpen U := by
  rw [isOpen_sigma_iff, isOpen_iff]
  exact ⟨fun hU i f ↦ hU ⟨i, f⟩, fun hU ⟨i, f⟩ ↦ hU f⟩

variable [Inhabited ι] [Nonempty (X default)]

lemma fromSigma_surjective : Function.Surjective (fromSigma X Y) := by
  intro y
  exact ⟨⟨⟨default, ⟨fun _ ↦ y, by continuity⟩⟩, Classical.arbitrary _⟩, rfl⟩

lemma isQuotientMap_fromSigma : IsQuotientMap (fromSigma X Y) where
  surjective := fromSigma_surjective X Y
  eq_coinduced := by
    ext U
    rw [isOpen_coinduced, isOpen_preimage_fromSigma_iff]

end WithGeneratedByTopology

namespace IsGeneratedBy

abbrev fromSigma : (Σ (p : Σ (i : ι), C(X i, Y)), X p.1) → Y :=
  fun ⟨p, x⟩ ↦ p.2 x

lemma iff_isQuotientMap_fromSigma [Inhabited ι] [Nonempty (X default)] :
    IsGeneratedBy X Y ↔ IsQuotientMap (fromSigma X Y) :=
  ⟨fun _ ↦ homeomorph.isQuotientMap.comp
    (WithGeneratedByTopology.isQuotientMap_fromSigma X Y), fun h ↦ h.isGeneratedBy⟩

end IsGeneratedBy

end Topology
