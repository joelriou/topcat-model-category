import TopCatModelCategory.Convenient.GeneratedBy
import Mathlib.Topology.CompactOpen

universe v v' t u

open Topology

namespace Topology

namespace IsQuotientMap

variable {X₁ X₂ : Type*} {f : X₁ → X₂}
  [TopologicalSpace X₁] [TopologicalSpace X₂]
  (hf : IsQuotientMap f)
  (Y : Type*) [TopologicalSpace Y] [LocallyCompactSpace Y]

include hf

lemma prod_locallyCompactSpace_aux
    {T : Type*} [TopologicalSpace T]
    (g : X₂ × Y → T) :
    Continuous g ↔ Continuous (g ∘ Prod.map f id) :=
  ⟨fun hg ↦ hg.comp (hf.continuous.prodMap continuous_id), fun hg ↦ by
    refine (ContinuousMap.uncurry ⟨fun x₂ ↦ ⟨fun y ↦ g (x₂, y), ?_⟩, ?_⟩).continuous
    · obtain ⟨x₁, rfl⟩ := hf.surjective x₂
      exact hg.comp (.prodMk_right x₁)
    · rw [hf.continuous_iff]
      exact ContinuousMap.continuous_of_continuous_uncurry _ hg⟩

lemma prodMap_id_right_of_locallyCompactSpace :
    IsQuotientMap (Prod.map f (id : Y → Y)) where
  surjective := hf.surjective.prodMap Function.surjective_id
  eq_coinduced := by
    apply le_antisymm
    · rw [← continuous_id_iff_le, hf.prod_locallyCompactSpace_aux,
        Function.id_comp, continuous_def]
      intro U hU
      rwa [isOpen_coinduced] at hU
    · rw [← continuous_iff_coinduced_le]
      exact (hf.continuous.prodMap continuous_id)

lemma prodMap_id_left_of_locallyCompactSpace :
    IsQuotientMap (Prod.map (id : Y → Y) f) :=
  (Homeomorph.prodComm _ _).isQuotientMap.comp
    ((hf.prodMap_id_right_of_locallyCompactSpace _).comp
      (Homeomorph.prodComm _ _).isQuotientMap)

end IsQuotientMap

end Topology
