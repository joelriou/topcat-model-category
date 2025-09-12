import TopCatModelCategory.Convenient.Sigma
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homeomorph.Lemmas

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

namespace IsGeneratedBy

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  (T : Type v') [TopologicalSpace T]
  (Y : Type v) [TopologicalSpace Y]

variable [Inhabited ι] [Nonempty (X default)]

instance [∀ i, IsGeneratedBy X (X i × Y)] [LocallyCompactSpace Y]
     [IsGeneratedBy X T] : IsGeneratedBy X (T × Y) := by
  have hT := (iff_isQuotientMap_fromSigma X T).1 inferInstance
  replace hT := hT.prodMap_id_right_of_locallyCompactSpace Y
  replace hT := hT.comp Homeomorph.sigmaProdDistrib.symm.isQuotientMap
  exact hT.isGeneratedBy

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

instance [IsGeneratedBy X T] [IsGeneratedBy X Y] [LocallyCompactSpace Y] :
    IsGeneratedBy X (T × Y) := by
  have (i : ι) : IsGeneratedBy X (X i × Y) :=
    (Homeomorph.prodComm _ _).isQuotientMap.isGeneratedBy
  infer_instance

instance [IsGeneratedBy X T] [IsGeneratedBy X Y] [LocallyCompactSpace T] :
    IsGeneratedBy X (T × Y) :=
  (Homeomorph.prodComm _ _).isQuotientMap.isGeneratedBy

end IsGeneratedBy

end Topology
