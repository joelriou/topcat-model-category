import TopCatModelCategory.Convenient.DeltaGenerated
import Mathlib.Topology.Category.DeltaGenerated
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

universe u

open Topology

instance {X : Type u} [TopologicalSpace X] [DeltaGeneratedSpace' X] :
    DeltaGeneratedSpace X where
  le_deltaGenerated := by
    convert IsGeneratedBy.le_generatedBy (X := fun n ↦ (Fin n → ℝ)) (Y := X)
    ext U
    rw [isOpen_deltaGenerated_iff, WithGeneratedByTopology.isOpen_iff]
    rfl
