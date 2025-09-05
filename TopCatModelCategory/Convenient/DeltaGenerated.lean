import Mathlib.Data.Finite.Sum
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import TopCatModelCategory.Convenient.OpenBall
import TopCatModelCategory.Convenient.CartesianClosed

universe u

open CategoryTheory MonoidalCategory Topology

abbrev DeltaGeneratedSpace' (X : Type u) [TopologicalSpace X] : Prop :=
  IsGeneratedBy (fun n ↦ (Fin n → ℝ)) X

abbrev DeltaGenerated' := GeneratedByTopCat.{u} (fun n ↦ (Fin n → ℝ))

instance {ι : Type*} [Finite ι] : DeltaGeneratedSpace' (ι → ℝ) :=
  have := Fintype.ofFinite ι
  (Homeomorph.piCongrLeft (Y := fun _ ↦ ℝ)
    (Fintype.equivFin ι)).symm.isQuotientMap.isGeneratedBy

instance (ι₁ ι₂ : Type*) [Finite ι₁] [Finite ι₂] :
    DeltaGeneratedSpace' ((ι₁ → ℝ) × (ι₂ → ℝ)) :=
  Homeomorph.sumArrowHomeomorphProdArrow.isQuotientMap.isGeneratedBy

lemma IsOpen.DeltaGeneratedSpace'
    {Y : Type u} [TopologicalSpace Y] [DeltaGeneratedSpace' Y] {U : Set Y} (hU : IsOpen U) :
    DeltaGeneratedSpace' U := by
  exact hU.isGeneratedBy

instance {Y : Type u} [TopologicalSpace Y] [DeltaGeneratedSpace' Y]
    (U : TopologicalSpace.Opens Y) :
    DeltaGeneratedSpace' U :=
  U.isOpen.isGeneratedBy

noncomputable example : CartesianClosed (DeltaGenerated'.{u}) := by infer_instance
