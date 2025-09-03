import TopCatModelCategory.Convenient.HomSpace
import TopCatModelCategory.Convenient.Limits
import Mathlib.CategoryTheory.Closed.Cartesian

open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe v v' v'' t u

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

lemma Topology.WithGeneratedByTopology.continuousGeneratedBy_continuous_equiv_symm
    {Y : Type*} [TopologicalSpace Y] :
      ContinuousGeneratedBy X (equiv (X := X) (Y := Y)).symm := by
  rw [continuousGeneratedBy_def]
  intro i f
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]
  exact f.continuous

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

namespace ContinuousGeneratedByCat

variable (Y : ContinuousGeneratedByCat.{v} X)

namespace CartesianClosed

def ihom : ContinuousGeneratedByCat.{v} X ⥤ ContinuousGeneratedByCat.{v} X where
  obj Z := of (ContinuousMapGeneratedBy X Y Z)
  map {Z₁ Z₂} p := ContinuousMapGeneratedBy.postcomp p

def ihomAdjunction : tensorLeft Y ⊣ ihom Y :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := ContinuousMapGeneratedBy.curryEquiv }

end CartesianClosed

instance : Exponentiable Y where
  rightAdj := CartesianClosed.ihom Y
  adj := CartesianClosed.ihomAdjunction Y

instance : CartesianClosed (ContinuousGeneratedByCat.{v} X) where

@[simps]
def isoOfWithGeneratedByTopology (Y : Type v) [TopologicalSpace Y] :
    of (X := X) Y ≅ of (WithGeneratedByTopology X Y) where
  hom :=
    { toFun := WithGeneratedByTopology.equiv.symm
      prop := WithGeneratedByTopology.continuousGeneratedBy_continuous_equiv_symm }
  inv :=
    { toFun := WithGeneratedByTopology.equiv (Y := Y)
      prop := WithGeneratedByTopology.continuous_equiv.continuousGeneratedBy }

end ContinuousGeneratedByCat

namespace GeneratedByTopCat

variable (Y₁ Y₂ : GeneratedByTopCat.{v} X)

namespace CartesianClosed

open ContinuousGeneratedByCat Functor

instance : (fromGeneratedByTopCat.{v} (X := X)).Monoidal :=
  CoreMonoidal.toMonoidal
  { εIso := Iso.refl _
    μIso _ _ := ContinuousGeneratedByCat.isoOfWithGeneratedByTopology _
    associativity _ _ _ := by
      ext ⟨⟨y₁, y₂⟩, y₃⟩
      exact Prod.ext (show y₁ = y₁ by rfl)
        (Prod.ext (show y₂ = y₂ by rfl) (show y₃ = y₃ by rfl)) }

noncomputable def tensorLeftIso :
    tensorLeft Y₁ ≅ fromGeneratedByTopCat ⋙
      tensorLeft (fromGeneratedByTopCat.obj Y₁) ⋙ toGeneratedByTopCat :=
  (Functor.rightUnitor _).symm ≪≫ isoWhiskerLeft _ equivalence.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Monoidal.commTensorLeft fromGeneratedByTopCat Y₁).symm
      toGeneratedByTopCat ≪≫ Functor.associator _ _ _

noncomputable def adj : tensorLeft Y₁ ⊣ fromGeneratedByTopCat ⋙
    ihom (fromGeneratedByTopCat.obj Y₁) ⋙ toGeneratedByTopCat :=
  (Adjunction.comp (equivalence.toAdjunction.comp (ihom.adjunction _))
    equivalence.symm.toAdjunction).ofNatIsoLeft
    (Functor.associator _ _ _≪≫ (tensorLeftIso Y₁).symm)

end CartesianClosed

noncomputable instance : Exponentiable Y₁ where
  rightAdj := _
  adj := CartesianClosed.adj Y₁

noncomputable instance : CartesianClosed (GeneratedByTopCat.{v} X) where

end GeneratedByTopCat
