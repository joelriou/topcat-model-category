import TopCatModelCategory.PullbackTypes
import TopCatModelCategory.SSet.Monoidal
import TopCatModelCategory.Pullback
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Over

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory Limits

namespace SSet

namespace Subcomplex

variable {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S)

def pullback : Subcomplex (X ⊗ Y) where
  obj n := setOf (fun x ↦ f.app _ x.1 = g.app _ x.2)
  map {n m} g := fun ⟨x, y⟩ hx ↦ by
    simpa only [← FunctorToTypes.naturality] using congr_arg (S.map g) hx

lemma mem_pullback_iff {n : SimplexCategoryᵒᵖ} (z : (X ⊗ Y).obj n) :
    z ∈ (pullback f g).obj _ ↔ f.app _ z.1 = g.app _ z.2 := Iff.rfl

abbrev pullbackπ₁ : (pullback f g : SSet) ⟶ X :=
  Subcomplex.ι _ ≫ fst _ _

abbrev pullbackπ₂ : (pullback f g : SSet) ⟶ Y :=
  Subcomplex.ι _ ≫ snd _ _

lemma isPullback :
    IsPullback (Subcomplex.pullbackπ₁ f g) (Subcomplex.pullbackπ₂ f g) f g where
  w := by ext _ ⟨_, hx⟩; exact hx
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun _ ↦
    (PullbackCone.isLimitMapConeEquiv ..).2 (Types.pullbackLimitCone _ _).isLimit)⟩

end Subcomplex

variable {E B : SSet.{u}} (p : E ⟶ B)

@[simps]
def overPullback : Over B ⥤ Over E where
  obj S := Over.mk (Subcomplex.pullbackπ₂ S.hom p)
  map {S₁ S₂} φ :=
    Over.homMk (Subcomplex.lift
      (lift (Subcomplex.pullbackπ₁ _ _ ≫ φ.left) (Subcomplex.pullbackπ₂ _ _)) (by
        simp only [Functor.const_obj_obj, Functor.id_obj, Subcomplex.preimage_eq_top_iff]
        rintro n _ ⟨⟨x, hx⟩, rfl⟩
        rw [Subcomplex.mem_pullback_iff] at hx ⊢
        dsimp
        rwa [← FunctorToTypes.comp, Over.w φ])) rfl

def overPullbackCompPostEvaluation (n : SimplexCategoryᵒᵖ) :
    overPullback p ⋙ Over.post ((evaluation _ _ ).obj n) ≅
      Over.post ((evaluation _ _ ).obj n) ⋙ Types.overPullback (p.app n) :=
  Iso.refl _

noncomputable def overPullbackIso : overPullback p ≅ Over.pullback p :=
  NatIso.ofComponents
    (fun S ↦ Over.pullbackObjIsoOfIsPullback (Subcomplex.isPullback S.hom p)) (fun {X Y} f ↦ by
      ext : 1
      dsimp
      ext : 1 <;> simp)

section

variable {J : Type*} [Category J] [HasColimitsOfShape J (Type u)]

instance (n : SimplexCategoryᵒᵖ) (X : SSet.{u}) :
    PreservesColimitsOfShape J (Over.post (X := X) (SSet.evaluation.obj n)) where
  preservesColimit := ⟨fun hc ↦ ⟨isColimitOfReflects (Over.forget _)
    (isColimitOfPreserves (Over.forget _ ⋙ SSet.evaluation.obj n) hc)⟩⟩

instance (F : J ⥤ Over B) : PreservesColimit F (overPullback p) where
  preserves hc := ⟨isColimitOfReflects (Over.forget E)
    (evaluationJointlyReflectsColimits _ (fun n ↦
      isColimitOfPreserves (Over.post (SSet.evaluation.obj n) ⋙
        Types.overPullback (p.app n) ⋙ Over.forget _) hc))⟩

instance : PreservesColimitsOfShape J (overPullback p) where

instance : PreservesColimitsOfShape J (Over.pullback p) :=
  preservesColimitsOfShape_of_natIso (overPullbackIso p)

end

end SSet
