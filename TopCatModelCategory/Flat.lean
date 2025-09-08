import Mathlib.CategoryTheory.Limits.Presheaf
import TopCatModelCategory.LeftKanExtensionAlongUliftYoneda
import TopCatModelCategory.FunctorCategoryLimits
import TopCatModelCategory.HasExactColimitsOfShape

universe w w' v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

@[reassoc]
lemma uliftYonedaEquiv_symm_app_apply {P₁ P₂ : Cᵒᵖ ⥤ Type max w v} (f : P₁ ⟶ P₂)
    {X : C} (x : P₁.obj (op X)) :
    uliftYonedaEquiv.symm (f.app _ x) = uliftYonedaEquiv.symm x ≫ f := by
  apply uliftYonedaEquiv.injective
  rw [Equiv.apply_symm_apply, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

namespace Presheaf

variable {F : C ⥤ Type max w u v} {G : (Cᵒᵖ ⥤ Type max w u v) ⥤ Type max w u v}
  (τ : F ⟶ uliftYoneda.{max w u} ⋙ G)

@[simps]
def coconeExtensionAlongUliftYoneda :
    Cocone ((CategoryOfElements.π F).op ⋙ evaluation _ (Type max w u v)) where
  pt := G
  ι :=
    { app p :=
        { app P x := G.map (uliftYonedaEquiv.symm x) (τ.app _ p.unop.2)
          naturality P₁ P₂ f := by
            dsimp
            ext x
            simp only [types_comp_apply, uliftYonedaEquiv_symm_app_apply, G.map_comp] }
      naturality p q φ := by
        ext P x
        dsimp at x ⊢
        rw [uliftYonedaEquiv_symm_map φ.unop.1.op, G.map_comp, types_comp_apply]
        have := congr_fun (τ.naturality φ.unop.1).symm q.unop.2
        dsimp at this ⊢
        simp [this] }

variable [G.IsLeftKanExtension τ]

def isColimitCoconeExtensionAlongUliftYoneda :
    IsColimit (coconeExtensionAlongUliftYoneda τ) :=
  evaluationJointlyReflectsColimits _ (fun P ↦ by
    obtain ⟨h₁, h₂⟩ := (isLeftKanExtension_along_uliftYoneda_iff' G τ).1 inferInstance
    have := isColimitOfPreserves G (colimitOfRepresentable.{max w u} P)
    sorry)

variable [IsCofiltered F.Elements]

open ObjectProperty in
include τ in
lemma preservesFiniteLimits_of_isCofiltered_elements :
    PreservesFiniteLimits G :=
  closedUnderColimitsOfShape_preservesFiniteLimits _ _ _
    (isColimitCoconeExtensionAlongUliftYoneda.{w} τ) (by
      simp only [Functor.comp_obj, Functor.op_obj, CategoryOfElements.π_obj,
        preservesFiniteLimits_iff]
      infer_instance)

end Presheaf

end CategoryTheory
