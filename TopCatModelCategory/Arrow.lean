import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.TypesFiltered
import TopCatModelCategory.ColimitsType

universe u

namespace CategoryTheory

open Limits

namespace Arrow

variable (C : Type u) [Category.{v} C]

def cartesianMorphisms : MorphismProperty (Arrow C) :=
  fun X Y f ↦
    IsPullback f.left X.hom Y.hom f.right

variable {C} in
@[simp]
lemma cartesianMorphisms_iff {X Y : Arrow C} (f : X ⟶ Y) :
    cartesianMorphisms C f ↔ IsPullback f.left X.hom Y.hom f.right := Iff.rfl

instance : (cartesianMorphisms C).RespectsIso :=
  .of_respects_arrow_iso _ (by
    intro f g e hf
    simp only [Functor.id_obj, cartesianMorphisms_iff] at hf ⊢
    exact IsPullback.of_iso hf ((leftFunc ⋙ leftFunc).mapIso e)
      ((rightFunc ⋙ leftFunc).mapIso e) ((leftFunc ⋙ rightFunc).mapIso e)
      ((rightFunc ⋙ rightFunc).mapIso e) (leftFunc.congr_map e.hom.w.symm)
      (by simp) (by simp) (rightFunc.congr_map e.hom.w.symm))

/-lemma isStableUnderColimitsOfShape_cartesianMorphisms (J : Type*) [Category J]
    [HasColimitsOfShape J C] [PreservesLimitsOfShape WalkingCospan (colim : (J ⥤ C) ⥤ C)] :
    (cartesianMorphisms C).IsStableUnderColimitsOfShape J := by
  sorry-/

lemma isStableUnderColimitsOfShape_cartesianMorphisms_type (J : Type*) [Category J]
    [HasColimitsOfShape J (Type u)] [IsFiltered J] :
    (cartesianMorphisms (Type u)).IsStableUnderColimitsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  generalize hφ : hc₁.desc { ι := f ≫ c₂.ι } = φ
  have hφ' (j) : c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j := by simp [← hφ]
  replace hf (j) := hf j
  simp only [cartesianMorphisms_iff, Functor.id_obj] at hf ⊢
  rw [Types.isPullback_iff]
  refine ⟨φ.w, ?_, ?_⟩
  · rintro x₁ x₁' ⟨h₁, h₂⟩
    obtain ⟨j₁, w₁, w₁', rfl, rfl⟩ :
        ∃ j w₁ w₁', x₁ = (c₁.ι.app j).left w₁ ∧ x₁' = (c₁.ι.app j).left w₁' := by
      obtain ⟨j, w₁, rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves Arrow.leftFunc hc₁) x₁
      obtain ⟨j', w₁', rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves Arrow.leftFunc hc₁) x₁'
      refine ⟨IsFiltered.max j j', (X₁.map (IsFiltered.leftToMax j j')).left w₁,
        (X₁.map (IsFiltered.rightToMax j j')).left w₁', ?_, ?_⟩
      · apply congr_fun (leftFunc.congr_map (Cocone.w c₁ (IsFiltered.leftToMax j j')).symm) w₁
      · apply congr_fun (leftFunc.congr_map (Cocone.w c₁ (IsFiltered.rightToMax j j')).symm) w₁'
    dsimp at h₁ h₂ ⊢
    obtain ⟨j₂, f₁₂, hj₂⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves Arrow.leftFunc hc₂)
        ((f.app j₁).left w₁) ((f.app j₁).left w₁')).1 (by
          convert h₁
          all_goals apply congr_fun (leftFunc.congr_map (hφ' j₁)).symm)
    obtain ⟨j₃, f₁₃, hj₃⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves Arrow.rightFunc hc₁) ((X₁.obj j₁).hom w₁) ((X₁.obj j₁).hom w₁')).1 (by
        convert h₂
        all_goals apply congr_fun (c₁.ι.app j₁).w.symm)
    dsimp at hj₂ hj₃
    obtain ⟨j₄, f₁₄, eq₁, eq₂⟩ :
        ∃ (j₄ : J) (f₁₄ : j₁ ⟶ j₄), (X₂.map f₁₄).left ((f.app j₁).left w₁) =
      (X₂.map f₁₄).left ((f.app j₁).left w₁') ∧
      (X₁.map f₁₄).right ((X₁.obj j₁).hom w₁) = (X₁.map f₁₄).right ((X₁.obj j₁).hom w₁') := by
      obtain ⟨j₄, f₂₄, f₃₄, eq⟩ := IsFiltered.span f₁₂ f₁₃
      refine ⟨j₄, f₁₂ ≫ f₂₄, ?_⟩
      constructor
      · simp [hj₂]
      · simp [eq, hj₃]
    simp only [← Cocone.w c₁ f₁₄]
    dsimp
    apply congr_arg
    apply Types.ext_of_isPullback (hf j₄)
    · convert eq₁ using 1
      all_goals apply congr_fun (leftFunc.congr_map (f.naturality f₁₄))
    · convert eq₂ using 1
      all_goals apply congr_fun (X₁.map f₁₄).w
  · intro x₂ x₁ hx
    obtain ⟨j₁, x₁, rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves Arrow.rightFunc hc₁) x₁
    obtain ⟨j₂, x₂, rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves Arrow.leftFunc hc₂) x₂
    dsimp at x₁ x₂ hx ⊢
    obtain ⟨j₃, f₁₃, f₂₃, eq⟩ := (Types.FilteredColimit.isColimit_eq_iff _
      (isColimitOfPreserves Arrow.rightFunc hc₂)
      (xi := (f.app j₁).right x₁) (xj := (X₂.obj j₂).hom x₂)).1 (by
        convert hx.symm using 1
        · apply congr_fun (rightFunc.congr_map (hφ' j₁).symm)
        · exact (congr_fun (c₂.ι.app j₂).w x₂).symm)
    dsimp at eq
    obtain ⟨y, hy₁, hy₂⟩ := Types.exists_of_isPullback (hf j₃) ((X₂.map f₂₃).left x₂)
      ((X₁.map f₁₃).right x₁) (by
        convert eq.symm using 1
        · apply congr_fun (X₂.map f₂₃).w
        · apply congr_fun (rightFunc.congr_map (f.naturality f₁₃)))
    refine ⟨(c₁.ι.app j₃).left y, ?_, ?_⟩
    · rw [← Cocone.w c₂ f₂₃]
      dsimp
      rw [hy₁]
      apply congr_fun (leftFunc.congr_map (hφ' j₃)).symm
    · rw [← Cocone.w c₁ f₁₃]
      dsimp
      rw [hy₂]
      apply congr_fun (c₁.ι.app j₃).w.symm

end Arrow

end CategoryTheory
