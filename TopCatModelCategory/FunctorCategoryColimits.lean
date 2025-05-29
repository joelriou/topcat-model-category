import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic

namespace CategoryTheory

open Limits

variable (K J C : Type*) [Category K] [Category J] [Category C]

namespace ObjectProperty

variable {J C}

def preservesColimitsOfShape : ObjectProperty (J ⥤ C) :=
  fun F ↦ Limits.PreservesColimitsOfShape K F

@[simp]
lemma preservesColimitsOfShape_iff (F : J ⥤ C) :
    preservesColimitsOfShape K F ↔ PreservesColimitsOfShape K F := Iff.rfl

variable (J C) in
lemma closedUnderColimitsOfShape_preservesColimitsOfShape (K' : Type*) [Category K']
    [HasColimitsOfShape K' C] :
    ClosedUnderColimitsOfShape K' (preservesColimitsOfShape K : ObjectProperty (J ⥤ C)) := by
  intro F c hc hF
  simp only [preservesColimitsOfShape_iff] at hF ⊢
  refine ⟨fun {G} ↦ ⟨fun {d} hd ↦ ⟨?_⟩⟩⟩
  let cocone' (s : Cocone (G ⋙ c.pt)) (k' : K') : Cocone (G ⋙ F.obj k') :=
    Cocone.mk s.pt
      { app k := (c.ι.app k').app (G.obj k) ≫ s.ι.app k
        naturality k₁ k₂ f := by
          have := Cocone.w s f
          dsimp at this ⊢
          rw [NatTrans.naturality_assoc, Category.comp_id, this] }
  let cocone (s : Cocone (G ⋙ c.pt)) : Cocone (F ⋙ (evaluation J C).obj d.pt) :=
    Cocone.mk s.pt
      { app k' := (isColimitOfPreserves (F.obj k') hd).desc (cocone' s k')
        naturality k'₁ k'₂ f := by
          dsimp
          rw [Category.comp_id]
          apply (isColimitOfPreserves (F.obj k'₁) hd).hom_ext
          intro k
          have h₁ := (isColimitOfPreserves (F.obj k'₁) hd).fac (cocone' s k'₁) k
          have h₂ := (isColimitOfPreserves (F.obj k'₂) hd).fac (cocone' s k'₂) k
          dsimp at h₁ h₂ ⊢
          rw [h₁, NatTrans.naturality_assoc, h₂]
          dsimp [cocone']
          rw [← Cocone.w c f, NatTrans.comp_app_assoc] }
  exact
    { desc s := (isColimitOfPreserves ((evaluation J C).obj d.pt) hc).desc (cocone s)
      fac s k := by
        apply (isColimitOfPreserves ((evaluation J C).obj (G.obj k)) hc).hom_ext
        intro k'
        have h₁ := (isColimitOfPreserves ((evaluation J C).obj d.pt) hc).fac (cocone s) k'
        have h₂ := (isColimitOfPreserves (F.obj k') hd).fac (cocone' s k') k
        dsimp at h₁ h₂ ⊢
        rw [← NatTrans.naturality_assoc, h₁]
        dsimp [cocone]
        rw [h₂]
      uniq s m hm := by
        dsimp
        apply (isColimitOfPreserves ((evaluation J C).obj d.pt) hc).hom_ext
        intro k'
        have h₁ := (isColimitOfPreserves ((evaluation J C).obj d.pt) hc).fac (cocone s) k'
        dsimp at h₁ ⊢
        rw [h₁]
        dsimp [cocone]
        apply (isColimitOfPreserves (F.obj k') hd).hom_ext
        intro k
        have h₂ := (isColimitOfPreserves (F.obj k') hd).fac (cocone' s k')
        dsimp at h₂ ⊢
        rw [h₂]
        dsimp [cocone']
        simp [← hm] }

end ObjectProperty

end CategoryTheory
