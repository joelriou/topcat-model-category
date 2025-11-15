import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

-- #31645

namespace CategoryTheory

open Limits

variable (K J C : Type*) [Category K] [Category J] [Category C]

namespace ObjectProperty

variable {J C}

def preservesLimitsOfShape : ObjectProperty (J ⥤ C) :=
  fun F ↦ PreservesLimitsOfShape K F

@[simp]
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl

def preservesFiniteLimits : ObjectProperty (J ⥤ C) :=
  fun F ↦ PreservesFiniteLimits F

@[simp]
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl

variable (J C) in
instance closedUnderColimitsOfShape_preservesLimitsOfShape (K' : Type*) [Category K']
    [HasColimitsOfShape K' C] [HasLimitsOfShape K C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)) K' := by
  -- the proof needs a small fix
  suffices ∀ (F : K' ⥤ J ⥤ C) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ x, preservesLimitsOfShape K (F.obj x)), preservesLimitsOfShape K c.pt from ⟨by
      rintro F ⟨h⟩
      exact this _ _ h.isColimit h.prop_diag_obj⟩
  intro F c hc h
  simp only [preservesLimitsOfShape_iff] at h ⊢
  have : PreservesLimitsOfShape K F.flip := ⟨fun {G} ↦ ⟨fun {c} hc ↦
    ⟨evaluationJointlyReflectsLimits _ (fun k' ↦ isLimitOfPreserves (F.obj k') hc)⟩⟩⟩
  let e : F.flip ⋙ colim ≅ c.pt :=
    NatIso.ofComponents (fun j ↦ (colimit.isColimit (F.flip.obj j)).coconePointUniqueUpToIso
      (isColimitOfPreserves ((evaluation _ _).obj j) hc))
  exact preservesLimitsOfShape_of_natIso e

variable (J C) in
instance closedUnderColimitsOfShape_preservesFiniteLimits (K' : Type*) [Category K']
    [HasColimitsOfShape K' C] [HasFiniteLimits C]
    [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' := by
  -- the proof needs a small fix
  suffices ∀ (F : K' ⥤ J ⥤ C) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ x, preservesFiniteLimits (F.obj x)), preservesFiniteLimits c.pt from ⟨by
      rintro F ⟨h⟩
      exact this _ _ h.isColimit h.prop_diag_obj⟩
  intro F c hc h
  constructor
  intro K _ _
  simp only [preservesFiniteLimits_iff] at h
  exact (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).prop_of_isColimit hc
    (fun k' ↦ by
      rw [preservesLimitsOfShape_iff]
      infer_instance)
