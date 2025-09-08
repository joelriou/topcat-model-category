import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

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
lemma closedUnderColimitsOfShape_preservesLimitsOfShape (K' : Type*) [Category K']
    [HasColimitsOfShape K' C] [HasLimitsOfShape K C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    ClosedUnderColimitsOfShape K' (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)) := by
  sorry

variable (J C) in
lemma closedUnderColimitsOfShape_preservesFiniteLimits (K' : Type*) [Category K']
    [HasColimitsOfShape K' C] [HasFiniteLimits C]
    [HasExactColimitsOfShape K' C] :
    ClosedUnderColimitsOfShape K' (preservesFiniteLimits : ObjectProperty (J ⥤ C)) := by
  intro F c hc h
  constructor
  intro K _ _
  simp only [preservesFiniteLimits_iff] at h
  exact closedUnderColimitsOfShape_preservesLimitsOfShape K J C K' hc (fun k' ↦ by
    rw [preservesLimitsOfShape_iff]
    infer_instance)
