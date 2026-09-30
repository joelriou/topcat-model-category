module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] (P : ObjectProperty C)

section Limits

variable {J : Type*} [Category J]

def ιReflectsIsLimit {F : J ⥤ P.FullSubcategory} {c : Cone F} (h : IsLimit (P.ι.mapCone c)) :
    IsLimit c where
  lift s := ObjectProperty.homMk (h.lift (P.ι.mapCone s))
  fac s j := by ext : 1; exact h.fac (P.ι.mapCone s) j
  uniq s _ hm := by
    ext : 1
    exact h.hom_ext (fun j ↦ congr($(hm j).hom).trans (h.fac (P.ι.mapCone s) j).symm)

@[simps]
def coneOfCompι {F : J ⥤ P.FullSubcategory} (c : Cone (F ⋙ P.ι)) (h : P c.pt) : Cone F where
  pt := ⟨c.pt, h⟩
  π :=
    { app j := ObjectProperty.homMk (c.π.app j)
      naturality _ _ f := by ext : 1; exact c.π.naturality f }

def isLimitConeOfCompι {F : J ⥤ P.FullSubcategory} (c : Cone (F ⋙ P.ι))
    (hc : IsLimit c) (h : P c.pt) : IsLimit (P.coneOfCompι c h) :=
  ιReflectsIsLimit _ hc

lemma preservesLimit_of_limit_cone_comp_ι
    {F : J ⥤ P.FullSubcategory} (c : Cone (F ⋙ P.ι))
    (hc : IsLimit c) (h : P c.pt) :
    PreservesLimit F P.ι :=
  preservesLimit_of_preserves_limit_cone (P.isLimitConeOfCompι c hc h) hc

end Limits

section Colimits

variable {J : Type*} [Category J]

def ιReflectsIsColimit
    {F : J ⥤ P.FullSubcategory} {c : Cocone F} (h : IsColimit (P.ι.mapCocone c)) :
    IsColimit c where
  desc s := ObjectProperty.homMk (h.desc (P.ι.mapCocone s))
  fac s j := by ext : 1; exact h.fac (P.ι.mapCocone s) j
  uniq s _ hm := by
    ext : 1
    exact h.hom_ext (fun j ↦ (congr($(hm j).hom).trans (h.fac (P.ι.mapCocone s) j).symm))

@[simps]
def coconeOfCompι {F : J ⥤ P.FullSubcategory} (c : Cocone (F ⋙ P.ι)) (h : P c.pt) :
    Cocone F where
  pt := ⟨c.pt, h⟩
  ι :=
    { app j := ObjectProperty.homMk (c.ι.app j)
      naturality _ _ f := by ext : 1; exact c.ι.naturality f }

end Colimits

end CategoryTheory.ObjectProperty
