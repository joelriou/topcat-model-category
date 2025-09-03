import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.IsLimit

open CategoryTheory Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] (P : ObjectProperty C)

section Limits

variable {J : Type*} [Category J]

def ιReflectsIsLimit {F : J ⥤ P.FullSubcategory} {c : Cone F} (h : IsLimit (P.ι.mapCone c)) :
    IsLimit c where
  lift s := h.lift (P.ι.mapCone s)
  fac s := h.fac (P.ι.mapCone s)
  uniq s _ hm := h.hom_ext (fun j ↦ (hm j).trans (h.fac (P.ι.mapCone s) j).symm)

@[simps]
def coneOfCompι {F : J ⥤ P.FullSubcategory} (c : Cone (F ⋙ P.ι)) (h : P c.pt) : Cone F where
  pt := ⟨c.pt, h⟩
  π :=
    { app j := c.π.app j
      naturality _ _ f := c.π.naturality f }

end Limits

end CategoryTheory.ObjectProperty
