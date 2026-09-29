module

public import TopCatModelCategory.SSet.HasDimensionLT
public import TopCatModelCategory.SSet.Coproducts

@[expose] public section

universe v u

open CategoryTheory Limits

namespace SSet

variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J (Type u)]

instance : HasColimitsOfShape J SSet.{u} :=
  inferInstanceAs ( HasColimitsOfShape J (_ ⥤ _))

variable {F : J ⥤ SSet.{u}}

lemma hasDimensionLT_of_isColimit {c : Cocone F} (hc : IsColimit c) (d : ℕ)
    (h : ∀ (j : J), HasDimensionLT (F.obj j) d) : HasDimensionLT c.pt d := by
  rw [← hasDimensionLT_iff_of_iso (Subcomplex.topIso _),
    Subcomplex.top_eq_iSup_of_isColimit hc,
    hasDimensionLT_iSup_iff]
  intro j
  apply hasDimensionLT_of_epi (toRangeSubcomplex (c.ι.app j))

variable (F)

instance hasDimensionLT_colimit (d : ℕ)
    [∀ (j : J), HasDimensionLT (F.obj j) d] : HasDimensionLT (colimit F) d :=
  hasDimensionLT_of_isColimit (colimit.isColimit F) d inferInstance

end SSet
