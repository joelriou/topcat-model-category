import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] {X : C}

lemma IsTerminal.preservesLimit (hX : IsTerminal X) {F : C ⥤ D}
    (hX' : IsTerminal (F.obj X)) :
    PreservesLimit (Functor.empty.{0} C) F :=
  preservesLimit_of_preserves_limit_cone hX (by
    refine (IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_).1 hX'
    exact Cones.ext (Iso.refl _))

lemma IsTerminal.preservesTerminal (hX : IsTerminal X) {F : C ⥤ D}
    (hX' : IsTerminal (F.obj X)) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) F where
  preservesLimit {K} := by
    have := IsTerminal.preservesLimit hX hX'
    exact preservesLimit_of_iso_diagram _ ((Functor.empty C).emptyExt K)

end CategoryTheory.Limits
