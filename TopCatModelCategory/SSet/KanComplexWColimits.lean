import TopCatModelCategory.SSet.KanComplexW

universe u

open CategoryTheory Limits

namespace SSet

namespace KanComplex

namespace W

variable (J : Type*) [Category J]

lemma isStableUnderColimitsOfShape [HasColimitsOfShape J (Type u)] [IsFiltered J] :
    W.{u}.IsStableUnderColimitsOfShape J := by
  sorry

end W

end KanComplex

end SSet
