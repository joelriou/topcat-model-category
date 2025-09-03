import TopCatModelCategory.Convenient.Category
import Mathlib.CategoryTheory.Limits.IsLimit

universe v t u

open CategoryTheory Topology Limits

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

variable {J : Type*} [Category J]

namespace ContinuousGeneratedByCat

def isLimitMapConeToContinuousGeneratedByCat {F : J ⥤ TopCat.{v}}
    {c : Cone F} (hc : IsLimit c) :
    IsLimit ((TopCat.toContinuousGeneratedByCat X).mapCone c) where
  lift s := by
    sorry
  fac := sorry
  uniq := sorry


end ContinuousGeneratedByCat
