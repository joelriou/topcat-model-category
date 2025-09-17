import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.RelativeT1CellComplex

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}} {K : TopCat.{u}} (f : K ⟶ |X|)

lemma exists_factor_thru_finite_of_topCatHom [CompactSpace K] :
    ∃ (A : X.Subcomplex) (_ : A.toSSet.IsFinite)
      (g : K ⟶ |A|), f = g ≫ toTop.map A.ι := by
  sorry

lemma exists_factor_thru_finite_connected_of_topCatHom [CompactSpace K] [PathConnectedSpace K] :
    ∃ (Y : SSet) (_ : Y.IsFinite) (_ : Y.IsConnected) (i : Y ⟶ X) (_ : Mono i)
      (g : K ⟶ |Y|), f = g ≫ toTop.map i := sorry

end SSet
