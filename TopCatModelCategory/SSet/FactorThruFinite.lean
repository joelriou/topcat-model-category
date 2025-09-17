import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.RelativeT1CellComplex
import TopCatModelCategory.TopCat.CoyonedaPreservesCoproducts
import TopCatModelCategory.SSet.ConnectedComponents

universe u

open CategoryTheory Simplicial Limits Opposite

namespace SSet

variable {X : SSet.{u}} {K : TopCat.{u}} (f : K ⟶ |X|)

lemma exists_factor_thru_finite_of_topCatHom [CompactSpace K] :
    ∃ (A : X.Subcomplex) (_ : A.toSSet.IsFinite)
      (g : K ⟶ |A|), f = g ≫ toTop.map A.ι := by
  sorry

lemma exists_factor_thru_finite_of_topCatHom' [CompactSpace K] :
    ∃ (Y : SSet) (_ : Y.IsFinite) (i : Y ⟶ X) (_ : Mono i)
      (g : K ⟶ |Y|), f = g ≫ toTop.map i := by
  obtain ⟨A, _, g, rfl⟩ := exists_factor_thru_finite_of_topCatHom f
  exact ⟨_, inferInstance, A.ι, inferInstance, g, rfl⟩

lemma exists_factor_thru_finite_connected_of_topCatHom
    [CompactSpace K] [PathConnectedSpace K] :
    ∃ (Y : SSet) (_ : Y.IsFinite) (_ : Y.IsConnected) (i : Y ⟶ X) (_ : Mono i)
      (g : K ⟶ |Y|), f = g ≫ toTop.map i := by
  obtain ⟨Z, _, i, _, g, rfl⟩ := exists_factor_thru_finite_of_topCatHom' f
  obtain ⟨⟨c⟩, φ, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (coyoneda.obj (op (TopCat.of K)))
      (isColimitOfPreserves toTop (π₀.isColimitCofan Z))) g
  exact ⟨_, inferInstance, inferInstance, c.component.ι ≫ i, inferInstance, φ, by simp⟩

end SSet
