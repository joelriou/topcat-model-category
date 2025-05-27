import TopCatModelCategory.TopCat.Adj

open CategoryTheory Simplicial MorphismProperty TopCat SSet.modelCategoryQuillen

namespace SSet

instance (n : ℕ) : T2Space |Δ[n]| := ⦋n⦌.toTopHomeo.symm.t2Space

lemma boundary.closedEmbeddings_toTop_map_ι (n : ℕ) :
    TopCat.closedEmbeddings (toTop.map ∂Δ[n].ι) := sorry

lemma boundary.t₁Inclusions_toTop_map_ι (n : ℕ) :
    TopCat.t₁Inclusions (toTop.map ∂Δ[n].ι) :=
  ⟨closedEmbeddings_toTop_map_ι n, fun _ _ ↦ isClosed_singleton⟩

lemma t₁Inclusions_toObj_map_of_mono {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] :
    t₁Inclusions (SSet.toTop.map i) := by
  have : (MorphismProperty.coproducts.{0, 0, 1} I).pushouts ≤
      (t₁Inclusions.{0}).inverseImage SSet.toTop := by
    rw [← MorphismProperty.map_le_iff]
    refine ((coproducts I).map_pushouts_le SSet.toTop).trans ?_
    simp only [pushouts_le_iff]
    refine (I.map_coproducts_le SSet.toTop).trans ?_
    simp only [coproducts_le_iff, MorphismProperty.map_le_iff]
    intro _ _ _ ⟨n⟩
    apply SSet.boundary.t₁Inclusions_toTop_map_ι
  exact t₁Inclusions.isT₁Inclusion_of_transfiniteCompositionOfShape
    ((transfiniteCompositionOfMono i).ofLE this).map

end SSet
