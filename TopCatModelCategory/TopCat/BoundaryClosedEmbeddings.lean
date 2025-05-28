import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.Glueing

open CategoryTheory Simplicial MorphismProperty TopCat SSet.modelCategoryQuillen
  Topology Limits

namespace SSet

namespace Subcomplex

variable {X : SSet}

@[simps!]
protected noncomputable def toTop : X.Subcomplex ⥤ TopCat :=
  toPresheafFunctor ⋙ SSet.toTop

variable {Ω : Type} [TopologicalSpace Ω] (ι : |X| → Ω) (hι : IsClosedEmbedding ι)

@[simps]
def toTopSet : X.Subcomplex ⥤ Set Ω where
  obj A := Set.range (ι.comp (SSet.toTop.map A.ι))
  map {A₁ A₂} f := CategoryTheory.homOfLE (by
    rintro _ ⟨x, rfl⟩
    refine ⟨Subcomplex.toTop.map f x, ?_⟩
    dsimp
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, homOfLE_ι])

lemma toTopSet_iSup {α : Type*} (U : α → X.Subcomplex) :
    ⋃ i, (toTopSet ι).obj (U i) = (toTopSet ι).obj (⨆ i, U i) := by
  apply subset_antisymm
  · rw [Set.iUnion_subset_iff]
    intro i
    exact leOfHom ((toTopSet ι).map (CategoryTheory.homOfLE (le_iSup _ _)))
  · sorry

variable {ι}

noncomputable def toTopNatTrans : Subcomplex.toTop ⟶ toTopSet ι ⋙ Set.functorToTopCat where
  app A := ofHom ⟨fun x ↦ ⟨ι (SSet.toTop.map A.ι x), by simp⟩, by
    dsimp
    exact Continuous.subtype_mk (hι.continuous.comp
      (ContinuousMapClass.map_continuous _)) _⟩
  naturality {A₁ A₂} f := by
    ext x₁
    dsimp
    ext
    dsimp
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, homOfLE_ι]

lemma isIso_toTopNatTrans_app (A : X.Subcomplex)
    (hA : IsClosedEmbedding (ι.comp (SSet.toTop.map A.ι))) :
    IsIso ((toTopNatTrans hι).app A) := by
  have : (toTopNatTrans hι).app A = (isoOfHomeo hA.homeomorphRange).hom := rfl
  rw [this]
  infer_instance

variable {α : Type*} [Finite α] {A : X.Subcomplex} {U : α → X.Subcomplex}
  {V : α → α → X.Subcomplex}
  (h : CompleteLattice.MulticoequalizerDiagram A U V)

noncomputable def isColimitMulticoforkMapToTop :
    IsColimit (h.multicofork.map Subcomplex.toTop) :=
  Multicofork.isColimitMapEquiv _ toTop
    (isColimitOfPreserves SSet.toTop (multicoforkIsColimit h))

variable (hU : ∀ i, IsClosedEmbedding (ι.comp (SSet.toTop.map (U i).ι)))
  (hV : ∀ i j, (toTopSet ι).obj (U i) ⊓ (toTopSet ι).obj (U j) = (toTopSet ι).obj (V i j))

include h hU hV in
lemma multicoequalizerDiagram_toTopSet :
    TopCat.MulticoequalizerDiagram (X := .of Ω) ((toTopSet ι).obj A)
      (fun i ↦ (toTopSet ι).obj (U i)) (fun i j ↦ (toTopSet ι).obj (V i j)) := by
  apply MulticoequalizerDiagram.mk_of_isClosed
  · constructor
    · rw [Set.iSup_eq_iUnion, toTopSet_iSup, h.iSup_eq]
    · exact hV
  · intro i
    exact (hU i).isClosed_range

/-example : 0 = by
    have := (multicoequalizerDiagram_toTopSet h hU hV).multicofork
    sorry
    := sorry-/

end Subcomplex

lemma boundary.closedEmbeddings_toTop_map_ι (n : ℕ) :
    TopCat.closedEmbeddings (toTop.map ∂Δ[n].ι) := by
  sorry

instance (n : ℕ) : T2Space |Δ[n]| := ⦋n⦌.toTopHomeo.symm.t2Space

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
