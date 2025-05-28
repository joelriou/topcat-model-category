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

omit [TopologicalSpace Ω] in
lemma toTopSet_obj_subset (A : X.Subcomplex) : (toTopSet ι).obj A ⊆ Set.range ι := by
  rintro _ ⟨a, rfl⟩
  simp

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

lemma surjective_toTopNatTrans_app (A : X.Subcomplex) :
    Function.Surjective ((toTopNatTrans hι).app A) := by
  sorry

instance (A : X.Subcomplex) :
    Epi ((toTopNatTrans hι).app A) := by
  rw [TopCat.epi_iff_surjective]
  apply surjective_toTopNatTrans_app

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

@[simps!]
noncomputable def multispanHom :
    (h.multispanIndex.map Subcomplex.toTop).multispan ⟶
      (multicoequalizerDiagram_toTopSet h hU hV).multispanIndex.multispan :=
  MultispanIndex.multispan.homMk (fun ⟨i, j⟩ ↦ (toTopNatTrans hι).app (V i j))
    (fun i ↦ (toTopNatTrans hι).app (U i))
    (fun ⟨i, j⟩ ↦
      (toTopNatTrans hι).naturality (CategoryTheory.homOfLE (by
        dsimp
        rw [← h.min_eq]
        exact inf_le_left)))
    (fun ⟨i, j⟩ ↦
      (toTopNatTrans hι).naturality (CategoryTheory.homOfLE (by
        dsimp
        rw [← h.min_eq]
        exact inf_le_right)))

noncomputable def isColimitCoconesPrecomposeMultispanHom :
    IsColimit ((Cocones.precompose (multispanHom hι h hU hV)).obj
      (multicoequalizerDiagram_toTopSet h hU hV).multicofork) :=
  Multicofork.isColimitPrecomposeObjOfIsIsoOfEpi
        (multispanHom hι h hU hV)
          (multicoequalizerDiagram_toTopSet h hU hV).multicoforkIsColimit
            (fun i ↦ isIso_toTopNatTrans_app hι _ (hU i)) (fun ⟨i, j⟩ ↦ by
              dsimp
              infer_instance)

include hι h hU hV in
lemma closedEmbeddings_toTop_map_ι :
    TopCat.closedEmbeddings (toTop.map A.ι) := by
  let Z := Set.range (ι ∘ toTop.map A.ι)
  let iZ : TopCat.of Z ⟶ TopCat.of (Set.range ι) :=
    ofHom ⟨fun ⟨x, hx⟩ ↦ ⟨x, toTopSet_obj_subset ι A hx⟩, by continuity⟩
  let j : TopCat.of (Set.range ι) ⟶ TopCat.of Ω :=
    ofHom ⟨fun ⟨x, _⟩ ↦ x, by continuity⟩
  have : Mono j := by
    apply (CategoryTheory.forget _).mono_of_mono_map
    rw [CategoryTheory.mono_iff_injective]
    exact Subtype.val_injective
  have h₁ := isColimitMulticoforkMapToTop h
  have h₂ := isColimitCoconesPrecomposeMultispanHom hι h hU hV
  let e := IsColimit.coconePointUniqueUpToIso h₁ h₂
  have he (i : α) (x) :
      (e.hom ((h.multicofork.map Subcomplex.toTop).π i x)).1 =
        ι (toTop.map (U i).ι x) := by
    dsimp [CompleteLattice.MulticoequalizerDiagram.multicofork,
      Multicofork.ofπ, Multicofork.map, Multicofork.π]
    have := congr_fun ((CategoryTheory.forget _).congr_map
      (IsColimit.comp_coconePointUniqueUpToIso_hom h₁ h₂ (.right i))) x
    dsimp at this
    rwa [Subtype.ext_iff] at this
  have : Arrow.mk (toTop.map A.ι) ≅ Arrow.mk iZ :=
    Arrow.isoMk e (isoOfHomeo hι.homeomorphRange) (by
      rw [← cancel_mono j]
      apply Multicofork.IsColimit.hom_ext h₁
      intro i
      ext x
      dsimp at i x ⊢
      refine (he i x).trans ?_
      dsimp [CompleteLattice.MulticoequalizerDiagram.multicofork,
        Multicofork.ofπ, Multicofork.map, Multicofork.π]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
  rw [closedEmbeddings.arrow_mk_iso_iff this]
  apply IsClosedEmbedding.inclusion
  · rintro _ ⟨x, rfl⟩
    simp
  · apply IsClosed.preimage continuous_subtype_val
    have := toTopSet_iSup ι U
    rw [h.iSup_eq] at this
    change _ = Z at this
    rw [← this]
    exact isClosed_iUnion_of_finite (fun i ↦ (hU i).isClosed_range)

end Subcomplex

open NNReal

namespace boundary.closedEmbeddings_toTop_map_ι

variable (n : ℕ)

def ι' : ⦋n⦌.toTopObj → (Fin (n + 1) → ℝ≥0) := Subtype.val
lemma hι' : IsClosedEmbedding (ι' n) :=
  Topology.IsClosedEmbedding.subtypeVal (IsCompact.isClosed (by
    rw [isCompact_iff_compactSpace, Set.setOf_mem_eq]
    infer_instance))

noncomputable def ι : |Δ[n]| → (Fin (n + 1) → ℝ≥0) := ι' n ∘ ⦋n⦌.toTopHomeo

lemma hι : IsClosedEmbedding (ι n) :=
    (hι' n).comp (Homeomorph.isClosedEmbedding _)

variable {n}

lemma injective_toTopMap_stdSimplex_map_of_mono
    {n m : SimplexCategory} (i : n ⟶ m) (hi : Mono i) :
    Function.Injective (SimplexCategory.toTop.map i) := by
  rw [SimplexCategory.mono_iff_injective] at hi
  intro f₁ f₂ h
  dsimp at h
  rw [Subtype.ext_iff] at h ⊢
  funext j
  have (f : SimplexCategory.toTop.obj n) : f.1 j = SimplexCategory.toTopMap i f (i j) := by
    dsimp
    rw [Finset.sum_eq_single j _ (by simp)]
    rintro b hb hb'
    exact (hb' (hi (by simpa using hb))).elim
  simp only [this, h]

lemma injective_toTop_map_stdSimplex_map_of_mono
    {n m : SimplexCategory} (i : n ⟶ m) (hi : Mono i) :
    Function.Injective (toTop.map (stdSimplex.map i)) := by
  refine ((MorphismProperty.injective _).arrow_mk_iso_iff ?_).2
    (injective_toTopMap_stdSimplex_map_of_mono i hi)
  refine Arrow.isoMk (isoOfHomeo n.toTopHomeo) (isoOfHomeo m.toTopHomeo) ?_
  exact (forget _).map_injective
    (SimplexCategory.toTopHomeo_naturality i).symm

lemma injective_toTop_map_face_ι (S : Finset (Fin (n + 1))) :
    Function.Injective (toTop.map (stdSimplex.face S).ι) := by
  dsimp [Subcomplex.toTopSet]
  generalize h : S.card = m
  obtain _ | m := m
  · have hS : IsInitial (toTop.obj (stdSimplex.face S)) := by
      obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
      rw [stdSimplex.face_emptySet]
      apply IsInitial.isInitialObj
      exact Subcomplex.botIsInitial
    have := (Types.initial_iff_empty _).1 ⟨hS.isInitialObj (forget _)⟩
    exact this.elim
  · let e := S.orderIsoOfFin h
    let φ : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom
      ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)
    have iso : Arrow.mk (stdSimplex.{0}.map φ) ≅ Arrow.mk (stdSimplex.face S).ι :=
      Arrow.isoMk (stdSimplex.isoOfRepresentableBy (stdSimplex.faceRepresentableBy _ _ e))
        (Iso.refl _) (by
          dsimp
          simp only [Category.comp_id]
          apply yonedaEquiv.injective
          rw [yonedaEquiv_comp]
          rfl)
    exact ((MorphismProperty.injective _).arrow_mk_iso_iff (toTop.mapArrow.mapIso iso)).1
      (injective_toTop_map_stdSimplex_map_of_mono φ (by
        rw [SimplexCategory.mono_iff_injective]
        intro _ _ _
        aesop))

lemma toTopSet_obj_face_compl (S : Finset (Fin (n + 1))) :
    (Subcomplex.toTopSet (ι n)).obj (stdSimplex.face Sᶜ) =
      ⦋n⦌.toTopObj ⊓ (⨅ (i : S), { f | f i.1 = 0}) := by
  dsimp [Subcomplex.toTopSet]
  sorry

lemma toTopSet_obj_face_singleton_compl (i : Fin (n + 1)) :
    (Subcomplex.toTopSet (ι n)).obj
      (stdSimplex.face {i}ᶜ) =
    ⦋n⦌.toTopObj ⊓ { f | f i = 0 } := by
  rw [toTopSet_obj_face_compl]
  simp

lemma toTopSet_obj_face_pair_compl (i j : Fin (n + 1)) :
    (Subcomplex.toTopSet (ι n)).obj
      (stdSimplex.face {i, j}ᶜ) =
    ⦋n⦌.toTopObj ⊓ { f | f i = 0 } ⊓ { f | f j = 0 } := by
  rw [toTopSet_obj_face_compl]
  aesop

end boundary.closedEmbeddings_toTop_map_ι

open boundary.closedEmbeddings_toTop_map_ι in
lemma boundary.closedEmbeddings_toTop_map_ι (n : ℕ) :
    TopCat.closedEmbeddings (toTop.map ∂Δ[n].ι) := by
  refine Subcomplex.closedEmbeddings_toTop_map_ι (hι n)
    (SSet.boundary.multicoequalizerDiagram n) ?_ ?_
  · intro i
    exact ((hι n).continuous.comp (by continuity)).isClosedEmbedding
      ((hι n).injective.comp (injective_toTop_map_face_ι _))
  · intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [toTopSet_obj_face_compl]
      aesop

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
