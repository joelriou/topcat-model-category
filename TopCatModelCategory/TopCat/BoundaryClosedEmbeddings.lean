import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.Glueing
import TopCatModelCategory.TopCat.ToTopULift
import TopCatModelCategory.SSet.ULift

universe u

open CategoryTheory Simplicial MorphismProperty TopCat SSet.modelCategoryQuillen
  Topology Limits

lemma Set.range_comp_eq_of_surjective {X Y Z : Type*}
    (f : Y → Z) {g : X → Y} (hg : Function.Surjective g) :
    Set.range (f.comp g) = Set.range f := by
  ext z
  simp only [mem_range, Function.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨g x, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨x, rfl⟩

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}}

@[simps!]
protected noncomputable def toTop : X.Subcomplex ⥤ TopCat :=
  toPresheafFunctor ⋙ SSet.toTop

variable {Ω : Type u} (ι : |X| → Ω)

@[simps]
def toTopSet : X.Subcomplex ⥤ Set Ω where
  obj A := Set.range (ι.comp (SSet.toTop.map A.ι))
  map {A₁ A₂} f := CategoryTheory.homOfLE (by
    rintro _ ⟨x, rfl⟩
    refine ⟨Subcomplex.toTop.map f x, ?_⟩
    dsimp
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, homOfLE_ι])

lemma toTopSet_obj_subset (A : X.Subcomplex) : (toTopSet ι).obj A ⊆ Set.range ι := by
  rintro _ ⟨a, rfl⟩
  simp

lemma toTopSet_iSup {α : Type*} (U : α → X.Subcomplex) :
    (toTopSet ι).obj (⨆ i, U i) = ⋃ i, (toTopSet ι).obj (U i) := by
  apply subset_antisymm
  · intro x hx
    simp only [toTopSet_obj, Set.mem_range, Function.comp_apply] at hx
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨⟨⟨n, ⟨s, hs⟩, hs'⟩, y⟩, rfl⟩ := surjective_sigmaToTopObj _ x
    dsimp at y
    simp only [Subpresheaf.iSup_obj, Set.mem_iUnion] at hs
    obtain ⟨i, hi⟩ := hs
    simp only [toTopSet_obj, Subpresheaf.toPresheaf_obj, Set.mem_iUnion, Set.mem_range,
      Function.comp_apply]
    refine ⟨i, toTop.map (by exact yonedaEquiv.symm ⟨s, hi⟩) (⦋n⦌.toTopHomeo.symm y), ?_⟩
    dsimp [sigmaToTopObj]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  · rw [Set.iUnion_subset_iff]
    intro i
    exact leOfHom ((toTopSet ι).map (CategoryTheory.homOfLE (le_iSup _ _)))

variable {ι} [TopologicalSpace Ω] (hι : IsClosedEmbedding ι)


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
  intro ⟨x, hx⟩
  simp at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, rfl⟩

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
    · rw [Set.iSup_eq_iUnion, ← toTopSet_iSup, h.iSup_eq]
    · intro i j
      exact (hV i j).symm
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
        rw [h.min_eq]
        exact inf_le_left)))
    (fun ⟨i, j⟩ ↦
      (toTopNatTrans hι).naturality (CategoryTheory.homOfLE (by
        dsimp
        rw [h.min_eq]
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
    change Z = _ at this
    rw [this]
    exact isClosed_iUnion_of_finite (fun i ↦ (hU i).isClosed_range)

end Subcomplex

open NNReal

namespace stdSimplex

variable (n : ℕ)

def ι'ToTop : ⦋n⦌.toTopObj → (Fin (n + 1) → ℝ≥0) := Subtype.val

lemma hι'ToTop : IsClosedEmbedding (ι'ToTop n) :=
  Topology.IsClosedEmbedding.subtypeVal (IsCompact.isClosed (by
    rw [isCompact_iff_compactSpace, Set.setOf_mem_eq]
    infer_instance))

@[simp]
lemma range_ι'ToTop : Set.range (ι'ToTop n) = ⦋n⦌.toTopObj := by
  simp [ι'ToTop]

noncomputable def ιToTop : |Δ[n]| → (Fin (n + 1) → ℝ≥0) := ι'ToTop n ∘ ⦋n⦌.toTopHomeo

@[simp]
lemma range_ιToTop : Set.range (ιToTop n) = ⦋n⦌.toTopObj := by
  dsimp only [ιToTop]
  rw [Set.range_comp_eq_of_surjective _ (Homeomorph.surjective _), range_ι'ToTop]

lemma hιToTop : IsClosedEmbedding (ιToTop n) :=
    (hι'ToTop n).comp (Homeomorph.isClosedEmbedding _)

variable {n}

lemma injective_toTopMap_stdSimplex_map_of_mono
    {n m : SimplexCategory} (i : n ⟶ m) (hi : Mono i) :
    Function.Injective (SimplexCategory.toTop.{u}.map i) := by
  rw [SimplexCategory.mono_iff_injective] at hi
  intro f₁ f₂ h
  dsimp at h
  rw [← ULift.down_inj] at h ⊢
  dsimp [ULift.map, TopCat.uliftFunctor] at h ⊢
  rw [Subtype.ext_iff] at h ⊢
  funext j
  have (f : SimplexCategory.toTop.{u}.obj n) :
      f.down.1 j = SimplexCategory.toTopMap i f.down (i j) := by
    dsimp
    rw [Finset.sum_eq_single j _ (by simp)]
    rintro b hb hb'
    exact (hb' (hi (by simpa using hb))).elim
  simp only [this, h]

lemma injective_toTop_map_stdSimplex_map_of_mono
    {n m : SimplexCategory} (i : n ⟶ m) (hi : Mono i) :
    Function.Injective (toTop.{u}.map (stdSimplex.map i)) := by
  refine ((MorphismProperty.injective _).arrow_mk_iso_iff ?_).2
    (injective_toTopMap_stdSimplex_map_of_mono i hi)
  refine Arrow.isoMk (toTopSimplex.app _) (toTopSimplex.app _)
    (toTopSimplex.{u}.hom.naturality i).symm

lemma injective_toTop_map_face_ι (S : Finset (Fin (n + 1))) :
    Function.Injective (toTop.{u}.map (stdSimplex.face S).ι) := by
  dsimp [Subcomplex.toTopSet]
  generalize h : S.card = m
  obtain _ | m := m
  · have hS : IsInitial (toTop.{u}.obj (stdSimplex.face S)) := by
      obtain rfl : S = ∅ := by rwa [← Finset.card_eq_zero]
      rw [stdSimplex.face_emptySet]
      apply IsInitial.isInitialObj
      exact Subcomplex.botIsInitial
    have := (Types.initial_iff_empty _).1 ⟨hS.isInitialObj (forget _)⟩
    exact this.elim
  · let e := S.orderIsoOfFin h
    let φ : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom
      ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)
    have iso : Arrow.mk (stdSimplex.{u}.map φ) ≅ Arrow.mk (stdSimplex.face S).ι :=
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
    (Subcomplex.toTopSet (ιToTop n)).obj (stdSimplex.face Sᶜ) =
      ⦋n⦌.toTopObj ⊓ (⨅ (i : S), { f | f i.1 = 0}) := by
  dsimp [Subcomplex.toTopSet]
  by_cases hS : S = Finset.univ
  · subst hS
    trans ∅
    · simp only [Set.range_eq_empty_iff, Finset.compl_univ, stdSimplex.face_emptySet,
        ← Types.initial_iff_empty]
      constructor
      exact IsInitial.isInitialObj (toTop ⋙ forget _) _ Subcomplex.botIsInitial
    · ext f
      simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_iInter, Subtype.forall,
        Finset.mem_univ, forall_const, false_iff, not_and, not_forall]
      intro hf
      by_contra!
      replace this (x : Fin (n + 1)) : f x = 0 := this x
      replace hf := Set.mem_setOf.1 hf
      simp [this] at hf
  · generalize hm : Sᶜ.card = m
    obtain _ | m := m
    · exact (hS (by simpa using hm)).elim
    let e := Sᶜ.orderIsoOfFin hm
    let φ : ⦋m⦌ ⟶ ⦋n⦌ := SimplexCategory.mkHom
      ((OrderHom.Subtype.val _).comp e.toOrderEmbedding.toOrderHom)
    have injective_φ : Function.Injective φ :=
      Subtype.val_injective.comp e.injective
    have range_φ : Set.range φ = (S.toSet)ᶜ := by
      ext x
      simp only [Set.mem_range,
        Set.mem_compl_iff, Finset.mem_coe]
      constructor
      · rintro ⟨y, rfl⟩
        have := (e y).2
        rwa [Finset.mem_compl] at this
      · intro hx
        exact ⟨e.symm ⟨x, by simpa⟩,
          Subtype.ext_iff.1 (e.apply_symm_apply ⟨x, _⟩)⟩
    let iso := stdSimplex.isoOfRepresentableBy.{0}
          (stdSimplex.faceRepresentableBy _ _ e)
    have hiso : (stdSimplex.face Sᶜ).ι =
        iso.inv ≫ stdSimplex.map φ := by
      rw [← cancel_epi iso.hom, Iso.hom_inv_id_assoc]
      apply yonedaEquiv.injective
      rw [yonedaEquiv_comp]
      rfl
    have : ιToTop n ∘ toTop.map (stdSimplex.face Sᶜ).ι =
        Subtype.val.comp (((SimplexCategory.toTopMap φ).comp
          ⦋m⦌.toTopHomeo).comp (toTop.map iso.inv)) := by
      rw [← SimplexCategory.toTopHomeo_naturality,
        hiso, Functor.map_comp]
      rfl
    rw [this, ← Function.comp_assoc, ← Function.comp_assoc,
      Set.range_comp_eq_of_surjective, Set.range_comp_eq_of_surjective]
    rotate_left
    · apply Homeomorph.surjective
    · apply ConcreteCategory.surjective_of_epi_of_preservesPushout
    · have hφ (g : ⦋m⦌.toTopObj) (i : Fin (n + 1)) (hi : i ∈ S) :
          SimplexCategory.toTopMap φ g i = 0 := by
        dsimp [SimplexCategory.toTopMap]
        apply Finset.sum_eq_zero
        rintro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have : i ∈ Sᶜ.toSet := by simp [← hj, ← range_φ]
        simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at this
        exact (this hi).elim
      ext f
      simp only [Set.mem_range, Function.comp_apply, Subtype.exists, Set.mem_inter_iff,
        Set.mem_iInter, Subtype.forall]
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨by simp, fun i hi ↦ hφ _ _ hi⟩
      · rintro ⟨hf, hf'⟩
        replace hf := Set.mem_setOf.1 hf
        replace hf' (i : Fin (n + 1)) (hi : i ∈ S) : f i = 0 := hf' i hi
        refine ⟨f ∘ φ, ?_, ?_⟩
        · simp only [SimplexCategory.toTopObj, SimplexCategory.len_mk, Set.mem_setOf_eq,
            Function.comp_apply]
          rw [← hf]
          erw [← Finset.sum_compl_add_sum S f]
          rw [Finset.sum_eq_zero hf', add_zero]
          apply Finset.sum_of_injOn (e := φ)
          · intro _ _ _ _ h
            exact injective_φ h
          · simp only [SimplexCategory.len_mk, Finset.coe_univ, Finset.coe_compl,
              Set.mapsTo_univ_iff, Set.mem_compl_iff, Finset.mem_coe]
            intro x
            have : φ x ∈ (S.toSet)ᶜ := by simp [← range_φ]
            simpa using this
          · intro i hi hi'
            exfalso
            simp only [SimplexCategory.len_mk, Finset.mem_compl] at hi
            apply hi
            have : i ∉ Set.range φ := by simpa using hi'
            rw [range_φ] at this
            simpa [range_φ]using this
          · tauto
        · ext i
          simp
          by_cases hi : i ∈ Set.range φ
          · obtain ⟨j, rfl⟩ := hi
            dsimp at j
            rw [Finset.sum_eq_single j _ (by simp)]
            · rfl
            · intro k hk hkj
              exact (hkj (injective_φ (by simpa using hk))).elim
          · rw [Finset.sum_eq_zero, hf']
            · rw [range_φ] at hi
              simpa using hi
            · simp at hi ⊢
              tauto

lemma toTopSet_obj_face_singleton_compl (i : Fin (n + 1)) :
    (Subcomplex.toTopSet (ιToTop n)).obj
      (stdSimplex.face {i}ᶜ) =
    ⦋n⦌.toTopObj ⊓ { f | f i = 0 } := by
  rw [toTopSet_obj_face_compl]
  simp

lemma toTopSet_obj_face_pair_compl (i j : Fin (n + 1)) :
    (Subcomplex.toTopSet (ιToTop n)).obj
      (stdSimplex.face {i, j}ᶜ) =
    ⦋n⦌.toTopObj ⊓ { f | f i = 0 } ⊓ { f | f j = 0 } := by
  rw [toTopSet_obj_face_compl]
  aesop

end stdSimplex

lemma boundary.closedEmbeddings_toTop_map_ι (n : ℕ) :
    TopCat.closedEmbeddings (toTop.{u}.map ∂Δ[n].ι) := by
  refine (TopCat.closedEmbeddings.arrow_mk_iso_iff (toTop.mapArrow.mapIso
      (arrowUliftIso.{u, 0} n))).1 (toTopMap_ulift_closedEmbeddings.{u} ?_)
  refine Subcomplex.closedEmbeddings_toTop_map_ι (stdSimplex.hιToTop n)
    (SSet.boundary.multicoequalizerDiagram n) ?_ ?_
  · intro i
    exact ((stdSimplex.hιToTop n).continuous.comp (by continuity)).isClosedEmbedding
      ((stdSimplex.hιToTop n).injective.comp (stdSimplex.injective_toTop_map_face_ι _))
  · intro i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [stdSimplex.toTopSet_obj_face_compl]
      aesop

instance (n : ℕ) : T2Space |Δ[n]| := ⦋n⦌.toTopHomeo.symm.t2Space

lemma boundary.t₁Inclusions_toTop_map_ι (n : ℕ) :
    TopCat.t₁Inclusions (toTop.map ∂Δ[n].ι) :=
  ⟨closedEmbeddings_toTop_map_ι n, fun _ _ ↦ isClosed_singleton⟩

lemma t₁Inclusions_toObj_map_of_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] :
    t₁Inclusions (SSet.toTop.map i) := by
  have : (MorphismProperty.coproducts.{u} I).pushouts ≤
      (t₁Inclusions.{u}).inverseImage SSet.toTop := by
    rw [← MorphismProperty.map_le_iff]
    refine ((coproducts I).map_pushouts_le SSet.toTop.{u}).trans ?_
    simp only [pushouts_le_iff]
    refine (I.map_coproducts_le SSet.toTop).trans ?_
    simp only [coproducts_le_iff, MorphismProperty.map_le_iff]
    intro _ _ _ ⟨n⟩
    apply SSet.boundary.t₁Inclusions_toTop_map_ι
  exact t₁Inclusions.isT₁Inclusion_of_transfiniteCompositionOfShape
    ((transfiniteCompositionOfMono i).ofLE this).map

namespace Subcomplex

variable {X : SSet.{u}} {Ω : Type u} {ι : |X| → Ω}
  [TopologicalSpace Ω] (hι : IsClosedEmbedding ι) (A : X.Subcomplex)

instance : IsIso ((toTopNatTrans hι).app A) :=
  isIso_toTopNatTrans_app hι A
    (hι.comp (t₁Inclusions_toObj_map_of_mono A.ι).1)

noncomputable def arrowMkToTopMapιIso :
    Arrow.mk (toTop.map A.ι) ≅
      Arrow.mk (Set.functorToTopCat.map (CategoryTheory.homOfLE (toTopSet_obj_subset ι A))) :=
  Arrow.isoMk (asIso ((toTopNatTrans hι).app A)) (isoOfHomeo hι.homeomorphRange)

end Subcomplex

end SSet
