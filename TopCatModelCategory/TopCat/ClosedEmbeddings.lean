import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.MorphismProperty.Composition
import TopCatModelCategory.SSet.Monomorphisms
import TopCatModelCategory.ColimitsType
import TopCatModelCategory.TopCat.Colimits

universe u

open CategoryTheory Topology Limits MorphismProperty

@[simps]
def Set.homeomorphOfEq {X : Type*} [TopologicalSpace X] {A B : Set X} (h : A = B) :
    A ≃ₜ B where
  toFun := fun ⟨x, hx⟩ ↦ ⟨x, by subst h; exact hx⟩
  invFun := fun ⟨x, hx⟩ ↦ ⟨x, by subst h; exact hx⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace Function.Injective

variable {X Y : Type*} {f : X → Y} (hf : Function.Injective f)

@[simps! apply]
noncomputable def equivRange :
    X ≃ Set.range f :=
  Equiv.ofBijective (fun x ↦ ⟨f x, by simp⟩)
    ⟨Function.Injective.of_comp (f := Subtype.val) hf,
      by rintro ⟨_, x, rfl⟩; exact ⟨x, rfl⟩⟩

@[simp]
lemma apply_equivRange_symm (x : Set.range f) :
    f (hf.equivRange.symm x) = x.1 :=
  congr_arg Subtype.val (hf.equivRange.apply_symm_apply x)

end Function.Injective

namespace Topology.IsEmbedding

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
  (h : IsEmbedding f)

@[simps! toEquiv_apply]
noncomputable def homeomorphRange : Homeomorph X (Set.range f) where
  toEquiv := h.injective.equivRange
  continuous_toFun := ⟨fun U hU ↦ by
    obtain ⟨V, hV, rfl⟩ := hU
    exact h.continuous.isOpen_preimage V hV⟩
  continuous_invFun := ⟨fun U hU ↦ by
    rw [h.isOpen_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    exact ⟨V, hV, by aesop⟩⟩

@[simp]
lemma apply_homeomorphRange_symm (y : Set.range f) :
    f (h.homeomorphRange.symm y) = y.1 := by
  simp [homeomorphRange]

end Topology.IsEmbedding

namespace TopCat

def closedEmbeddings : MorphismProperty TopCat.{u} :=
  fun _ _ f ↦ IsClosedEmbedding f

lemma closedEmbeddings_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    closedEmbeddings f ↔ IsClosedEmbedding f := Iff.rfl

lemma closedEmbedding_le_inverseImage_monomorphisms :
    closedEmbeddings.{u} ≤ (monomorphisms (Type u)).inverseImage (forget _) :=
  fun _ _ _ hf ↦ by simpa [CategoryTheory.mono_iff_injective] using hf.injective

instance : closedEmbeddings.{u}.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

lemma isClosedEmbedding_of_isIso {X Y : TopCat.{u}} (f : X ⟶ Y) [IsIso f] :
    IsClosedEmbedding f := (homeoOfIso (asIso f)).isClosedEmbedding

instance : closedEmbeddings.{u}.RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition (by
    intro X Y f hf
    have : IsIso f := by assumption
    apply isClosedEmbedding_of_isIso)

section

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
  {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma injective_of_isPushout (sq : IsPushout t l r b) (ht : Function.Injective t) :
    Function.Injective b :=
  Types.injective_of_isPushout (sq.map (forget _)) ht

lemma isClosed_image_iff_of_isPushout (sq : IsPushout t l r b) (ht : IsClosedEmbedding t)
    (F : Set X₃) :
    IsClosed (b '' F) ↔ IsClosed F := by
  have hb := injective_of_isPushout sq ht.injective
  constructor
  · intro hF
    rw [← Function.Injective.preimage_image hb F]
    exact IsClosed.preimage (by continuity) hF
  · intro hF
    rw [isClosed_iff_of_isPushout sq]
    constructor
    · have := Types.preimage_image_eq_of_isPushout (sq.map (forget _)) ht.injective
      dsimp at this
      rw [this, ← ht.isClosed_iff_image_isClosed]
      exact IsClosed.preimage (f := l) (by continuity) hF
    · rwa [Function.Injective.preimage_image hb]

lemma isClosedEmbedding_of_isPushout (sq : IsPushout t l r b)
    (ht : IsClosedEmbedding t) :
    IsClosedEmbedding b where
  injective := injective_of_isPushout sq ht.injective
  eq_induced := by
    rw [TopologicalSpace.ext_iff_isClosed]
    intro F
    rw [isClosed_induced_iff]
    constructor
    · intro hF
      exact ⟨b '' F, by rwa [isClosed_image_iff_of_isPushout sq ht],
        by rw [(injective_of_isPushout sq ht.injective).preimage_image]⟩
    · rintro ⟨G, hG, rfl⟩
      exact IsClosed.preimage (by continuity) hG
  isClosed_range := by simpa using isClosed_image_iff_of_isPushout sq ht (b ⁻¹' ⊤)

end

section

variable {J : Type u'} {X₁ : J → TopCat.{u}} {X₂ : J → TopCat.{u}}
  (f : ∀ j, X₁ j ⟶ X₂ j) {c₁ : Cofan X₁} (h₁ : IsColimit c₁) {c₂ : Cofan X₂}
  (h₂ : IsColimit c₂) (φ : c₁.pt ⟶ c₂.pt) (hφ : ∀ j, c₁.inj j ≫ φ = f j ≫ c₂.inj j)

include h₁ in
lemma cofanInj_injective_of_isColimit (j : J) : Function.Injective (c₁.inj j) :=
  Types.cofanInj_injective_of_isColimit
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁) j

include h₁ in
lemma eq_cofanInj_apply_eq_of_isColimit {i j : J} (x : X₁ i) (y : X₁ j)
    (h : c₁.inj i x = c₁.inj j y) : i = j :=
  Types.eq_cofanInj_apply_eq_of_isColimit
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁) _ _ h

include h₁ h₂ hφ

lemma injective_of_coproducts (hf : ∀ j, Function.Injective (f j)) :
    Function.Injective φ := by
  rw [← CategoryTheory.mono_iff_injective]
  refine colimitsOfShape_le _
    (colimitsOfShape.mk' (W := monomorphisms (Type u))
      (X₁ := Discrete.functor X₁ ⋙ forget _)
      (X₂ := Discrete.functor X₂ ⋙ forget _)
      (h₁ := (isColimitOfPreserves (forget _) h₁))
      (h₂ := (isColimitOfPreserves (forget _) h₂))
      (f := Discrete.natTrans (fun ⟨j⟩ ↦ (forget _).map (f j))) _ _ ?_ _ ?_)
  · intro j
    dsimp
    rw [monomorphisms.iff, CategoryTheory.mono_iff_injective]
    apply hf
  · rintro ⟨j⟩
    exact (forget _).congr_map (hφ j)

lemma preimage_image_eq_of_coproducts
    (j : J) (F : Set (X₂ j)) :
    φ ⁻¹' (c₂.inj j '' F) = c₁.inj j '' ((f j) ⁻¹' F) :=
  Types.preimage_image_eq_of_coproducts
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁)
    (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₂.inj j) h₂) (fun j ↦ f j)
    ((forget _).map φ) (fun j ↦ by
      ext x
      exact congr_fun ((forget _).congr_map (hφ j)) x) j F

lemma isInducing_of_coproducts (hf : ∀ j, IsInducing (f j)) :
    IsInducing φ := by
  have := h₁
  have := h₂
  have := hφ
  constructor
  rw [TopologicalSpace.ext_iff_isClosed]
  intro F
  rw [isClosed_induced_iff]
  constructor
  · intro hF
    let G (j : J) := (c₁.inj j) ⁻¹' F
    have hG (j : J) : IsClosed (G j) := (isClosed_iff_of_isColimit _ h₁ F).1 hF ⟨j⟩
    simp only [fun j ↦ (hf j).eq_induced, isClosed_induced_iff] at hG
    let W (j : J) := (hG j).choose
    have hW (j : J) : IsClosed (W j) := (hG j).choose_spec.1
    have hW' (j : J) : (f j) ⁻¹' (W j) = G j := (hG j).choose_spec.2
    refine ⟨⨆ (j : J), c₂.inj j '' (W j), ?_, ?_⟩
    · rw [isClosed_iff_of_isColimit _ h₂]
      rintro ⟨j⟩
      simp only [Discrete.functor_obj_eq_as, Functor.const_obj_obj, Set.iSup_eq_iUnion,
        Set.preimage_iUnion]
      convert hW j
      ext x₂
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨i, y₂, hy₂, h⟩
        obtain rfl := eq_cofanInj_apply_eq_of_isColimit h₂ _ _ h
        obtain rfl := cofanInj_injective_of_isColimit h₂ i h
        exact hy₂
      · rintro hx₂
        exact ⟨j, x₂, hx₂, rfl⟩
    · simp only [Set.iSup_eq_iUnion, Set.preimage_iUnion,
        preimage_image_eq_of_coproducts f h₁ h₂ φ hφ, hW']
      ext x₁
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage, G]
      constructor
      · rintro ⟨j, y, hy, rfl⟩
        exact hy
      · intro hx₁
        obtain ⟨⟨j⟩, (x : X₁ j), rfl⟩ := Types.jointly_surjective_of_isColimit
          (isColimitCofanMkObjOfIsColimit (forget _) _ (fun j ↦ c₁.inj j) h₁) x₁
        dsimp
        exact ⟨j, x, hx₁, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    exact IsClosed.preimage (by continuity) hG

lemma isClosedEmbedding_of_isColimit (hf : ∀ j, IsClosedEmbedding (f j)) :
    IsClosedEmbedding φ where
  toIsInducing := isInducing_of_coproducts f h₁ h₂ φ hφ (fun j ↦ (hf j).toIsInducing)
  injective := injective_of_coproducts f h₁ h₂ φ hφ (fun j ↦ (hf j).injective)
  isClosed_range := by
    rw [isClosed_iff_of_isColimit _ h₂]
    rintro ⟨j⟩
    convert (hf j).isClosed_range
    ext (x₂ : X₂ j)
    dsimp
    simp only [Set.mem_preimage, Set.mem_range]
    constructor
    · rintro ⟨x₁, hx⟩
      obtain ⟨⟨j'⟩, (x₁ : X₁ j'), rfl⟩ := Types.jointly_surjective_of_isColimit
        (isColimitOfPreserves (forget _) h₁) x₁
      replace hx : φ (c₁.inj j' x₁) = c₂.inj j x₂ := hx
      have : c₂.inj j' (f j' x₁) = c₂.inj j x₂ := by
        rw [← hx]
        exact congr_fun ((forget _).congr_map (hφ j').symm) x₁
      obtain rfl : j = j' := eq_cofanInj_apply_eq_of_isColimit h₂ _ _ this.symm
      exact ⟨x₁, cofanInj_injective_of_isColimit h₂ j this⟩
    · rintro ⟨x₁, rfl⟩
      exact ⟨c₁.inj j x₁, congr_fun ((forget _).congr_map (hφ j)) x₁⟩

end

section

variable {J : Type u'} [LinearOrder J]

instance : PreservesWellOrderContinuousOfShape J (forget TopCat.{u}) where

variable [OrderBot J]

lemma isClosedEmbedding_of_transfiniteCompositionOfShape_aux
    {X : J ⥤ TopCat.{u}} {c : Cocone X} (hc : IsColimit c)
    (hX : ∀ (j : J), IsClosedEmbedding (X.map (homOfLE bot_le : ⊥ ⟶ j)))
    (h' : ∀ ⦃j j' : J⦄ (f : j ⟶ j'), Function.Injective (X.map f)) :
    IsClosedEmbedding (c.ι.app ⊥) := by
  have inj (j : J) : Function.Injective (c.ι.app j) := fun x₁ x₂ h ↦ by
    obtain ⟨k, g, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget _) hc) _ _).1 h
    exact h' _ hk
  have closed {F : Set (X.obj ⊥)} (hF : IsClosed F) :
      IsClosed (c.ι.app ⊥ '' F) := by
    rw [isClosed_iff_of_isColimit c hc]
    intro j
    convert (hX j).isClosedMap _ hF
    ext x
    simp only [Set.mem_preimage, Set.mem_image, homOfLE_leOfHom]
    constructor
    · rintro ⟨y, hy, h⟩
      refine ⟨y, hy, inj _ ?_⟩
      rw [← h]
      exact congr_fun ((forget _).congr_map (c.w (homOfLE bot_le : ⊥ ⟶ j))) y
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, congr_fun ((forget _).congr_map (c.w (homOfLE bot_le : ⊥ ⟶ j)).symm) y⟩
  exact {
    eq_induced := by
      rw [TopologicalSpace.ext_iff_isClosed]
      intro F
      simp only [isClosed_induced_iff]
      constructor
      · intro hF
        exact ⟨c.ι.app ⊥ '' F, closed hF, (inj ⊥).preimage_image F⟩
      · rintro ⟨V, hV, rfl⟩
        exact IsClosed.preimage (by continuity) hV
    injective := inj ⊥
    isClosed_range := by simpa using closed isClosed_univ }

lemma isClosedEmbedding_of_transfiniteCompositionOfShape
    [WellFoundedLT J] [SuccOrder J] {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : closedEmbeddings.{u}.TransfiniteCompositionOfShape J f) :
    IsClosedEmbedding f := by
  have inj ⦃j j' : J⦄ (g : j ⟶ j') : Function.Injective (hf.F.map g) := by
    rw [← CategoryTheory.mono_iff_injective]
    exact MorphismProperty.transfiniteCompositionsOfShape_le _ _ _
      ((((hf.ici j).iic ⟨j', leOfHom g⟩).ofLE
        closedEmbedding_le_inverseImage_monomorphisms)).map.mem
  simp only [← hf.fac, Functor.const_obj_obj, hom_comp, ContinuousMap.coe_comp]
  refine IsClosedEmbedding.comp
    (isClosedEmbedding_of_transfiniteCompositionOfShape_aux hf.isColimit (fun j ↦ ?_) inj)
    (isClosedEmbedding_of_isIso _)
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl := hj.eq_bot
    simpa using IsClosedEmbedding.id
  | succ j hj hj' =>
    rw [← homOfLE_comp bot_le (Order.le_succ j), Functor.map_comp]
    exact (hf.map_mem j hj).comp hj'
  | isSuccLimit j hj hj' =>
    letI : OrderBot (Set.Iio j) :=
      { bot := ⟨⊥, hj.bot_lt⟩
        bot_le j := bot_le }
    exact isClosedEmbedding_of_transfiniteCompositionOfShape_aux
      (hf.F.isColimitOfIsWellOrderContinuous j hj) (fun ⟨i, hi⟩ ↦ hj' i hi) (fun _ _ _ ↦ inj _)

end

instance : closedEmbeddings.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hl := isClosedEmbedding_of_isPushout sq.flip hl

instance : IsStableUnderCoproducts.{u'} closedEmbeddings.{u} where
  isStableUnderCoproductsOfShape J := by
    apply IsStableUnderCoproductsOfShape.mk
    intro X₁ X₂ _ _ f hf
    exact isClosedEmbedding_of_isColimit f (colimit.isColimit _)
      (colimit.isColimit _) _ (fun j ↦ colimit.ι_desc _ _) hf

instance : IsStableUnderTransfiniteComposition.{u'} closedEmbeddings.{u} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    ⟨fun _ _ _ ⟨hf⟩ ↦ isClosedEmbedding_of_transfiniteCompositionOfShape hf⟩

namespace closedEmbeddings

variable {J : Type*} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {X Y : TopCat.{u}} {f : X ⟶ Y}
  (hf : closedEmbeddings.TransfiniteCompositionOfShape J f)
  {ι : ℕ → J} (hι : StrictMono ι)

namespace coconeOfTransfiniteCompositionOfShape

variable (ι)

abbrev point : Set Y := ⋃ (n : ℕ), Set.range (hf.incl.app (ι n))

def ιPoint : TopCat.of (point hf ι) ⟶ Y := ofHom ⟨Subtype.val, by continuity⟩

end coconeOfTransfiniteCompositionOfShape

@[simps]
def coconeOfTransfiniteCompositionOfShape : Cocone (hι.monotone.functor ⋙ hf.F) where
  pt := .of (coconeOfTransfiniteCompositionOfShape.point hf ι)
  ι :=
    { app i := ofHom ⟨fun x ↦ ⟨hf.incl.app (ι i) x, by aesop⟩, by continuity⟩
      naturality i₁ i₂ g := by
        dsimp
        ext x
        exact congr_fun ((forget _).congr_map
          (hf.incl.naturality (homOfLE (hι.monotone (leOfHom g))))) x }

namespace coconeOfTransfiniteCompositionOfShape

section Final

variable [hι.monotone.functor.Final]
include hι

lemma point_eq_top_of_final : point hf ι = ⊤ := by
  ext y
  simp only [Set.mem_iUnion, Functor.const_obj_obj, Set.mem_range,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact Types.jointly_surjective _ (isColimitOfPreserves (forget _)
    ((Functor.Final.isColimitWhiskerEquiv hι.monotone.functor _).2 hf.isColimit)) y

lemma isIso_ιPoint_of_final : IsIso (ιPoint hf ι) :=
  (TopCat.isoOfHomeo (IsHomeomorph.homeomorph (ιPoint hf ι) (by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    constructor
    · exact .subtypeVal
    · rintro x
      exact ⟨⟨x, by simp [point_eq_top_of_final hf hι]⟩, rfl⟩))).isIso_hom

lemma closedEmbeddings_ιPoint_of_final : closedEmbeddings (ιPoint hf ι) := by
  have := isIso_ιPoint_of_final hf hι
  apply isClosedEmbedding_of_isIso

noncomputable def isColimitOfFinal :
    IsColimit (coconeOfTransfiniteCompositionOfShape hf hι) :=
  IsColimit.ofIsoColimit
    (((Functor.Final.isColimitWhiskerEquiv hι.monotone.functor _).2 hf.isColimit)) (by
      have := isIso_ιPoint_of_final hf hι
      exact Iso.symm (Cocones.ext (asIso (ιPoint hf ι))))

end Final

section NotFinal

variable {l : J} (hl : ∀ (n : ℕ), ι n < l) (hl' : Order.IsSuccLimit l)

def functorOfNotFinal : ℕ ⥤ Set.Iio l :=
  Monotone.functor (f := fun n ↦ ⟨ι n, hl n⟩) (fun _ _ h ↦ hι.monotone h)

variable [(functorOfNotFinal hι hl).Final]

include hl hl' hι

lemma point_eq_of_not_final : point hf ι = Set.range (hf.incl.app l) := by
  have := hl
  have := hl'
  have mono : Monotone (fun (j : J) ↦ (Set.range (hf.incl.app j) : Set Y)) := by
    rintro j₁ j₂ hj _ ⟨x, rfl⟩
    exact ⟨hf.F.map (homOfLE hj) x,
      congr_fun ((forget _).congr_map (hf.incl.naturality (homOfLE hj))) x⟩
  ext y
  simp only [point, Set.mem_iUnion]
  constructor
  · rintro ⟨n, hn⟩
    exact mono (hl n).le hn
  · rintro ⟨x, rfl⟩
    obtain ⟨n, x, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _)
      (((Functor.Final.isColimitWhiskerEquiv (functorOfNotFinal hι hl) _).2
        (hf.F.isColimitOfIsWellOrderContinuous l hl')))) x
    exact ⟨n, x,
      congr_fun ((forget _).congr_map (hf.incl.naturality (homOfLE (hl n).le)).symm) x⟩

noncomputable def homeomorphOfNotFinal : point hf ι ≃ₜ hf.F.obj l :=
  (Set.homeomorphOfEq (point_eq_of_not_final hf hι hl hl')).trans
    ((isClosedEmbedding_of_transfiniteCompositionOfShape
      (hf.ici l)).homeomorphRange).symm

lemma closedEmbeddings_ιPoint_of_not_final :
    closedEmbeddings (ιPoint hf ι) := by
  refine (closedEmbeddings.arrow_mk_iso_iff ?_).1
    (isClosedEmbedding_of_transfiniteCompositionOfShape (hf.ici l))
  exact Arrow.isoMk (TopCat.isoOfHomeo (homeomorphOfNotFinal hf hι hl hl').symm)
    (Iso.refl _)

noncomputable def isColimitOfNotFinal :
    IsColimit (coconeOfTransfiniteCompositionOfShape hf hι) := by
  refine IsColimit.ofIsoColimit
    ((Functor.Final.isColimitWhiskerEquiv (functorOfNotFinal hι hl) _).2
      (hf.F.isColimitOfIsWellOrderContinuous l hl'))
      (Cocones.ext (TopCat.isoOfHomeo (homeomorphOfNotFinal hf hι hl hl').symm) ?_)
  intro n
  ext x
  dsimp
  ext
  exact congr_fun ((forget _).congr_map (hf.incl.naturality (homOfLE (hl n).le))) x

end NotFinal

omit [SuccOrder J] in
lemma final_or : hι.monotone.functor.Final ∨
    ∃ (l : J) (hl : ∀ (n : ℕ), ι n < l) (_ : Order.IsSuccLimit l),
      (functorOfNotFinal hι hl).Final := by
  by_cases h : hι.monotone.functor.Final
  · exact Or.inl h
  · refine Or.inr ?_
    let S : Set J := setOf (fun j ↦ ∀ (n : ℕ), ι n < j)
    have hS : S.Nonempty := by
      rw [Monotone.final_functor_iff] at h
      by_contra!
      exfalso
      apply h
      intro j
      have : j ∉ S := by simp [this]
      simpa [S] using this
    let l := WellFounded.min wellFounded_lt S hS
    have hl : l ∈ S := WellFounded.min_mem wellFounded_lt S hS
    refine ⟨l, hl, ?_, ?_⟩
    · constructor
      · intro hl
        have : ⊥ ∉ S := by simp [S]
        exact this (by rwa [← hl.eq_bot])
      · rintro j ⟨hj, hj'⟩
        have : j ∉ S := fun hj'' ↦ WellFounded.not_lt_min wellFounded_lt S hS hj'' hj
        simp only [Set.mem_setOf_eq, not_forall, not_lt, S] at this
        obtain ⟨n, hn⟩ := this
        have := hj' (lt_of_le_of_lt hn (hι (Nat.lt_succ_self n)))
        simp only [Nat.succ_eq_add_one] at this
        exact this (hl (n + 1))
    · dsimp [functorOfNotFinal]
      rw [Monotone.final_functor_iff]
      rintro ⟨j, hj⟩
      have : j ∉ S := fun hj' ↦
        (WellFounded.not_lt_min wellFounded_lt S hS hj') hj
      simpa [S] using this

end coconeOfTransfiniteCompositionOfShape

open coconeOfTransfiniteCompositionOfShape

noncomputable def isColimitCoconeOfTransfiniteCompositionOfShape :
    IsColimit (coconeOfTransfiniteCompositionOfShape hf hι) := Nonempty.some (by
  obtain _ | ⟨l, hl, hl', _⟩ := final_or hι
  · exact ⟨isColimitOfFinal hf hι⟩
  · exact ⟨isColimitOfNotFinal hf hι hl hl'⟩)

include hι in
lemma coconeOfTransfiniteCompositionOfShape.closedEmbeddings_ιPoint :
    closedEmbeddings (ιPoint hf ι) := by
  obtain _ | ⟨l, hl, hl', _⟩ := final_or hι
  · exact closedEmbeddings_ιPoint_of_final hf hι
  · exact closedEmbeddings_ιPoint_of_not_final hf hι hl hl'

end closedEmbeddings

end TopCat
