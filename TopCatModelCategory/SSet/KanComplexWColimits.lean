import TopCatModelCategory.SSet.FundamentalGroupoidPiOne
import TopCatModelCategory.SSet.SmallObject
import TopCatModelCategory.SSet.Quotient
import TopCatModelCategory.Arrow

universe u

open CategoryTheory Limits HomotopicalAlgebra SSet.modelCategoryQuillen
  Simplicial Opposite MonoidalCategory

namespace CategoryTheory

namespace Arrow

variable {J C : Type*} [Category J] [Category C] {F : J ⥤ Arrow C}
  {c : Cocone F}

def isColimitOfLeftRight (h₁ : IsColimit (leftFunc.mapCocone c))
    (h₂ : IsColimit (rightFunc.mapCocone c)) : IsColimit c where
  desc s := Arrow.homMk (h₁.desc (leftFunc.mapCocone s))
      (h₂.desc (rightFunc.mapCocone s)) (h₁.hom_ext (fun j ↦ by
        have := h₂.fac (rightFunc.mapCocone s) j
        rw [h₁.fac_assoc]
        dsimp at this ⊢
        simp [this]))
  fac s j := by
    ext
    · exact h₁.fac (leftFunc.mapCocone s) j
    · exact h₂.fac (rightFunc.mapCocone s) j
  uniq s m hm := by
    ext
    · refine h₁.hom_ext (fun j ↦ ?_)
      have := h₁.fac (leftFunc.mapCocone s) j
      dsimp at this ⊢
      rw [this, ← hm]
      dsimp
    · refine h₂.hom_ext (fun j ↦ ?_)
      have := h₂.fac (rightFunc.mapCocone s) j
      dsimp at this ⊢
      rw [this, ← hm]
      dsimp

end Arrow

end CategoryTheory

namespace SSet

namespace Subcomplex

variable {B : SSet.{u}} (A : B.Subcomplex)

noncomputable def quotientι₀ : A.quotient ⟶ (A.prod (⊤ : Δ[1].Subcomplex)).quotient :=
  A.descQuotient (ι₀ ≫ (A.prod ⊤).toQuotient) (A.prod ⊤).quotient₀ (by
    rw [← Category.assoc]
    apply comp_toQuotient_eq_const
    apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, image_comp, image_top]
    rintro n b h
    simp only [Subpresheaf.range_ι, Subpresheaf.image_obj, Set.mem_image] at h
    obtain ⟨a, ha, ha'⟩ := h
    rw [← ha']
    exact ⟨ha, by simp⟩)

noncomputable def quotientι₁ : A.quotient ⟶ (A.prod (⊤ : Δ[1].Subcomplex)).quotient :=
  A.descQuotient (ι₁ ≫ (A.prod ⊤).toQuotient) (A.prod ⊤).quotient₀ (by
    rw [← Category.assoc]
    apply comp_toQuotient_eq_const
    apply le_antisymm (by simp)
    rw [← Subcomplex.image_le_iff, image_comp, image_top]
    rintro n b h
    simp only [Subpresheaf.range_ι, Subpresheaf.image_obj, Set.mem_image] at h
    obtain ⟨a, ha, ha'⟩ := h
    rw [← ha']
    exact ⟨ha, by simp⟩)

@[reassoc (attr := simp)]
lemma to_quotient₀ : A.toQuotient ≫ A.quotientι₀ = ι₀ ≫ (A.prod ⊤).toQuotient := by
  simp [quotientι₀]

@[reassoc (attr := simp)]
lemma to_quotient₁ : A.toQuotient ≫ A.quotientι₁ = ι₁ ≫ (A.prod ⊤).toQuotient := by
  simp [quotientι₁]

@[simp]
lemma quotientι₀_app_quotient₀ :
    A.quotientι₀.app _ A.quotient₀ = (A.prod ⊤).quotient₀ :=
  descQuotient_app_quotient₀ _ _ _ _

@[simp]
lemma quotientι₁_app_quotient₀ :
    A.quotientι₁.app _ A.quotient₀ = (A.prod ⊤).quotient₀ :=
  descQuotient_app_quotient₀ _ _ _ _

protected noncomputable def πFunctor : SSet.{u} ⥤ Type u :=
  coequalizer (coyoneda.map A.quotientι₀.op) (coyoneda.map A.quotientι₁.op)

noncomputable def πNatTrans : A.πFunctor ⟶ SSet.evaluation.obj (op ⦋0⦌) :=
  coequalizer.desc (coyoneda.map (const A.quotient₀ : Δ[0] ⟶ _).op ≫
    (stdSimplex.coyonedaObjIsoEvaluation 0).hom) (by
    simp only [← Functor.map_comp_assoc, ← op_comp,
      const_comp, quotientι₀_app_quotient₀, quotientι₁_app_quotient₀])

end Subcomplex

noncomputable def πSuccFunctor (n : ℕ) : SSet.{u} ⥤ Type u := (boundary (n + 1)).πFunctor

def πSuccFunctorObjEquiv (n : ℕ) (X : SSet.{u}) :
    (πSuccFunctor n).obj X ≃ Σ (x : X _⦋0⦌), KanComplex.π (n + 1) X x := sorry

@[simp]
lemma πSuccFunctor_map_equiv_symm_apply {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}
    (a : KanComplex.π (n + 1) X x) {Y : SSet.{u}} (f : X ⟶ Y) :
    (πSuccFunctor n).map f ((πSuccFunctorObjEquiv n X).symm ⟨x, a⟩) =
      (πSuccFunctorObjEquiv n Y).symm (⟨_, KanComplex.mapπ f (n + 1) x _ rfl a⟩) := sorry

noncomputable def πSuccNatTrans (n : ℕ) : πSuccFunctor.{u} n ⟶ SSet.evaluation.obj (op ⦋0⦌) :=
  Subcomplex.πNatTrans _

@[simp]
lemma πSuccNatTrans_app_equiv_symm_apply {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}
    (a : KanComplex.π (n + 1) X x) :
    (πSuccNatTrans n).app X ((πSuccFunctorObjEquiv n X).symm ⟨x, a⟩) = x := sorry

@[simps]
noncomputable def πSuccArrowFunctor (n : ℕ) : SSet.{u} ⥤ Arrow (Type u) where
  obj X := Arrow.mk ((πSuccNatTrans n).app X)
  map f := Arrow.homMk ((πSuccFunctor n).map f) (f.app _)

def naiveW : MorphismProperty SSet.{u} :=
  (MorphismProperty.isomorphisms _).inverseImage π₀Functor ⊓
    ⨅ (n : ℕ), (Arrow.cartesianMorphisms _).inverseImage (πSuccArrowFunctor.{u} n)

section

variable (J : Type*) [Category J] [h₁ : Small.{u} J]

open MorphismProperty

lemma isStableUnderColimitsOfShape_inverseImage_isomorphisms_π₀Functor :
    ((isomorphisms _).inverseImage
      π₀Functor.{u}).IsStableUnderColimitsOfShape J := by
  rw [isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  intro X Y f hf
  rw [inverseImage_iff]
  apply (IsStableUnderColimitsOfShape.isomorphisms (Type u) J).colimitsOfShape_le
  apply colimitsOfShape_monotone _ _ _ (map_colimitsOfShape _ hf π₀Functor)
  rw [map_le_iff]

variable [h₂ : IsFiltered J]

instance (n : ℕ) : PreservesColimitsOfShape J (πSuccFunctor.{u} n) := by
  have := h₁
  have := h₂
  sorry

instance (n : ℕ) : PreservesColimitsOfShape J (πSuccArrowFunctor.{u} n) where
  preservesColimit {F} := ⟨fun {c} hc ↦ ⟨by
    apply Arrow.isColimitOfLeftRight
    · exact isColimitOfPreserves (πSuccFunctor n) hc
    · have : PreservesColimitsOfShape J (SSet.evaluation _⦋0⦌) := by
        apply evaluation_preservesColimitsOfShape
      exact isColimitOfPreserves (SSet.evaluation.obj (op ⦋0⦌)) hc⟩⟩

lemma isStableUnderColimitsOfShape_inverseImage_cartesianMorphisms_πSuccArrowFunctor (n : ℕ) :
    ((Arrow.cartesianMorphisms _).inverseImage
      (πSuccArrowFunctor.{u} n)).IsStableUnderColimitsOfShape J := by
  rw [MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  intro X Y f hf
  rw [inverseImage_iff]
  apply (Arrow.isStableUnderColimitsOfShape_cartesianMorphisms_type J).colimitsOfShape_le
  apply colimitsOfShape_monotone _ _ _ (map_colimitsOfShape _ hf _)
  rw [map_le_iff]

lemma isStableUnderColimitsOfShape_naiveW :
    naiveW.{u}.IsStableUnderColimitsOfShape J := by
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf
  have hf (j) := hf j
  simp only [naiveW, MorphismProperty.min_iff, MorphismProperty.iInf_iff] at hf ⊢
  exact ⟨isStableUnderColimitsOfShape_inverseImage_isomorphisms_π₀Functor _ _ _ _ _ _ hc₂ _
      (fun j ↦ (hf j).1),
    fun n ↦ isStableUnderColimitsOfShape_inverseImage_cartesianMorphisms_πSuccArrowFunctor
      _ _ _ _ _ _ _ hc₂ _ (fun j ↦ (hf j).2 n)⟩

end
namespace KanComplex

open SSet.modelCategoryQuillen in
lemma of_isColimit {K : Type*} [Category K] [IsFiltered K]
    [Small.{u} K] [LocallySmall.{u} K] {F : K ⥤ SSet.{u}}
    [hF : ∀ j, IsFibrant (F.obj j)]
    {c : Cocone F} (hc : IsColimit c) : IsFibrant c.pt where
  mem := by
    rw [fibrations_eq]
    intro A B f hf
    have : A.IsFinite := by
      simp [J] at hf
      obtain ⟨n, ⟨i⟩⟩ := hf
      infer_instance
    have : B.IsFinite := by
      simp [J] at hf
      obtain ⟨n, ⟨i⟩⟩ := hf
      infer_instance
    constructor
    intro t b sq
    obtain ⟨k, t, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (coyoneda.obj (Opposite.op A)) hc) t
    dsimp at t sq
    simp only [fibration_iff] at hF
    have := hF k f hf
    have sq' : CommSq t f (terminal.from _) (terminal.from _) := ⟨by simp⟩
    exact ⟨⟨{ l := sq'.lift ≫ c.ι.app k }⟩⟩

lemma W_iff_naiveW {X Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    W f ↔ naiveW f := by
  rw [W_iff, naiveW, MorphismProperty.min_iff, MorphismProperty.inverseImage_iff,
    MorphismProperty.isomorphisms.iff, isIso_iff_bijective, MorphismProperty.iInf_iff]
  refine and_congr (by rfl) (forall_congr' (fun n ↦ ?_))
  simp only [MorphismProperty.inverseImage_iff, πSuccArrowFunctor_obj, evaluation_obj_obj,
    πSuccArrowFunctor_map, Arrow.cartesianMorphisms_iff, Arrow.mk_left, Arrow.mk_right,
    Functor.id_obj, Arrow.homMk_left, Arrow.mk_hom, Arrow.homMk_right, Types.isPullback_iff,
    NatTrans.naturality, evaluation_obj_map, and_imp, true_and]
  constructor
  · intro hf
    constructor
    · intro x₁ x₂ hx hx'
      obtain ⟨⟨x, p₁⟩, rfl⟩ := (πSuccFunctorObjEquiv _ _ ).symm.surjective x₁
      obtain ⟨⟨x₂, p₂⟩, rfl⟩ := (πSuccFunctorObjEquiv _ _ ).symm.surjective x₂
      obtain rfl : x = x₂ := by simpa using hx'
      obtain rfl : p₁ = p₂ := (hf x _ rfl).1 (by simpa using hx)
      rfl
    · intro p x hp
      obtain ⟨⟨y, p⟩, rfl⟩ := (πSuccFunctorObjEquiv _ _ ).symm.surjective p
      simp only [πSuccNatTrans_app_equiv_symm_apply] at hp
      subst hp
      obtain ⟨q, rfl⟩ := (hf x _ rfl).2 p
      exact ⟨(πSuccFunctorObjEquiv _ _ ).symm ⟨x, q⟩, by simp⟩
  · rintro hf x _ rfl
    constructor
    · intro p₁ p₂ hp
      simpa using hf.1 ((πSuccFunctorObjEquiv _ _ ).symm ⟨_, p₁⟩)
        ((πSuccFunctorObjEquiv _ _ ).symm ⟨_, p₂⟩) (by simpa) (by simp)
    · intro p
      obtain ⟨q, hq₁, hq₂⟩ := hf.2 ((πSuccFunctorObjEquiv _ _ ).symm ⟨_, p⟩) x (by simp)
      obtain ⟨⟨x', q⟩, rfl⟩ := (πSuccFunctorObjEquiv _ _ ).symm.surjective q
      obtain rfl : x = x' := by simpa using hq₂
      simp only [πSuccFunctor_map_equiv_symm_apply, EmbeddingLike.apply_eq_iff_eq, Sigma.mk.injEq,
        heq_eq_eq, true_and] at hq₁
      exact ⟨q, hq₁.symm⟩

namespace W

variable (J : Type*) [Category J]

lemma isStableUnderColimitsOfShape [Small.{u} J] [LocallySmall.{u} J]  [IsFiltered J] :
    W.{u}.IsStableUnderColimitsOfShape J := by
  intro F₁ F₂ c₁ c₂ hc₁ hc₂ f hf
  have (j) := (hf j).isFibrant_src
  have (j) := (hf j).isFibrant_tgt
  have : IsFibrant c₁.pt := of_isColimit hc₁
  have : IsFibrant c₂.pt := of_isColimit hc₂
  replace hf (j) := hf j
  simp only [W_iff_naiveW] at hf ⊢
  exact isStableUnderColimitsOfShape_naiveW J _ _ _ _ _ hc₂ _ hf

end W

end KanComplex

end SSet
