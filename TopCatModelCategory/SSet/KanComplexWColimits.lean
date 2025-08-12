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

noncomputable def toπFunctor : coyoneda.obj (op A.quotient) ⟶ A.πFunctor := coequalizer.π _ _

@[reassoc]
lemma πFunctor_condition :
    coyoneda.map A.quotientι₀.op ≫ A.toπFunctor =
      coyoneda.map A.quotientι₁.op ≫ A.toπFunctor :=
  coequalizer.condition _ _

noncomputable def isColimitπFunctor : IsColimit (Cofork.ofπ _ A.πFunctor_condition) :=
  coequalizerIsCoequalizer _ _

noncomputable def πFunctorObjCofork (X : SSet.{u}):
    Cofork ((coyoneda.map A.quotientι₀.op).app X)
      ((coyoneda.map A.quotientι₁.op).app X) :=
  Cofork.ofπ (A.toπFunctor.app X) (congr_app A.πFunctor_condition X)

noncomputable def isColimitπFunctorObjCofork (X : SSet.{u}) :
    IsColimit (πFunctorObjCofork A X) :=
  isColimitCoforkMapOfIsColimit
    ((CategoryTheory.evaluation _ _).obj X) _ A.isColimitπFunctor

variable {A X} in
lemma toπFunctor_app_surjective : Function.Surjective (A.toπFunctor.app X) := by
  rw [← epi_iff_surjective]
  exact Cofork.IsColimit.epi (A.isColimitπFunctorObjCofork X)

noncomputable def πNatTrans : A.πFunctor ⟶ SSet.evaluation.obj (op ⦋0⦌) :=
  coequalizer.desc (coyoneda.map (const A.quotient₀ : Δ[0] ⟶ _).op ≫
    (stdSimplex.coyonedaObjIsoEvaluation 0).hom) (by
    simp only [← Functor.map_comp_assoc, ← op_comp,
      const_comp, quotientι₀_app_quotient₀, quotientι₁_app_quotient₀])

@[reassoc (attr := simp)]
lemma toπFunctor_πNatTrans :
    A.toπFunctor ≫ A.πNatTrans =
    (coyoneda.map (const A.quotient₀ : Δ[0] ⟶ _).op ≫
      (stdSimplex.coyonedaObjIsoEvaluation 0).hom) := by
  apply Limits.coequalizer.π_desc

@[simp]
lemma πNatTrans_app_toπFunctor_app {X : SSet.{u}} (f : A.quotient ⟶ X) :
    A.πNatTrans.app _ (A.toπFunctor.app _ f) = f.app _ A.quotient₀ := by
  simp [← FunctorToTypes.comp, toπFunctor_πNatTrans]

instance (J : Type*) [Category J] [h₁ : Small.{u} J] [LocallySmall.{u} J]
    [IsFiltered J] [B.IsFinite] :
    PreservesColimitsOfShape J A.πFunctor := by
  apply ObjectProperty.closedUnderColimitsOfShape_preservesColimitsOfShape
    J SSet.{u} (Type u) WalkingParallelPair (Subcomplex.isColimitπFunctor A)
  rintro (_ | _) <;> simp <;> infer_instance

namespace πFunctorEquiv

variable {X : SSet.{u}}

noncomputable def invFun' (x : X _⦋0⦌) :
      Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) → A.πFunctor.obj X :=
  Quot.lift (fun p ↦ A.toπFunctor.app X (A.descQuotient p.map x (by simp))) (by
    rintro p₁ p₂ ⟨h⟩
    let φ : (A.prod (⊤ : Subcomplex Δ[1])).quotient ⟶ X :=
      (A.prod _).descQuotient h.h x (by
        rw [← cancel_epi (Subcomplex.prodIso A (⊤ : Subcomplex Δ[1])).inv]
        have : (Subcomplex.prodIso A (⊤ : Subcomplex Δ[1])).inv ≫ Subcomplex.ι _ =
          _ ◁ Subcomplex.ι _ ≫ A.ι ▷ Δ[1] := rfl
        rw [reassoc_of% this, h.rel]
        rfl)
    have hφ₁ : A.descQuotient p₁.map x (by simp) = A.quotientι₀ ≫ φ := by aesop
    have hφ₂ : A.descQuotient p₂.map x (by simp) = A.quotientι₁ ≫ φ := by aesop
    have := congr_fun (congr_app A.πFunctor_condition X) φ
    dsimp at this ⊢
    rw [hφ₁, hφ₂, this])

lemma invFun'_eq {x : X _⦋0⦌}
    (p : Subcomplex.RelativeMorphism A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
  invFun' A x p.homotopyClass =
    A.toπFunctor.app X (A.descQuotient p.map x (by simp)) := rfl

variable (X)

@[simp]
noncomputable def invFun : (Σ (x : X _⦋0⦌),
      Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) → A.πFunctor.obj X :=
  fun ⟨x, p⟩ ↦ invFun' A x p

variable {X}

noncomputable def toFun'' (f : A.quotient ⟶ X) (x : X _⦋0⦌) (hx : f.app _ A.quotient₀ = x) :
    Σ (x : X _⦋0⦌), Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) :=
  ⟨x, RelativeMorphism.homotopyClass { map := A.toQuotient ≫ f }⟩

noncomputable def toFun' (f : A.quotient ⟶ X) :
    Σ (x : X _⦋0⦌), Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) :=
  toFun'' _ f _ rfl

lemma toFun'_eq (f : A.quotient ⟶ X) (x : X _⦋0⦌) (hx : f.app _ A.quotient₀ = x) :
    toFun' A f = ⟨x, RelativeMorphism.homotopyClass { map := A.toQuotient ≫ f }⟩ := by
  subst hx
  rfl

variable (X)

noncomputable def toFun : A.πFunctor.obj X →
    Σ (x : X _⦋0⦌), Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) :=
  Cofork.IsColimit.desc (A.isColimitπFunctorObjCofork X) (toFun' A) (by
      ext f : 1
      dsimp at f ⊢
      let x := f.app _ (quotient₀ _)
      rw [toFun'_eq _ _ x (by simp [x]), toFun'_eq _ _ x (by simp [x])]
      simp only [to_quotient₀_assoc, to_quotient₁_assoc, Sigma.mk.injEq, heq_eq_eq, true_and, x]
      apply RelativeMorphism.Homotopy.eq
      exact
        { h := toQuotient _ ≫ f
          h₀ := by simp
          h₁ := by simp
          rel := by
            have : (Subcomplex.prodIso A (⊤ : Subcomplex Δ[1])).inv ≫ Subcomplex.ι _ =
              _ ◁ Subcomplex.ι _ ≫ A.ι ▷ Δ[1] := rfl
            rw [← cancel_epi (A.toSSet ◁ (Subcomplex.topIso Δ[1]).hom), topIso_hom,
              ← reassoc_of% this]
            simp })

lemma toFun_eq (f : A.quotient ⟶ X) (x : X _⦋0⦌) (hx : f.app _ A.quotient₀ = x) :
    toFun A X (A.toπFunctor.app X f) =
      ⟨x, RelativeMorphism.homotopyClass { map := A.toQuotient ≫ f }⟩ := by
  have : A.toπFunctor.app X ≫ toFun A X = toFun' A :=
    Cofork.IsColimit.π_desc' (A.isColimitπFunctorObjCofork X) _ _
  refine (congr_fun this f).trans ?_
  rw [toFun'_eq _ _ _ hx]

@[simp]
lemma invFun'_toFun (p : A.πFunctor.obj X) :
    invFun' A _ (toFun A X p).2 = p := by
  obtain ⟨f, rfl⟩ := toπFunctor_app_surjective p
  rw [toFun_eq _ _ _ _ rfl, invFun'_eq]
  apply congr_arg
  aesop

end πFunctorEquiv

noncomputable def πFunctorEquiv (X : SSet.{u}) :
    A.πFunctor.obj X ≃ Σ (x : X _⦋0⦌),
      Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
        (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩) where
  toFun := πFunctorEquiv.toFun _ _
  invFun := πFunctorEquiv.invFun _ _
  left_inv _ := by simp
  right_inv := by
    rintro ⟨x, p⟩
    obtain ⟨p, rfl⟩ := p.eq_homotopyClass
    rw [πFunctorEquiv.invFun, πFunctorEquiv.invFun'_eq,
      πFunctorEquiv.toFun_eq _ _ _ x (by simp)]
    simp

lemma πFunctor_map_equiv_symm_apply {X : SSet.{u}} {x : X _⦋0⦌}
    (a : Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) {Y : SSet.{u}} (f : X ⟶ Y) :
    A.πFunctor.map f ((A.πFunctorEquiv X).symm ⟨x, a⟩) =
      (A.πFunctorEquiv Y).symm ⟨f.app _ x,
        a.postcomp (ψ := const ⟨f.app _ x, by simp⟩) { map := f } (by simp)⟩ := by
  obtain ⟨p, rfl⟩ := a.mk_surjective
  dsimp [πFunctorEquiv, πFunctorEquiv.invFun, πFunctorEquiv.invFun']
  erw [RelativeMorphism.homotopyClass_postcomp]
  dsimp [RelativeMorphism.homotopyClass]
  rw [← FunctorToTypes.naturality]
  apply congr_arg
  aesop

lemma πNatTrans_app_equiv_symm_apply {X : SSet.{u}} {x : X _⦋0⦌}
    (a : Subcomplex.RelativeMorphism.HomotopyClass A (Subcomplex.ofSimplex x)
      (const ⟨x, Subcomplex.mem_ofSimplex_obj x⟩)) :
    A.πNatTrans.app X ((A.πFunctorEquiv X).symm ⟨x, a⟩) = x := by
  obtain ⟨p, rfl⟩ := a.mk_surjective
  apply (A.πNatTrans_app_toπFunctor_app (A.descQuotient p.map x (by simp))).trans (by simp)

end Subcomplex

noncomputable def πSuccFunctor (n : ℕ) : SSet.{u} ⥤ Type u := (boundary (n + 1)).πFunctor

noncomputable def πSuccFunctorObjEquiv (n : ℕ) (X : SSet.{u}) :
    (πSuccFunctor n).obj X ≃ Σ (x : X _⦋0⦌), KanComplex.π (n + 1) X x := by
  apply Subcomplex.πFunctorEquiv

@[simp]
lemma πSuccFunctor_map_equiv_symm_apply {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}
    (a : KanComplex.π (n + 1) X x) {Y : SSet.{u}} (f : X ⟶ Y) :
    (πSuccFunctor n).map f ((πSuccFunctorObjEquiv n X).symm ⟨x, a⟩) =
      (πSuccFunctorObjEquiv n Y).symm (⟨_, KanComplex.mapπ f (n + 1) x _ rfl a⟩) := by
  apply Subcomplex.πFunctor_map_equiv_symm_apply

noncomputable def πSuccNatTrans (n : ℕ) : πSuccFunctor.{u} n ⟶ SSet.evaluation.obj (op ⦋0⦌) :=
  Subcomplex.πNatTrans _

@[simp]
lemma πSuccNatTrans_app_equiv_symm_apply {n : ℕ} {X : SSet.{u}} {x : X _⦋0⦌}
    (a : KanComplex.π (n + 1) X x) :
    (πSuccNatTrans n).app X ((πSuccFunctorObjEquiv n X).symm ⟨x, a⟩) = x :=
  Subcomplex.πNatTrans_app_equiv_symm_apply _ _

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

instance isStableUnderColimitsOfShape_inverseImage_isomorphisms_π₀Functor :
    ((isomorphisms _).inverseImage
      π₀Functor.{u}).IsStableUnderColimitsOfShape J := by
  rw [isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  intro X Y f hf
  rw [inverseImage_iff]
  exact colimitsOfShape_le _
    (colimitsOfShape_monotone (by rw [map_le_iff]) _ _ (map_colimitsOfShape _ hf π₀Functor))

variable [LocallySmall.{u} J] [IsFiltered J]

instance (n : ℕ) : PreservesColimitsOfShape J (πSuccFunctor.{u} n) := by
  dsimp only [πSuccFunctor]
  infer_instance

instance (n : ℕ) : PreservesColimitsOfShape J (πSuccArrowFunctor.{u} n) where
  preservesColimit {F} := ⟨fun {c} hc ↦ ⟨by
    apply Arrow.isColimitOfLeftRight
    · exact isColimitOfPreserves (πSuccFunctor n) hc
    · have : PreservesColimitsOfShape J (SSet.evaluation _⦋0⦌) := by
        apply evaluation_preservesColimitsOfShape
      exact isColimitOfPreserves (SSet.evaluation.obj (op ⦋0⦌)) hc⟩⟩

instance isStableUnderColimitsOfShape_inverseImage_cartesianMorphisms_πSuccArrowFunctor (n : ℕ) :
    ((Arrow.cartesianMorphisms _).inverseImage
      (πSuccArrowFunctor.{u} n)).IsStableUnderColimitsOfShape J := by
  rw [MorphismProperty.isStableUnderColimitsOfShape_iff_colimitsOfShape_le]
  intro X Y f hf
  rw [inverseImage_iff]
  exact colimitsOfShape_le _
    (colimitsOfShape_monotone (by rw [map_le_iff]) _ _ (map_colimitsOfShape _ hf _))


instance isStableUnderColimitsOfShape_naiveW :
    naiveW.{u}.IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    have hf (j) := hf j
    simp only [naiveW, MorphismProperty.min_iff, MorphismProperty.iInf_iff] at hf ⊢
    exact ⟨colimitsOfShape_le _ (colimitsOfShape.mk' _ _ _ _ hc₁ hc₂ _ (fun j ↦ (hf j).1) _ hφ),
      fun n ↦ colimitsOfShape_le _
        (colimitsOfShape.mk' _ _ _ _ hc₁ hc₂ _ (fun j ↦ (hf j).2 n) _ hφ)⟩

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

instance isStableUnderColimitsOfShape [Small.{u} J] [LocallySmall.{u} J]  [IsFiltered J] :
    W.{u}.IsStableUnderColimitsOfShape J where
  condition F₁ F₂ c₁ c₂ hc₁ hc₂ f hf φ hφ := by
    have (j : J) := (hf j).isFibrant_src
    have (j : J) := (hf j).isFibrant_tgt
    have : IsFibrant c₁.pt := of_isColimit hc₁
    have : IsFibrant c₂.pt := of_isColimit hc₂
    replace hf (j) := hf j
    simp only [W_iff_naiveW] at hf ⊢
    exact MorphismProperty.colimitsOfShape_le _
      (MorphismProperty.colimitsOfShape.mk' _ _ _ _ hc₁ hc₂ f hf _ hφ)

end W

end KanComplex

end SSet
