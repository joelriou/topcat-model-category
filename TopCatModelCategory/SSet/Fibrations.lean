module

public import TopCatModelCategory.SSet.AnodyneExtensionsAdjunctions
public import TopCatModelCategory.SSet.Monoidal
public import TopCatModelCategory.SSet.Fiber

@[expose] public section

universe u

open CategoryTheory MonoidalCategory HomotopicalAlgebra Limits MonoidalClosed Opposite Simplicial
  SSet.modelCategoryQuillen

namespace SSet

instance {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : Fibration f] [hg : Fibration g] :
    Fibration (f ≫ g) := by
  rw [fibration_iff] at hf hg ⊢
  apply MorphismProperty.comp_mem <;> assumption

instance {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] : Fibration f := by
  rw [fibration_iff]
  exact MorphismProperty.rlp_of_isIso J f

instance : IsFibrant (Δ[0] : SSet) := by
  rw [isFibrant_iff_of_isTerminal (𝟙 _) stdSimplex.isTerminalObj₀]
  infer_instance

end SSet

namespace CategoryTheory

namespace Limits

variable {C : Type*} [Category C]
  {X Y Z : C ⥤ Type u} {f : Y ⟶ X} {g : Z ⟶ X}

lemma FunctorToTypes.pullback_ext {A : C} {x y : (pullback f g).obj A} :
    x = y ↔ (pullback.fst f g).app _ x = (pullback.fst f g).app _ y ∧
      (pullback.snd f g).app _ x = (pullback.snd f g).app _ y := by
  constructor
  · rintro rfl
    tauto
  · rintro ⟨_, _⟩
    apply (PullbackCone.IsLimit.equivPullbackObj
      ((IsPullback.of_hasPullback f g).map ((evaluation _ _ ).obj A)).isLimit).injective
    ext <;> assumption

end Limits

namespace Arrow

variable {C : Type*} [Category C]

/-abbrev LiftStruct {f g : Arrow C} (φ : f ⟶ g) := (CommSq.mk φ.w).LiftStruct

lemma hasLiftingProperty_iff {A B X Y : C} (i : A ⟶ B) (p : X ⟶ Y) :
    HasLiftingProperty i p ↔ ∀ (φ : Arrow.mk i ⟶ Arrow.mk p), Nonempty (LiftStruct φ) := by
  constructor
  · intro _ φ
    have sq : CommSq φ.left i p φ.right := (CommSq.mk φ.w)
    exact ⟨{ l := sq.lift }⟩
  · intro h
    exact ⟨fun {f g} sq ↦ ⟨h (Arrow.homMk f g sq.w)⟩⟩-/

end Arrow

end CategoryTheory

namespace SSet

variable {A B X Y : SSet.{u}}

lemma yonedaEquiv_apply {n : SimplexCategory} (f : stdSimplex.obj n ⟶ X) :
    yonedaEquiv f = f.app _ (stdSimplex.objEquiv.symm (𝟙 _)) := rfl

lemma eq_const_iff_range_le_ofSimplex (f : X ⟶ Y) (y : Y _⦋0⦌) :
    f = const y ↔ Subcomplex.range f ≤ Subcomplex.ofSimplex y := by
  rw [Subcomplex.le_ofSimplex_iff, ← cancel_epi (toRangeSubcomplex f),
    toRangeSubcomplex_ι, comp_const]

section

variable {K L : SSet.{u}} (i : A ⟶ B) (f : K ⟶ L) (p : X ⟶ Y)

noncomputable abbrev fromPushoutProduct : pushout (i ▷ K) (A ◁ f) ⟶ B ⊗ L :=
  pushout.desc (B ◁ f) (i ▷ L) (by simp only [whisker_exchange])

variable {f i} in
noncomputable def fromPushoutProductCongr {K' L' A' B' : SSet.{u}} {f' : K' ⟶ L'}
    {i' : A' ⟶ B'}
    (e₁ : Arrow.mk f ≅ Arrow.mk f') (e₂ : Arrow.mk i ≅ Arrow.mk i') :
    Arrow.mk (fromPushoutProduct i f) ≅ Arrow.mk (fromPushoutProduct i' f') := by
  refine Arrow.isoMk
    -- generalize as `pushout.mapIso`...
    { hom := pushout.map _ _ _ _ (e₂.hom.right ⊗ₘ e₁.hom.left) (e₂.hom.left ⊗ₘ e₁.hom.right)
        (e₂.hom.left ⊗ₘ e₁.hom.left) ?_ ?_
      inv := pushout.map _ _ _ _ (e₂.inv.right ⊗ₘ e₁.inv.left) (e₂.inv.left ⊗ₘ e₁.inv.right)
        (e₂.inv.left ⊗ₘ e₁.inv.left) ?_ ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
    (Arrow.rightFunc.mapIso e₂ ⊗ᵢ Arrow.rightFunc.mapIso e₁) ?_
  · have := e₂.hom.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange, ← comp_whiskerRight_assoc, this]
  · have := e₁.hom.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp, this]
  · have := e₂.inv.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange, ← comp_whiskerRight_assoc, this]
  · have := e₁.inv.w
    dsimp at this
    simp only [tensorHom_def, Category.assoc, whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp, this]
  · simp [pushout.map_comp]
  · simp [pushout.map_comp]
  · dsimp only [Arrow.mk_left, Arrow.mk_right, Functor.id_obj, Functor.id_map, Arrow.mk_hom,
      eq_mp_eq_cast, cast_eq, _root_.id_eq, eq_mpr_eq_cast, tensorIso_hom, Functor.mapIso_hom,
      Arrow.rightFunc_map]
    ext : 1
    · simp [tensorHom_def, whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp]
    · have := e₂.hom.w
      dsimp at this
      simp only [tensorHom_def, pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc,
        ← comp_whiskerRight_assoc, whisker_exchange, this]

noncomputable def fromPushoutProductιιIso (A : K.Subcomplex) (B : L.Subcomplex) :
    Arrow.mk (fromPushoutProduct A.ι B.ι) ≅ Arrow.mk (A.unionProd B).ι :=
  Arrow.isoMk (Subcomplex.unionProd.isPushout A B).isoPushout.symm (Iso.refl _)

noncomputable abbrev ihomToPullback :
    (ihom B).obj X ⟶ pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y) :=
  pullback.lift ((MonoidalClosed.pre i).app X) ((ihom B).map p) (by simp)

variable {f i p} in
@[simps]
noncomputable def arrowMkFromPushoutProductHomEquiv :
    (Arrow.mk (fromPushoutProduct i f) ⟶ Arrow.mk p) ≃
      (Arrow.mk f ⟶ Arrow.mk (ihomToPullback i p)) where
  toFun φ :=
    Arrow.homMk (curry (pushout.inl _ _ ≫ φ.left))
      (pullback.lift (curry (pushout.inr _ _ ≫ φ.left)) (curry φ.right) (by
        have := φ.w
        dsimp at this
        rw [← curry_natural_right, Category.assoc, this, pushout.inr_desc_assoc,
          ← curry_whiskerRight_comp]
        dsimp)) (by
        dsimp
        ext : 1
        · dsimp
          simp only [Category.assoc, pullback.lift_fst,
            ← curry_whiskerRight_comp, ← curry_natural_left,
            pushout.condition_assoc]
        · dsimp
          have := φ.w
          dsimp at this
          simp only [Category.assoc, pullback.lift_snd, ← curry_natural_left,
            ← curry_natural_right, this, pushout.inl_desc_assoc])
  invFun ψ :=
    Arrow.homMk (pushout.desc (uncurry ψ.left) (uncurry (ψ.right ≫ pullback.fst _ _)) (by
        have := ψ.w =≫ pullback.fst _ _
        dsimp at this
        rw [Category.assoc, Category.assoc, pullback.lift_fst] at this
        rw [← uncurry_natural_left, ← this, whiskerRight_comp_uncurry]
        dsimp))
      (uncurry (ψ.right ≫ pullback.snd _ _)) (by
        dsimp only [Arrow.mk_left, Arrow.mk_hom]
        ext : 1
        · have := ψ.w =≫ pullback.snd _ _
          dsimp at this
          rw [Category.assoc, Category.assoc, pullback.lift_snd] at this
          rw [pushout.inl_desc_assoc, pushout.inl_desc_assoc,
            ← uncurry_natural_right, this, uncurry_natural_left]
        · rw [pushout.inr_desc_assoc, pushout.inr_desc_assoc,
            ← uncurry_natural_right, Category.assoc, pullback.condition,
            whiskerRight_comp_uncurry, Category.assoc]
          dsimp)
  left_inv φ := by
    ext : 1
    · dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      ext : 1
      · rw [pushout.inl_desc, uncurry_curry]
      · rw [pushout.inr_desc, pullback.lift_fst, uncurry_curry]
    · dsimp
      rw [pullback.lift_snd, uncurry_curry]
  right_inv ψ := by
    ext : 1
    · dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      rw [pushout.inl_desc, curry_uncurry]
    · dsimp only [Arrow.mk_right, Arrow.mk_left, Arrow.mk_hom,
        Arrow.homMk_left, Arrow.homMk_right]
      ext : 1
      · rw [pullback.lift_fst, pushout.inr_desc, curry_uncurry]
      · rw [pullback.lift_snd, curry_uncurry]

variable {f i p} in
noncomputable def fromPushoutProductLiftStructEquiv
    (φ : Arrow.mk (fromPushoutProduct f i) ⟶ Arrow.mk p) :
    Arrow.LiftStruct φ ≃
      Arrow.LiftStruct (arrowMkFromPushoutProductHomEquiv φ) where
  toFun l :=
    { l := curry l.l
      fac_left := by
        have := pushout.inl _ _ ≫= l.fac_left
        dsimp at this ⊢
        rw [← this, pushout.inl_desc_assoc, curry_natural_left]
      fac_right := by
        have h₁ := pushout.inr _ _ ≫= l.fac_left
        have h₂ := l.fac_right
        dsimp at h₁ h₂ ⊢
        ext : 1
        · simp only [Category.assoc, pullback.lift_fst, ← h₁, pushout.inr_desc_assoc,
            curry_whiskerRight_comp]
        · simp only [Category.assoc, pullback.lift_snd, ← h₂, curry_natural_right] }
  invFun l :=
    { l := uncurry l.l
      fac_left := by
        have h₁ := l.fac_left
        have h₂ := l.fac_right =≫ pullback.fst _ _
        dsimp at h₁ h₂ ⊢
        rw [pullback.lift_fst, Category.assoc, pullback.lift_fst] at h₂
        ext : 1
        · rw [pushout.inl_desc_assoc]
          apply curry_injective
          simp only [← h₁, curry_natural_left, curry_uncurry]
        · rw [pushout.inr_desc_assoc]
          apply curry_injective
          simp only [← h₂, curry_whiskerRight_comp, curry_uncurry]
      fac_right := by
        have := l.fac_right =≫ pullback.snd _ _
        dsimp at this ⊢
        rw [pullback.lift_snd, Category.assoc, pullback.lift_snd] at this
        apply curry_injective
        simp only [← this, ← uncurry_natural_right, curry_uncurry] }
  left_inv l := by ext : 1; apply uncurry_curry
  right_inv l := by ext : 1; apply curry_uncurry

lemma hasLiftingProperty_iHomToPullback_iff :
    HasLiftingProperty f (ihomToPullback i p) ↔
      HasLiftingProperty (fromPushoutProduct i f) p := by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h φ
    exact ⟨(fromPushoutProductLiftStructEquiv _).symm (h _).some⟩
  · intro h ψ
    obtain ⟨φ, rfl⟩ := arrowMkFromPushoutProductHomEquiv.surjective ψ
    exact ⟨fromPushoutProductLiftStructEquiv _ ((h φ).some)⟩

end

section

instance (i : A ⟶ B) (p : X ⟶ Y) [Mono i] [Fibration p] :
    Fibration (ihomToPullback i p) := by
  rw [modelCategoryQuillen.fibration_iff]
  intro _ _ _ hf
  simp only [modelCategoryQuillen.J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨j⟩⟩ := hf
  rw [hasLiftingProperty_iHomToPullback_iff]
  apply anodyneExtensions.hasLeftLiftingProperty
  refine (anodyneExtensions.arrow_mk_iso_iff ?_).2
    (anodyneExtensions.subcomplex_unionProd_mem_of_right (Subcomplex.range i) _
    (anodyneExtensions.horn_ι_mem _ j))
  exact fromPushoutProductCongr (Iso.refl _)
    (Arrow.isoMk (asIso (toRangeSubcomplex i)) (Iso.refl _)) ≪≫ fromPushoutProductιιIso _ _

end

@[simps! hom_left inv_left hom_right]
noncomputable def ihomToPullbackTerminalFromArrowIso (f : A ⟶ B) (Z : SSet.{u}) :
    Arrow.mk (ihomToPullback f (terminal.from Z)) ≅
      Arrow.mk ((MonoidalClosed.pre f).app Z) :=
  Arrow.isoMk (Iso.refl _)
    { hom := pullback.fst _ _
      inv := pullback.lift (𝟙 _) (by
        apply IsTerminal.from
        apply isLimitOfHasTerminalOfPreservesLimit) (by
          apply IsTerminal.hom_ext
          apply isLimitOfHasTerminalOfPreservesLimit)
      hom_inv_id := by
        dsimp
        ext : 1
        · simp
        · apply IsTerminal.hom_ext
          apply isLimitOfHasTerminalOfPreservesLimit
      inv_hom_id := by simp }

instance {Z : SSet.{u}} (f : A ⟶ B) [Mono f] [IsFibrant Z] :
    Fibration ((MonoidalClosed.pre f).app Z) := by
  rw [HomotopicalAlgebra.fibration_iff]
  refine ((fibrations _).arrow_mk_iso_iff (ihomToPullbackTerminalFromArrowIso f Z)).1 ?_
  rw [← HomotopicalAlgebra.fibration_iff]
  infer_instance

@[simps! hom_left inv_left hom_right]
noncomputable def ihomToPullbackInitialToArrowIso
    (A : SSet.{u}) {X Y : SSet.{u}} (p : X ⟶ Y):
    Arrow.mk (ihomToPullback (initial.to A) p) ≅
      Arrow.mk ((ihom A).map p) :=
  Arrow.isoMk (Iso.refl _)
    { hom := pullback.snd _ _
      inv := pullback.lift (curry (by
        apply IsInitial.to
        apply isColimitOfHasInitialOfPreservesColimit (tensorRight _))) (𝟙 _) (by
          apply uncurry_injective
          apply IsInitial.hom_ext
          apply isColimitOfHasInitialOfPreservesColimit (tensorRight _))
      hom_inv_id := by
        dsimp
        ext : 1
        · apply uncurry_injective
          apply IsInitial.hom_ext
          apply isColimitOfHasInitialOfPreservesColimit (tensorRight _)
        · simp
      inv_hom_id := by simp }

open MorphismProperty in
instance (A : SSet.{u}) : Mono (initial.to A) := by
  have e : Arrow.mk (initial.to A) ≅ Arrow.mk (⊥ : A.Subcomplex).ι :=
    Arrow.isoMk (initialIsInitial.coconePointUniqueUpToIso
        (Subcomplex.isInitialBot A)) (Iso.refl _)
        (by dsimp; apply Subsingleton.elim)
  exact ((monomorphisms _).arrow_mk_iso_iff e).2
    (monomorphisms.infer_property _)

instance (p : X ⟶ Y) [Fibration p] :
    Fibration ((ihom A).map p) := by
  rw [HomotopicalAlgebra.fibration_iff]
  refine ((fibrations _).arrow_mk_iso_iff (ihomToPullbackInitialToArrowIso A p)).1 ?_
  rw [← HomotopicalAlgebra.fibration_iff]
  infer_instance

instance {A X : SSet.{u}} [IsFibrant X] : IsFibrant (A ⟶[SSet] X) := by
  rw [isFibrant_iff_of_isTerminal ((ihom A).map (terminal.from X))]
  · infer_instance
  · apply isLimitOfHasTerminalOfPreservesLimit

section

variable {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y} (sq : CommSq t i p b)

include sq in
noncomputable def ihomToPullbackTgt₀Mk :
    pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y) _⦋0⦌ :=
  yonedaEquiv (pullback.lift (yonedaEquiv.symm (ihom₀Equiv.symm t))
      (yonedaEquiv.symm (ihom₀Equiv.symm b))
        (yonedaEquiv.injective (ihom₀Equiv.injective (by
        simp only [yonedaEquiv_symm_zero, const_comp, yonedaEquiv₀,
          ← ihom₀Equiv_symm_comp, ← ihom₀Equiv_symm_comp', sq.w]))))

@[simp]
lemma pullback_fst_app_ihomToPullbackTgt₀Mk :
    (pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
      (ihomToPullbackTgt₀Mk sq) = ihom₀Equiv.symm t := by
  apply yonedaEquiv.symm.injective
  simp [← yonedaEquiv_symm_comp, ihomToPullbackTgt₀Mk]

@[simp]
lemma pullback_snd_app_ihomToPullbackTgt₀Mk :
    (pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _
      (ihomToPullbackTgt₀Mk sq) = ihom₀Equiv.symm b := by
  apply yonedaEquiv.symm.injective
  simp [← yonedaEquiv_symm_comp, ihomToPullbackTgt₀Mk]

lemma ihomToPullbackTgt₀Mk_surjective
    (x : pullback ((ihom A).map p) ((MonoidalClosed.pre i).app Y) _⦋0⦌) :
    ∃ (t : A ⟶ X) (b : B ⟶ Y) (sq : CommSq t i p b),
      ihomToPullbackTgt₀Mk sq = x := by
  refine ⟨ihom₀Equiv ((pullback.fst ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _ x),
    ihom₀Equiv ((pullback.snd ((ihom A).map p) ((MonoidalClosed.pre i).app Y)).app _ x), ⟨?_⟩, ?_⟩
  · apply ihom₀Equiv.symm.injective
    rw [ihom₀Equiv_symm_comp', Equiv.symm_apply_apply,
      ihom₀Equiv_symm_comp, Equiv.symm_apply_apply]
    exact congr_fun (congr_app (pullback.condition
      (f := (ihom A).map p) (g := (MonoidalClosed.pre i).app Y)) (op ⦋0⦌)) x
  · simp only [ihomToPullbackTgt₀Mk, Equiv.symm_apply_apply]
    apply yonedaEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    ext : 1 <;> simp

noncomputable abbrev ihomToPullbackFiber : ((ihom B).obj X).Subcomplex :=
  Subcomplex.fiber (ihomToPullback i p)
    (ihomToPullbackTgt₀Mk sq)

lemma range_le_ihomToPullbackFiber_iff {Z : SSet.{u}} (f : Z ⟶ (ihom B).obj X) :
    Subcomplex.range f ≤ ihomToPullbackFiber sq ↔
      f ≫ (MonoidalClosed.pre i).app X = SSet.const (ihom₀Equiv.symm t) ∧
      f ≫ (ihom B).map p = SSet.const (ihom₀Equiv.symm b) := by
  rw [ihomToPullbackFiber, ihomToPullbackTgt₀Mk, Subcomplex.le_fiber_iff, ihomToPullback,
    pullback.hom_ext_iff, Category.assoc, Category.assoc, pullback.lift_fst,
      pullback.lift_snd, const_comp, const_comp, yonedaEquiv_apply,
      ← FunctorToTypes.comp, ← FunctorToTypes.comp,
      pullback.lift_fst, pullback.lift_snd,
      yonedaEquiv_symm_zero, yonedaEquiv_symm_zero, const_app, const_app,
      SimplexCategory.const_eq_id, op_id,
      FunctorToTypes.map_id_apply, FunctorToTypes.map_id_apply,
      eq_const_iff_range_le_ofSimplex, eq_const_iff_range_le_ofSimplex,
      eq_const_iff_range_le_ofSimplex, eq_const_iff_range_le_ofSimplex,
      Subcomplex.range_comp, Subcomplex.range_comp,
      Subcomplex.range_comp, Subcomplex.range_comp]
  simp only [Subcomplex.range_ι]

lemma le_ihomToPullbackFiber_iff (Z : ((ihom B).obj X).Subcomplex) :
    Z ≤ ihomToPullbackFiber sq ↔
      Z.ι ≫ (MonoidalClosed.pre i).app X = SSet.const (ihom₀Equiv.symm t) ∧
      Z.ι ≫ (ihom B).map p = SSet.const (ihom₀Equiv.symm b) := by
  rw [← range_le_ihomToPullbackFiber_iff sq]
  simp only [Subcomplex.range_ι]

lemma ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff (f : B ⟶ X) :
    ihom₀Equiv.symm f ∈ (ihomToPullbackFiber sq).obj (op ⦋0⦌) ↔
      i ≫ f = t ∧ f ≫ p = b:= by
  have := range_le_ihomToPullbackFiber_iff sq
    (yonedaEquiv.symm (ihom₀Equiv.symm f))
  simp only [yonedaEquiv_symm_zero, Subcomplex.range_eq_ofSimplex, yonedaEquiv₀,
      Subcomplex.ofSimplex_le_iff] at this
  convert this using 2
  all_goals
  · rw [← EmbeddingLike.apply_eq_iff_eq ihom₀Equiv.symm,
      ← EmbeddingLike.apply_eq_iff_eq yonedaEquiv.symm]
    rfl

@[reassoc (attr := simp)]
lemma ihomToPullbackFiber_ihom_map :
    (ihomToPullbackFiber sq).ι ≫ (ihom B).map p = SSet.const (ihom₀Equiv.symm b) :=
  ((le_ihomToPullbackFiber_iff sq _).1 (by rfl)).2

@[reassoc (attr := simp)]
lemma ihomToPullbackFiber_pre_app :
    (ihomToPullbackFiber sq).ι ≫ (MonoidalClosed.pre i).app X = SSet.const (ihom₀Equiv.symm t) :=
  ((le_ihomToPullbackFiber_iff sq _).1 (by rfl)).1

instance [Mono i] [Fibration p] :
    IsFibrant (C := SSet.{u}) (ihomToPullbackFiber sq) := by
  dsimp only [ihomToPullbackFiber]
  infer_instance

end

section

instance (i : A ⟶ B) : IsIso ((MonoidalClosed.pre i).app (⊤_ SSet)) :=
  ⟨(IsTerminal.isTerminalObj _ _ terminalIsTerminal).from _,
    (IsTerminal.isTerminalObj _ _ terminalIsTerminal).hom_ext _ _,
    (IsTerminal.isTerminalObj _ _ terminalIsTerminal).hom_ext _ _⟩

instance (i : A ⟶ B) [Mono i] [IsFibrant X] :
    Fibration ((MonoidalClosed.pre i).app X) := by
  let h : PullbackIhom i (terminal.from X) :=
    { pt := (ihom A).obj X
      fst := 𝟙 _
      snd := curry (terminal.from _)
      isPullback := by
        dsimp
        apply IsPullback.of_horiz_isIso
        constructor
        apply IsTerminal.hom_ext
        apply IsTerminal.isTerminalObj
        exact terminalIsTerminal }
  have : h.π = (MonoidalClosed.pre i).app X := by
    apply h.isPullback.hom_ext
    · rw [h.π_fst]
      simp [h]
    · apply uncurry_injective
      apply Subsingleton.elim
  rw [← this]
  infer_instance

end

-- a consequence of the right lifting property with respect
-- to the horn inclusion `Λ[2, 1] ⟶ Δ[2]`: it is possible
-- to compose path above if we provide a composition below
lemma exists_path_composition_above_of_fibration
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₁₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂)
    (s : Δ[2] ⟶ Y)
    (hs₀₁ : stdSimplex.δ 2 ≫ s = x₀₁ ≫ p)
    (hs₁₂ : stdSimplex.δ 0 ≫ s = x₁₂ ≫ p) :
    ∃ (x₀₂ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₀₂ =
        stdSimplex.δ 1 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₀₂ =
        stdSimplex.δ 0 ≫ x₁₂ ∧
        x₀₂ ≫ p = stdSimplex.δ 1 ≫ s := by
  obtain ⟨t, ht₁, ht₂⟩ := horn₂₁.isPushout.exists_desc x₀₁ x₁₂ h
  have sq : CommSq t (horn 2 1).ι p s := ⟨by
    apply horn₂₁.isPushout.hom_ext
    · simp [reassoc_of% ht₁, ← hs₀₁]
    · simp [reassoc_of% ht₂, ← hs₁₂]⟩
  refine ⟨stdSimplex.δ 1 ≫ sq.lift, ?_, ?_, ?_⟩
  · rw [← ht₁]
    conv_rhs => rw [← sq.fac_left]
    rw [horn.ι_ι_assoc]
    symm
    apply stdSimplex.δ_comp_δ_assoc (n := 0) (i := 1) (j := 1) (by rfl)
  · rw [← ht₂]
    conv_rhs => rw [← sq.fac_left]
    rw [horn.ι_ι_assoc]
    symm
    apply stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0)
  · rw [Category.assoc, sq.fac_right]

lemma exists_path_composition_above_of_fibration'
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₁₂ : Δ[1] ⟶ X) (b : Y _⦋0⦌)
    (h : stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂)
    (hx : x₀₁ ≫ p = const b) :
    ∃ (x₀₂ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₀₂ = stdSimplex.δ 1 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂ ∧
        x₀₂ ≫ p = x₁₂ ≫ p := by
  obtain ⟨x₀₂, eq₁, eq₂, eq₃⟩ := exists_path_composition_above_of_fibration p x₀₁ x₁₂ h
    (stdSimplex.σ 0 ≫ x₁₂ ≫ p) (by
      have h₁ := h =≫ p
      simp only [Category.assoc] at h₁
      have h₂ := stdSimplex.{u}.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by simp)
      dsimp at h₂
      rw [reassoc_of% h₂, ← h₁, hx, comp_const, comp_const])
    (stdSimplex.{u}.δ_comp_σ_self_assoc (n := 1) (i := 0) _)
  refine ⟨x₀₂, eq₁, eq₂, ?_⟩
  have := stdSimplex.{u}.δ_comp_σ_succ (n := 1) (i := 0)
  dsimp at this
  rw [eq₃, reassoc_of% this]

lemma exists_path_composition₀_above_of_fibration
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₀₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂)
    (s : Δ[2] ⟶ Y)
    (hs₀₁ : stdSimplex.δ 2 ≫ s = x₀₁ ≫ p)
    (hs₀₂ : stdSimplex.δ 1 ≫ s = x₀₂ ≫ p) :
    ∃ (x₁₂ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₁₂ =
        stdSimplex.δ 0 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₁₂ =
        stdSimplex.δ 0 ≫ x₀₂ ∧
        x₁₂ ≫ p = stdSimplex.δ 0 ≫ s := by
  obtain ⟨t, ht₁, ht₂⟩ := horn₂₀.isPushout.exists_desc x₀₁ x₀₂ h
  have sq : CommSq t (horn 2 0).ι p s := ⟨by
    apply horn₂₀.isPushout.hom_ext
    · simp [reassoc_of% ht₁, ← hs₀₁]
    · simp [reassoc_of% ht₂, ← hs₀₂]⟩
  refine ⟨stdSimplex.δ 0 ≫ sq.lift, ?_, ?_, ?_⟩
  · rw [← ht₁]
    conv_rhs => rw [← sq.fac_left]
    rw [horn.ι_ι_assoc]
    symm
    apply stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp)
  · rw [← ht₂]
    conv_rhs => rw [← sq.fac_left]
    rw [horn.ι_ι_assoc]
    symm
    apply stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 0)
  · rw [Category.assoc, sq.fac_right]

lemma exists_path_composition₀_above_of_fibration'
    (p : X ⟶ Y) [Fibration p] (x₀₁ x₀₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂)
    (hx : x₀₁ ≫ p = x₀₂ ≫ p) :
    ∃ (x₁₂ : Δ[1] ⟶ X) (b : Y _⦋0⦌),
      stdSimplex.δ 1 ≫ x₁₂ = stdSimplex.δ 0 ≫ x₀₁ ∧
      stdSimplex.δ 0 ≫ x₁₂ = stdSimplex.δ 0 ≫ x₀₂ ∧
        x₁₂ ≫ p = const b := by
  obtain ⟨x₁₂, eq₁, eq₂, eq₃⟩ :=
    exists_path_composition₀_above_of_fibration p x₀₁ x₀₂ h
      (stdSimplex.σ 1 ≫ x₀₁ ≫ p) (stdSimplex.δ_comp_σ_succ_assoc (n := 1) (i := 1) _) (by
        rw [hx]
        exact stdSimplex.δ_comp_σ_self_assoc (n := 1) (i := 1) _)
  refine ⟨x₁₂, yonedaEquiv (stdSimplex.δ 0 ≫ x₀₁ ≫ p), eq₁, eq₂, ?_⟩
  have := stdSimplex.{u}.δ_comp_σ_of_le (n := 0) (i := 0) (j := 0) (by simp)
  dsimp at this
  rw [eq₃, reassoc_of% this]
  have : stdSimplex.{u}.σ (0 : Fin 1) = const (yonedaEquiv (𝟙 _)) := by
    apply yonedaEquiv.injective
    ext i
    fin_cases i <;> rfl
  simp [this]
  rfl

lemma exists_path_composition₂_above_of_fibration
    (p : X ⟶ Y) [Fibration p] (x₀₂ x₁₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂)
    (s : Δ[2] ⟶ Y)
    (hs₀₂ : stdSimplex.δ 1 ≫ s = x₀₂ ≫ p)
    (hs₁₂ : stdSimplex.δ 0 ≫ s = x₁₂ ≫ p) :
    ∃ (x₀₁ : Δ[1] ⟶ X),
      stdSimplex.δ 1 ≫ x₀₁ =
        stdSimplex.δ 1 ≫ x₀₂ ∧
      stdSimplex.δ 0 ≫ x₀₁ =
        stdSimplex.δ 1 ≫ x₁₂ ∧
        x₀₁ ≫ p = stdSimplex.δ 2 ≫ s := by
  obtain ⟨t, ht₁, ht₂⟩ := horn₂₂.isPushout.exists_desc x₀₂ x₁₂ h
  have sq : CommSq t (horn 2 2).ι p s := ⟨by
    apply horn₂₂.isPushout.hom_ext
    · simp [reassoc_of% ht₁, ← hs₀₂]
    · simp [reassoc_of% ht₂, ← hs₁₂]⟩
  refine ⟨stdSimplex.δ 2 ≫ sq.lift, ?_, ?_, ?_⟩
  · rw [← ht₁]
    conv_rhs => rw [← sq.fac_left]
    rw [horn.ι_ι_assoc]
    symm
    apply stdSimplex.δ_comp_δ_self_assoc (n := 0) (i := 1)
  · rw [← ht₂]
    conv_rhs => rw [← sq.fac_left]
    rw [horn.ι_ι_assoc]
    apply stdSimplex.δ_comp_δ_assoc (n := 0) (i := 0) (j := 1) (by simp)
  · rw [Category.assoc, sq.fac_right]

lemma exists_path_composition₂_above_of_fibration'
    (p : X ⟶ Y) [Fibration p] (x₀₂ x₁₂ : Δ[1] ⟶ X)
    (h : stdSimplex.δ 0 ≫ x₀₂ = stdSimplex.δ 0 ≫ x₁₂)
    (hx : x₀₂ ≫ p = x₁₂ ≫ p) :
    ∃ (x₀₁ : Δ[1] ⟶ X) (b : Y _⦋0⦌),
      stdSimplex.δ 1 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₀₂ ∧
      stdSimplex.δ 0 ≫ x₀₁ = stdSimplex.δ 1 ≫ x₁₂ ∧
        x₀₁ ≫ p = const b := by
  obtain ⟨x₀₁, eq₁, eq₂, eq₃⟩ := exists_path_composition₂_above_of_fibration p x₀₂ x₁₂ h
    (stdSimplex.σ 0 ≫ x₀₂ ≫ p) (stdSimplex.{u}.δ_comp_σ_succ_assoc (n := 1) (i := 0) _) (by
      rw [← hx]
      apply stdSimplex.δ_comp_σ_self_assoc (n := 1) (i := 0))
  refine ⟨x₀₁, yonedaEquiv (stdSimplex.δ 1 ≫ x₀₂ ≫ p), eq₁, eq₂, ?_⟩
  have := stdSimplex.{u}.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by simp)
  dsimp at this
  rw [eq₃, reassoc_of% this]
  have : stdSimplex.{u}.σ (0 : Fin 1) = const (yonedaEquiv (𝟙 _)) := by
    apply yonedaEquiv.injective
    ext i
    fin_cases i <;> rfl
  simp [this]
  rfl

lemma homotopy_extension_property₁ {E K L : SSet.{u}} (i : K ⟶ L) (p : E ⟶ B) [Fibration p]
    [Mono i]
    (hE : K ⊗ Δ[1] ⟶ E) (f : L ⟶ E) (h₁ : i ≫ f = ι₁ ≫ hE)
    (hB : L ⊗ Δ[1] ⟶ B) (h₂ : ι₁ ≫ hB = f ≫ p) (h₃ : i ▷ _ ≫ hB = hE ≫ p)  :
    ∃ ψ : L ⊗ Δ[1] ⟶ E, ι₁ ≫ ψ = f ∧ i ▷ _ ≫ ψ = hE ∧ ψ ≫ p = hB := by
  have h := IsPushout.of_hasPushout i ι₁
  let l : pushout i ι₁ ⟶ L ⊗ Δ[1] := pushout.desc ι₁ (i ▷ _) (by simp)
  have : anodyneExtensions l := anodyneExtensions.pushout_desc_ι₁_whiskerRight_mono i
  have := this.hasLeftLiftingProperty p
  obtain ⟨t, ht₁, ht₂⟩ := h.exists_desc _ _ h₁
  have sq : CommSq t l p hB := ⟨by aesop⟩
  refine ⟨sq.lift, ?_, ?_, ?_⟩
  · rw [← ht₁]
    conv_rhs => rw [← sq.fac_left, pushout.inl_desc_assoc]
  · rw [← ht₂]
    conv_rhs => rw [← sq.fac_left, pushout.inr_desc_assoc]
  · exact sq.fac_right

lemma homotopy_extension_property₀ {E K L : SSet.{u}} (i : K ⟶ L) (p : E ⟶ B) [Fibration p]
    [Mono i]
    (hE : K ⊗ Δ[1] ⟶ E) (f : L ⟶ E) (h₁ : i ≫ f = ι₀ ≫ hE)
    (hB : L ⊗ Δ[1] ⟶ B) (h₂ : ι₀ ≫ hB = f ≫ p) (h₃ : i ▷ _ ≫ hB = hE ≫ p)  :
    ∃ ψ : L ⊗ Δ[1] ⟶ E, ι₀ ≫ ψ = f ∧ i ▷ _ ≫ ψ = hE ∧ ψ ≫ p = hB := by
  have h := IsPushout.of_hasPushout i ι₀
  let l : pushout i ι₀ ⟶ L ⊗ Δ[1] := pushout.desc ι₀ (i ▷ _) (by simp)
  have : anodyneExtensions l := anodyneExtensions.pushout_desc_ι₀_whiskerRight_mono i
  have := this.hasLeftLiftingProperty p
  obtain ⟨t, ht₁, ht₂⟩ := h.exists_desc _ _ h₁
  have sq : CommSq t l p hB := ⟨by aesop⟩
  refine ⟨sq.lift, ?_, ?_, ?_⟩
  · rw [← ht₁]
    conv_rhs => rw [← sq.fac_left, pushout.inl_desc_assoc]
  · rw [← ht₂]
    conv_rhs => rw [← sq.fac_left, pushout.inr_desc_assoc]
  · exact sq.fac_right

end SSet
