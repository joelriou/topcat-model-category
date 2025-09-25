import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.SSet.FiniteInduction
import TopCatModelCategory.TrivialBundleOver
import TopCatModelCategory.TopCat.SerreFibrationBundle
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.TopCat.ToTopExact
import TopCatModelCategory.ModelCategoryTopCat
import TopCatModelCategory.Pullback

universe u

open Simplicial CategoryTheory MorphismProperty HomotopicalAlgebra
  TopCat.modelCategory Limits Topology GeneratedByTopCat

namespace CategoryTheory

lemma Limits.PushoutCocone.isPushout_iff_nonempty_isColimit
    {C : Type*} [Category C]
    {S T₁ T₂ : C} {f₁ : S ⟶ T₁} {f₂ : S ⟶ T₂}
    (c : PushoutCocone f₁ f₂) :
    IsPushout f₁ f₂ c.inl c.inr ↔ Nonempty (IsColimit c) :=
  ⟨fun sq ↦ ⟨IsColimit.ofIsoColimit sq.isColimit (PushoutCocone.ext (Iso.refl _))⟩, fun h ↦
    { w := c.condition
      isColimit' := ⟨IsColimit.ofIsoColimit h.some (PushoutCocone.ext (Iso.refl _))⟩ }⟩

namespace Over

variable {C : Type*} [Category C] {B : C} {X₁ X₂ X₃ X₄ : Over B}
  {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

lemma isPushout_iff_forget [HasPushouts C] :
    IsPushout t l r b ↔ IsPushout t.left l.left r.left b.left :=
  ⟨fun sq ↦ sq.map (Over.forget _), fun sq ↦
    { w := by ext; exact sq.w
      isColimit' := ⟨by
        refine PushoutCocone.IsColimit.mk _
          (fun s ↦ Over.homMk (sq.desc s.inl.left s.inr.left
            ((Over.forget _).congr_map s.condition)) (by apply sq.hom_ext <;> simp))
          (by aesop) (by aesop) (fun s m h₁ h₂ ↦ ?_)
        ext
        apply sq.hom_ext
        · simp [← h₁]
        · simp [← h₂]⟩ }⟩

instance {D : Type*} [Category D] [HasPushouts C] [HasPushouts D]
    (F : C ⥤ D) [PreservesColimitsOfShape WalkingSpan F] (X : C) :
    PreservesColimitsOfShape WalkingSpan (Over.post (X := X) F) := by
  suffices ∀ {S T₁ T₂ : Over X} (f₁ : S ⟶ T₁) (f₂ : S ⟶ T₂),
      PreservesColimit (span f₁ f₂) (Over.post (X := X) F) from
    ⟨fun {K} ↦ preservesColimit_of_iso_diagram _ (diagramIsoSpan K).symm⟩
  intro S T₁ T₂ f₁ f₂
  constructor
  intro c hc
  refine ⟨(PushoutCocone.isColimitMapCoconeEquiv _ _).2
    (((PushoutCocone.isPushout_iff_nonempty_isColimit _).1 ?_).some)⟩
  rw [isPushout_iff_forget]
  exact (PushoutCocone.isPushout_iff_nonempty_isColimit _).2
    ⟨(PushoutCocone.isColimitMapCoconeEquiv _ _).1
      (isColimitOfPreserves (Over.forget _ ⋙ F) hc)⟩

instance {X Y : C} (f : X ⟶ Y) [HasPushouts C] :
    PreservesColimitsOfShape WalkingSpan (Over.map f) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨by
    have := isColimitOfPreserves (Over.forget _ ) hc
    exact isColimitOfReflects (Over.forget _) this
    ⟩⟩

end Over

end CategoryTheory

def DeltaGenerated'.isLimitBinaryFanOfIsEmpty
    {X Y : DeltaGenerated'.{u}} {c : BinaryFan X Y}
    (hX : IsEmpty ((forget _).obj X)) (_ : IsEmpty ((forget _).obj c.pt)) :
    IsLimit c :=
  have h {T : DeltaGenerated'.{u}} (f : T ⟶ X) (t : (forget _).obj T) : False := by
    have := Function.isEmpty ((forget _).map f)
    exact isEmptyElim (α := ((forget _).obj T)) t
  BinaryFan.IsLimit.mk _ (fun {T} f₁ _ ↦ TopCat.ofHom ⟨fun t ↦ (h f₁ t).elim, by
      rw [continuous_iff_continuousAt]
      intro t
      exact (h f₁ t).elim⟩)
    (fun f₁ _ ↦ by ext t; exact (h f₁ t).elim)
    (fun f₁ _ ↦ by ext t; exact (h f₁ t).elim)
    (fun f₁ _ _ _ _ ↦ by ext t; exact (h f₁ t).elim)

def DeltaGenerated'.isInitialOfIsEmpty (X : DeltaGenerated'.{u})
    [IsEmpty ((forget _).obj X)] :
    IsInitial X :=
  have h {T : DeltaGenerated'.{u}} (f : T ⟶ X) (t : (forget _).obj T) : False := by
    have := Function.isEmpty ((forget _).map f)
    exact isEmptyElim (α := ((forget _).obj T)) t
  IsInitial.ofUniqueHom
    (fun _ ↦ TopCat.ofHom ⟨fun (x : (forget _).obj X) ↦ isEmptyElim x, by
      rw [continuous_iff_continuousAt]
      intro (x : (forget _).obj X)
      exact isEmptyElim x⟩)
    (fun _ f ↦ by
      ext (x : (forget _).obj X)
      dsimp
      exact isEmptyElim x)

lemma DeltaGenerated'.isEmpty_of_isInitial {X : DeltaGenerated'.{u}}
    (hX : IsInitial X) : IsEmpty ((forget _).obj X) := by
  let f : X ⟶ GeneratedByTopCat.of PEmpty := hX.to _
  exact Function.isEmpty f

namespace DeltaGenerated'

lemma trivialBundlesWithFiber_overLocally_of_isPushout'
    {E B F : DeltaGenerated'.{u}} {X₁ X₂ X₃ : Over B} {t : X₁ ⟶ X₂}
    {l : X₁ ⟶ X₃} (sq : IsPushout t.left l.left X₂.hom X₃.hom)
    (hl : TopCat.closedEmbeddings (toTopCat.map l.left)) (p : E ⟶ B)
    [PreservesColimit (span t l) (Over.pullback p)]
    (h₂ : ((trivialBundlesWithFiber F).objectPropertyOver p).overLocally grothendieckTopology X₂)
    (h₃ : (trivialBundlesWithFiber F).objectPropertyOver p X₃)
    {U : DeltaGenerated'.{u}} (j : U ⟶ X₃.left) (hj : openImmersions j)
    (l' : X₁.left ⟶ U) (fac : l' ≫ j = l.left) (ρ : U ⟶ X₁.left) (fac' : l' ≫ ρ = 𝟙 _) :
    ((trivialBundlesWithFiber F).objectPropertyOver p).overLocally grothendieckTopology
      (Over.mk (𝟙 B)) := by
  sorry

lemma trivialBundlesWithFiber_overLocally_of_isPushout
    {E B F : DeltaGenerated'.{u}} {X₁ X₂ X₃ X₄ : Over B} {t : X₁ ⟶ X₂}
    {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPushout t l r b)
    (hl : TopCat.closedEmbeddings (toTopCat.map l.left)) (p : E ⟶ B)
    [PreservesColimit (span t l) (Over.pullback p)]
    (h₂ : ((trivialBundlesWithFiber F).objectPropertyOver p).overLocally grothendieckTopology X₂)
    (h₃ : (trivialBundlesWithFiber F).objectPropertyOver p X₃)
    {U : DeltaGenerated'.{u}} (j : U ⟶ X₃.left) (hj : openImmersions j)
    (l'' : X₁.left ⟶ U) (fac : l'' ≫ j = l.left) (ρ : U ⟶ X₁.left) (fac' : l'' ≫ ρ = 𝟙 _) :
    ((trivialBundlesWithFiber F).objectPropertyOver p).overLocally grothendieckTopology X₄ := by
  rw [Over.isPushout_iff_forget] at sq
  let Y₁ := Over.mk (t.left ≫ r.left)
  let Y₂ := Over.mk (r.left)
  let Y₃ := Over.mk (b.left)
  let t' : Y₁ ⟶ Y₂ := Over.homMk t.left
  let l' : Y₁ ⟶ Y₃ := Over.homMk l.left sq.w.symm
  let Z₄ := pullback p X₄.hom
  let p' : Z₄ ⟶ X₄.left := pullback.snd _ _
  have sq' : IsPullback (pullback.fst _ _) p' p X₄.hom := IsPullback.of_hasPullback _ _
  replace sq : IsPushout t'.left l'.left Y₂.hom Y₃.hom := sq
  have : PreservesColimit (span t' l' ⋙ Over.map X₄.hom)
      (CategoryTheory.Over.pullback p ⋙ Over.forget E) := by
    have e : (span t' l' ⋙ Over.map X₄.hom) ≅ span t l :=
      spanCompIso _ _ _ ≪≫ spanExt (by exact Over.isoMk (Iso.refl _))
        (by exact Over.isoMk (Iso.refl _)) (by exact Over.isoMk (Iso.refl _))
        (by ext : 1; simp [t']) (by ext : 1; simp [l'])
    apply preservesColimit_of_iso_diagram _ e.symm
  have : PreservesColimit (span t' l') (CategoryTheory.Over.pullback p' ⋙ Over.forget _) :=
    preservesColimit_of_natIso _ (Over.pullbackCompForgetOfIsPullback sq').symm
  have : PreservesColimit (span t' l') (CategoryTheory.Over.pullback p') :=
    preservesColimit_of_reflects_of_preserves _ (Over.forget _)
  have := trivialBundlesWithFiber_overLocally_of_isPushout' sq hl p' (F := F) (by
    rw [← overLocally_objectPropertyOver_over_map_obj_iff _ _ sq']
    exact ObjectProperty.prop_of_iso _ (by exact Over.isoMk (Iso.refl _)) h₂) (by
    rw [objectPropertyOver_iff_map_of_isPullback _ sq']
    exact ObjectProperty.prop_of_iso _ (by exact Over.isoMk (Iso.refl _)) h₃)
    j hj l'' fac ρ fac'
  rw [← overLocally_objectPropertyOver_over_map_obj_iff _ _ sq'] at this
  exact ObjectProperty.prop_of_iso _ (Over.isoMk (Iso.refl _)) this

end DeltaGenerated'

namespace SSet

variable {E B : SSet.{u}} {p : E ⟶ B} {F : SSet.{u}}
  (τ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ)

namespace MinimalFibrationLocTrivial

section

noncomputable abbrev pull (_ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ) :=
    Over.pullback ((toDeltaGenerated.map p))

variable (A : Over (toDeltaGenerated.obj B))

noncomputable def pullObj : DeltaGenerated'.{u} := ((pull τ).obj A).left

noncomputable def ι : pullObj τ A ⟶ toDeltaGenerated.obj E := ((pull τ).obj A).hom

noncomputable def π : pullObj τ A ⟶ A.left := pullback.fst _ _

lemma isPullback : IsPullback (ι τ A) (π τ A) (toDeltaGenerated.map p) A.hom :=
  (IsPullback.of_hasPullback _ _).flip

variable (p F) in
def IsTrivial {A : DeltaGenerated'} (f : A ⟶ toDeltaGenerated.obj B) : Prop :=
  Nonempty (TrivialBundleWithFiberOver (toDeltaGenerated.obj F) (toDeltaGenerated.map p) f)

instance (X : Type u) [IsEmpty X] [TopologicalSpace X] [DeltaGeneratedSpace' X] :
    IsEmpty ((forget DeltaGenerated').obj (.of X)) := by assumption

lemma isTrivial_of_isEmpty (h : IsEmpty ((forget _).obj A.left)) :
    IsTrivial p F A.hom := by
  let φ := ((forget _).map (pullback.fst (X := A.left) A.hom (toDeltaGenerated.map p)))
  have := Function.isEmpty φ
  exact
    ⟨{sq := (IsPullback.of_hasPullback _ _).flip
      h :=
      { r := (DeltaGenerated'.isInitialOfIsEmpty _).to _
        isLimit :=DeltaGenerated'.isLimitBinaryFanOfIsEmpty h (by assumption) } }⟩

lemma isTrivial_of_fac {A' A : DeltaGenerated'} {f : A ⟶ toDeltaGenerated.obj B}
    (h : IsTrivial p F f) (j : A' ⟶ A)
    (f' : A' ⟶ toDeltaGenerated.obj B)
    (fac : j ≫ f = f')  :
    IsTrivial p F f' := by
  subst fac
  exact ⟨h.some.pullback' _⟩

def IsLocTrivial : Prop :=
  (trivialBundlesWithFiber (toDeltaGenerated.obj F)).locallyTarget
    GeneratedByTopCat.grothendieckTopology (π τ A)

variable (p F) in
def IsLocTrivialAt {A : DeltaGenerated'} (f : A ⟶ toDeltaGenerated.obj B) (a : A) : Prop :=
  ∃ (U : DeltaGenerated') (i : U ⟶ A)
        (_ : GeneratedByTopCat.openImmersions i) (_ : a ∈ Set.range i),
        IsTrivial p F (i ≫ f)

lemma isLocTrivial_iff :
    IsLocTrivial τ A ↔
      ∀ (a : A.left), IsLocTrivialAt p F A.hom a := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro a
    obtain ⟨C, hC⟩ := h
    obtain ⟨i, u, rfl⟩ := C.exists_eq a
    refine ⟨C.U i, C.p i, C.hp i, ⟨_, rfl⟩, ?_⟩
    have hi := hC (C.p i) (Sieve.ofArrows_mk _ _ _)
    rw [mem_sieveLocallyTarget_iff] at hi
    obtain ⟨hi⟩ := hi
    exact ⟨{
      E' := _
      p' := hi.l
      t := hi.t ≫ ι τ A
      sq := hi.sq.paste_horiz (isPullback τ A)
      h := hi.hl.some
    }⟩
  · choose U i hi hU' t using h
    refine ⟨{
      ι := A.left
      U := U
      p := i
      hp := hi }, ?_⟩
    simp only [Sieve.ofArrows_le_iff]
    intro a
    rw [mem_sieveLocallyTarget_iff]
    refine ⟨?_⟩
    have ip := (t a).some
    exact {
      obj := _
      t := _
      l := _
      sq := (IsPullback.of_hasPullback (i a) (π τ A)).flip
      hl := ⟨(t a).some.trivialBundleWithFiber
          ((IsPullback.of_hasPullback _ _).flip.paste_horiz (isPullback τ A))⟩ }

variable {τ A} in
lemma IsTrivial.isLocTrivial (hA : IsTrivial p F A.hom) : IsLocTrivial τ A :=
  MorphismProperty.le_locallyTarget _ _ _
    ⟨hA.some.trivialBundleWithFiber (IsPullback.of_hasPullback _ _).flip⟩

section

variable {Z : DeltaGenerated'.{u}} {t : Z ⟶ toDeltaGenerated.obj E}
    {l : Z ⟶ A.left} (sq : IsPullback t l (toDeltaGenerated.map p) A.hom)

include sq

noncomputable def objIso : pullObj τ A ≅ Z :=
  (IsPullback.exists_iso_of_isos (isPullback τ A) sq (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)).choose

@[reassoc (attr := simp)]
lemma objIso_hom_comp_eq_π : (objIso τ A sq).hom ≫ l = π τ A := by
  simpa using ((IsPullback.exists_iso_of_isos (isPullback τ A) sq (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)).choose_spec.2).symm

end

end

section

variable {A} {K₀ A₀ K : Over (toDeltaGenerated.obj B)}
  {t : K₀ ⟶ A₀} {l : K₀ ⟶ K} {r : A₀ ⟶ A} {b : K ⟶ A}
  (sq : IsPushout t l r b)

include sq

lemma isLocTrivial_of_isPushout
    (hl : TopCat.closedEmbeddings (DeltaGenerated'.toTopCat.map l.left))
    (hK : IsTrivial p F K.hom) (hA₀ : IsLocTrivial τ A₀)
    (hsq : PreservesColimit (span t l) (CategoryTheory.Over.pullback (toDeltaGenerated.map p)))
    {U : DeltaGenerated'.{u}} (i : U ⟶ K.left) (hi : GeneratedByTopCat.openImmersions i)
    (l' : K₀.left ⟶ U) (fac : l' ≫ i = l.left) (ρ : U ⟶ K₀.left) (fac' : l' ≫ ρ = 𝟙 _) :
    IsLocTrivial τ A := by
  rw [isLocTrivial_iff] at hA₀ ⊢
  intro a
  obtain (⟨a₀, rfl⟩ | ⟨k, rfl, hk⟩) := Types.eq_or_eq_of_isPushout'
    (sq.map (Over.forget _ ⋙ DeltaGenerated'.toTopCat ⋙ forget _)) a
  · dsimp at a₀
    dsimp
    sorry
  · dsimp at k hk ⊢
    let e : ((Set.range l.left)ᶜ : Set _) ≃ₜ ((Set.range r.left)ᶜ : Set _) :=
      TopCat.homeoComplOfIsPushoutOfIsClosedEmbedding
        (sq.map (Over.forget _ ⋙ DeltaGenerated'.toTopCat)).flip hl
    have hr : IsOpen ((Set.range r.left)ᶜ) :=
      TopCat.closedEmbeddings.isOpen
        (TopCat.isClosedEmbedding_of_isPushout
          (sq.flip.map (Over.forget _ ⋙ DeltaGenerated'.toTopCat)) hl)
    have : DeltaGeneratedSpace' ((Set.range l.left)ᶜ : Set _) :=
      IsOpen.isGeneratedBy _ (by simpa only [isOpen_compl_iff] using hl.isClosed_range)
    refine ⟨.of ((Set.range l.left)ᶜ : Set _),
      TopCat.ofHom (ContinuousMap.comp ⟨_, continuous_subtype_val⟩ ⟨_, e.continuous⟩),
      (IsOpenEmbedding.comp (IsOpen.isOpenEmbedding_subtypeVal hr) e.isOpenEmbedding :),
      ⟨⟨k, hk⟩, rfl⟩,
      isTrivial_of_fac hK (TopCat.ofHom ⟨_, continuous_subtype_val⟩) _
      (by rw [← Over.w b]; rfl)⟩

end

lemma isLocTrivial' {Z : SSet.{u}} [IsFinite Z] (a : Z ⟶ B) :
    IsLocTrivial τ (Over.mk (toDeltaGenerated.map a)) := by
  induction Z using SSet.finite_induction with
  | hP₀ X =>
    refine (isTrivial_of_isEmpty _
      (DeltaGenerated'.isEmpty_of_isInitial ?_)).isLocTrivial
    dsimp
    exact IsInitial.isInitialObj _ _ (SSet.isInitialOfNotNonempty
      (by rwa [SSet.notNonempty_iff_hasDimensionLT_zero]))
  | @hP Z₀ Z i n j j₀ sq _ h₀ =>
    let t : Over.mk (j ≫ i ≫ a) ⟶ Over.mk (i ≫ a) := Over.homMk j
    let b : Over.mk (j₀ ≫ a) ⟶ Over.mk a := Over.homMk j₀
    have sq' : IsPushout (Over.homMk j : Over.mk (j ≫ i ≫ a) ⟶ Over.mk (i ≫ a))
        (Over.homMk (Subcomplex.ι _) (by simp [sq.w_assoc]))
        (Over.homMk (by exact i)) (Over.homMk j₀ : Over.mk (j₀ ≫ a) ⟶ Over.mk a) := by
      rwa [Over.isPushout_iff_forget ]
    refine isLocTrivial_of_isPushout τ (sq'.map (Over.post (SSet.toDeltaGenerated)))
      ?_ ⟨(τ (j₀ ≫ a)).map toDeltaGenerated⟩ (h₀ _) ?_ (U := ?_) ?_ ?_ ?_ ?_ ?_ ?_
    · dsimp
      apply closedEmbeddings_toObj_map_of_mono
    · dsimp
      sorry
    -- the next goals are about taking the complement of the isobarycenter in the simplex
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

include τ  in
lemma isLocTrivial {Z : SSet.{u}} [IsFinite Z] (a : Z ⟶ B) :
   ((trivialBundlesWithFiber (toDeltaGenerated.obj F)).objectPropertyOver
    (toDeltaGenerated.map p)).overLocally grothendieckTopology
    (Over.mk (toDeltaGenerated.map a)) := by
  have := τ
  sorry

end MinimalFibrationLocTrivial

variable (p) in
open MinimalFibrationLocTrivial MorphismProperty in
include τ in
lemma fibration_toTop_map_of_trivialBundle_over_simplices [IsFinite B] :
    Fibration (toTop.map p) := by
  apply DeltaGenerated'.fibration_toTopCat_map_of_locallyTarget_trivialBundle
    (p := toDeltaGenerated.map p)
  apply locallyTarget_monotone (trivialBundlesWithFiber_le_trivialBundles (toDeltaGenerated.obj F))
  rw [← MorphismProperty.overLocally_objectPropertyOver_iff_locallyTarget _ _ _
    (Over.mk (𝟙 (toDeltaGenerated.obj B))) IsPullback.of_id_fst]
  simpa using isLocTrivial τ (𝟙 B)

end SSet
