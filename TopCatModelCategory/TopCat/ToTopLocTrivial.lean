import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.SSet.FiniteInduction
import TopCatModelCategory.SSet.Pullback
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

lemma Limits.preservesColimits_comp_of_hasColimit {J C D E : Type*} [Category J] [Category C]
    [Category D] [Category E] (F : J ⥤ C) (G : C ⥤ D) (K : D ⥤ E)
    [PreservesColimit F (G ⋙ K)] [HasColimit F] [PreservesColimit F G] :
    PreservesColimit (F ⋙ G) K :=
  preservesColimit_of_preserves_colimit_cocone (isColimitOfPreserves G (colimit.isColimit F))
    (isColimitOfPreserves (G ⋙ K) (colimit.isColimit F))

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
    (hX : IsInitial X) : IsEmpty X := by
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
  rw [objectProprertyOverLocally_iff] at h₂ ⊢
  intro a
  obtain (⟨a₀, rfl⟩ | ⟨k, rfl, hk⟩) := Types.eq_or_eq_of_isPushout'
    (sq.map (DeltaGenerated'.toTopCat ⋙ forget _)) a
  · obtain ⟨V, i, hi, ha₀, hi'⟩ := h₂ a₀
    refine ⟨sorry, sorry, sorry, sorry, ?_⟩
    rw [objectPropertyOver_iff, Over.nonempty_over_trivialBundlesWithFiber_iff] at hi' ⊢
    sorry
  · dsimp at k hk ⊢
    let e : ((Set.range l.left)ᶜ : Set _) ≃ₜ ((Set.range X₂.hom)ᶜ : Set _) :=
      TopCat.homeoComplOfIsPushoutOfIsClosedEmbedding
        (sq.map (DeltaGenerated'.toTopCat)).flip hl
    have hr : IsOpen ((Set.range X₂.hom)ᶜ) :=
      TopCat.closedEmbeddings.isOpen
        (TopCat.isClosedEmbedding_of_isPushout
          (sq.flip.map (DeltaGenerated'.toTopCat)) hl)
    have : DeltaGeneratedSpace' ((Set.range l.left)ᶜ : Set _) :=
      IsOpen.isGeneratedBy _ (by simpa only [isOpen_compl_iff] using hl.isClosed_range)
    exact ⟨Over.mk (Y := .of ((Set.range l.left)ᶜ : Set _))
      (TopCat.ofHom (ContinuousMap.comp ⟨_, continuous_subtype_val⟩ ⟨_, e.continuous⟩)),
      Over.homMk (TopCat.ofHom ⟨fun ⟨x, _⟩ ↦ X₃.hom x, by continuity⟩),
      (IsOpenEmbedding.comp (IsOpen.isOpenEmbedding_subtypeVal hr) e.isOpenEmbedding :),
      ⟨⟨k, hk⟩, rfl⟩, h₃.precomp (Over.homMk (TopCat.ofHom ⟨_, continuous_subtype_val⟩))⟩

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

include τ  in
lemma isLocTrivial {Z : SSet.{u}} [IsFinite Z] (a : Z ⟶ B) :
   ((trivialBundlesWithFiber (toDeltaGenerated.obj F)).objectPropertyOver
    (toDeltaGenerated.map p)).overLocally grothendieckTopology
    (Over.mk (toDeltaGenerated.map a)) := by
  induction Z using SSet.finite_induction with
  | hP₀ X =>
    rw [objectProprertyOverLocally_iff]
    have : IsEmpty (toDeltaGenerated.obj X) :=
      DeltaGenerated'.isEmpty_of_isInitial
        (IsInitial.isInitialObj _ _ (SSet.isInitialOfNotNonempty
            (by rwa [SSet.notNonempty_iff_hasDimensionLT_zero])))
    dsimp
    intro x
    exact (IsEmpty.false x).elim
  | @hP Z₀ Z i n j₀ j sq _ h₀ =>
    let Y₁ := Over.mk (j₀ ≫ i ≫ a)
    let Y₂ := Over.mk (i ≫ a)
    let Y₃ := Over.mk (j ≫ a)
    let Y₄ := Over.mk a
    let t' : Y₁ ⟶ Y₂ := Over.homMk j₀
    let l' : Y₁ ⟶ Y₃ := Over.homMk ∂Δ[n].ι (by simp [Y₁, Y₃, sq.w_assoc])
    let r' : Y₂ ⟶ Y₄ := Over.homMk i
    let b' : Y₃ ⟶ Y₄ := Over.homMk j
    have : Mono l'.left := by dsimp [l']; infer_instance
    have sq' : IsPushout t' l' r' b' := by rwa [Over.isPushout_iff_forget]
    have : PreservesColimit (span t' l') (Over.post toDeltaGenerated ⋙
      CategoryTheory.Over.pullback (toDeltaGenerated.map p) ⋙
        Over.forget (toDeltaGenerated.obj E)) :=
      preservesColimit_of_natIso _
        (Functor.isoWhiskerRight (Over.pullbackPostIso toDeltaGenerated p) (Over.forget _))
    have := preservesColimits_comp_of_hasColimit (span t' l') (Over.post toDeltaGenerated)
      (CategoryTheory.Over.pullback (toDeltaGenerated.map p) ⋙
        Over.forget (toDeltaGenerated.obj E))
    have : PreservesColimit (span ((Over.post toDeltaGenerated).map t')
      ((Over.post toDeltaGenerated).map l'))
      (CategoryTheory.Over.pullback (toDeltaGenerated.map p) ⋙
        Over.forget (toDeltaGenerated.obj E)) :=
      preservesColimit_of_iso_diagram _ (spanCompIso (Over.post toDeltaGenerated) t' l')
    have : PreservesColimit (span ((Over.post toDeltaGenerated).map t')
        ((Over.post toDeltaGenerated).map l'))
        (CategoryTheory.Over.pullback (toDeltaGenerated.map p)) :=
        preservesColimit_of_reflects_of_preserves _ (Over.forget _)
    refine DeltaGenerated'.trivialBundlesWithFiber_overLocally_of_isPushout
      (sq'.map (Over.post toDeltaGenerated)) (closedEmbeddings_toObj_map_of_mono _) _ (h₀ _) ?_
      (U := sorry) sorry sorry sorry sorry sorry sorry
    · rw [objectPropertyOver_iff,
        Over.nonempty_over_trivialBundlesWithFiber_iff]
      exact ⟨(τ (j ≫ a)).map (SSet.toDeltaGenerated)⟩

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
