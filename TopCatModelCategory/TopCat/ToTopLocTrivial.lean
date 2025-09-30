import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.SSet.FiniteInduction
import TopCatModelCategory.SSet.Pullback
import TopCatModelCategory.TrivialBundleOver
import TopCatModelCategory.TopCat.SerreFibrationBundle
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.TopCat.ToTopExact
import TopCatModelCategory.TopCat.Pullback
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

set_option maxHeartbeats 600000 in
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
  · obtain ⟨V₀, i, hi, ha₀, hi'⟩ := h₂ a₀
    obtain ⟨V, V₁, V₂, V₃, hV₂, hV₂', hV₁, hV₃, hV₃'⟩ :
      ∃ (V : TopologicalSpace.Opens B) (V₁ : TopologicalSpace.Opens X₁.left)
        (V₂ : TopologicalSpace.Opens X₂.left) (V₃ : TopologicalSpace.Opens U),
        V₂.1 = Set.range i.left ∧ X₂.hom ⁻¹' V.1 = V₂.1 ∧ t.left ⁻¹' V₂.1 = V₁.1 ∧
        V₃.1 = ρ ⁻¹' V₁.1 ∧ X₃.hom ⁻¹' V.1 = Set.image j V₃.1 := sorry
    let W : Over B := Over.mk (Y := .of V) (TopCat.ofHom ⟨_, continuous_subtype_val⟩)
    have hW : openImmersions W.hom := V.isOpen.isOpenEmbedding_subtypeVal
    have := hW.preservesColimitsOfShape_overPullback (J := WalkingSpan)
    refine ⟨W, Over.homMk W.hom, hW, ?_, ?_⟩
    · rw [← hV₂, ← hV₂'] at ha₀
      dsimp [W] at ha₀ ⊢
      simp only [Set.mem_range, Subtype.exists]
      simp only [Set.mem_preimage, SetLike.mem_coe] at ha₀
      exact ⟨_, ha₀, rfl⟩
    · let r : X₂ ⟶ Over.mk (𝟙 B) := Over.homMk X₂.hom
      let b : X₃ ⟶ Over.mk (𝟙 B) := Over.homMk X₃.hom
      have sq : IsPushout t l r b := by rwa [Over.isPushout_iff_forget]
      have : IsSplitMono ((CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom).map l).left := by
        let k : (GeneratedByTopCat.of V₃ : DeltaGenerated') ⟶ X₃.left :=
          TopCat.ofHom ⟨_, continuous_subtype_val⟩ ≫ j
        have hk : openImmersions k :=
          MorphismProperty.comp_mem _ _ _ (V₃.isOpen.isOpenEmbedding_subtypeVal) hj
        let α : (GeneratedByTopCat.of V₁ : DeltaGenerated') ⟶ X₃.left :=
          TopCat.ofHom ⟨_, continuous_subtype_val⟩ ≫ l.left
        obtain ⟨φ, hφ⟩ := hk.exists_lift α (by
            rintro _ ⟨a, rfl⟩
            refine ⟨⟨l' a.1, ?_⟩, ConcreteCategory.congr_hom fac a.1⟩
            change l' a.1 ∈ V₃.carrier
            rw [hV₃]
            have : ρ (l' a.1) = a.1 := ConcreteCategory.congr_hom fac' a.1
            simp only [TopologicalSpace.Opens.carrier_eq_coe, Set.mem_preimage, SetLike.mem_coe,
              this, SetLike.coe_mem])
        have : IsSplitMono φ := ⟨⟨{
          retraction := TopCat.ofHom ⟨fun x ↦ ⟨ρ x.1, by
            obtain ⟨x, (hx : x ∈ V₃.carrier)⟩ := x
            rwa [hV₃] at hx⟩, by continuity⟩
          id := by
            ext ⟨v, hv⟩ : 3
            have : (φ ⟨v, hv⟩).1 = l' v := hj.injective (by
              change (φ ≫ k) ⟨v, hv⟩ = _
              simp only [hφ, α, ← fac]
              rfl)
            change ρ (φ ⟨v, hv⟩).1 = v
            rw [this]
            exact ConcreteCategory.congr_hom fac' v
            }⟩⟩
        let ιV₁ : GeneratedByTopCat.of V₁ ⟶ X₁.left := TopCat.ofHom ⟨_, continuous_subtype_val⟩
        let pV₁ : GeneratedByTopCat.of V₁ ⟶ W.left :=
          TopCat.ofHom ⟨fun ⟨v, (hv : v ∈ V₁.carrier)⟩ ↦ ⟨X₁.hom v, by
            rw [← hV₁, ← hV₂', ← Set.preimage_comp] at hv
            dsimp at hv
            rwa [← CategoryTheory.hom_comp, Over.w t] at hv⟩, by continuity⟩
        let ιV₃ : GeneratedByTopCat.of V₃ ⟶ X₃.left :=
          TopCat.ofHom ⟨_, continuous_subtype_val⟩ ≫ j
        let pV₃ : GeneratedByTopCat.of V₃ ⟶ W.left :=
          TopCat.ofHom ⟨fun ⟨v, hv⟩ ↦ ⟨X₃.hom (j v), by
            dsimp
            erw [← Set.mem_preimage, hV₃']
            exact Set.mem_image_of_mem _ hv⟩, by continuity⟩
        have facι : ιV₁ ≫ l.left = φ ≫ ιV₃ := hφ.symm
        have facp : pV₁ = φ ≫ pV₃ := by
          ext ⟨x, hx⟩
          rw [Subtype.ext_iff]
          dsimp [pV₁, pV₃]
          change X₁.hom x = X₃.hom ((φ ≫ k) ⟨x, hx⟩)
          rw [hφ, ← Over.w l]
          rfl
        have sq₁ : IsPullback ιV₁ pV₁ X₁.hom W.hom := by
          apply openImmersions.isPullback
          · exact V₁.isOpen.isOpenEmbedding_subtypeVal
          · exact hW
          · rfl
          · rintro x hx
            simp only [Functor.const_obj_obj, Set.mem_preimage, Set.mem_range] at hx
            obtain ⟨y, hy⟩ := hx
            refine ⟨⟨x, ?_⟩, rfl⟩
            change x ∈ V₁.1
            rw [← hV₁, ← hV₂', ← Set.preimage_comp]
            dsimp
            rw [← CategoryTheory.hom_comp, Over.w t]
            simp only [Set.mem_preimage, SetLike.mem_coe]
            rw [← hy]
            exact y.2
        have sq₃ : IsPullback ιV₃ pV₃ X₃.hom W.hom := by
          apply openImmersions.isPullback
          · exact MorphismProperty.comp_mem _ _ _ (V₃.isOpen.isOpenEmbedding_subtypeVal) hj
          · exact hW
          · rfl
          · rintro x ⟨y, hy⟩
            have hx : x ∈ j '' V₃ := by
              dsimp at hV₃'
              rw [← hV₃']
              simp only [Set.mem_preimage, SetLike.mem_coe]
              erw [← hy]
              exact y.2
            obtain ⟨z, hz, rfl⟩ := hx
            exact ⟨⟨z, hz⟩, rfl⟩
        let e₁ : GeneratedByTopCat.of V₁ ≅ pullback X₁.hom W.hom := sq₁.isoPullback
        let e₃ : GeneratedByTopCat.of V₃ ≅ pullback X₃.hom W.hom := sq₃.isoPullback
        have : ((CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom).map l).left =
            e₁.inv ≫ φ ≫ e₃.hom := by
          rw [← cancel_epi e₁.hom, e₁.hom_inv_id_assoc]
          apply pullback.hom_ext
          · simp [e₁, e₃, facι]
          · simp [e₁, e₃, facp]
        rw [this]
        infer_instance
      have : PreservesColimit (span t l)
        ((CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom) ⋙
          CategoryTheory.Over.pullback p) := by
        let W' := (CategoryTheory.Over.pullback p).obj W
        have hW' : openImmersions W'.hom :=
          MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hW
        have := hW'.preservesColimitsOfShape_overPullback (J := WalkingSpan)
        have e : (CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom) ⋙
          CategoryTheory.Over.pullback p ≅
            CategoryTheory.Over.pullback p ⋙ CategoryTheory.Over.pullback W'.hom ⋙
              Over.map W'.hom :=
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft _
              (Over.mapCompPullbackIsoOfIsPullback (IsPullback.of_hasPullback W.hom p).flip) ≪≫
              (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
                ((Over.pullbackComp _ _).symm ≪≫ eqToIso (by
                  congr 1; exact pullback.condition) ≪≫ Over.pullbackComp _ _) _ ≪≫
                Functor.associator _ _ _
        exact preservesColimit_of_natIso _ e.symm
      have : PreservesColimit
          (span t l ⋙ (CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom))
          (CategoryTheory.Over.pullback p) :=
        preservesColimits_comp_of_hasColimit (span t l) _ _
      have : PreservesColimit
          (span ((CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom).map t)
            ((CategoryTheory.Over.pullback W.hom ⋙ Over.map W.hom).map l))
          (CategoryTheory.Over.pullback p) :=
        preservesColimit_of_iso_diagram _ (spanCompIso _ t l)
      have := TrivialBundleWithFiberOver.nonempty_of_isPushout_of_isSplitMono
        (sq.map (Over.pullback W.hom ⋙ Over.map W.hom)) p (F := F) (Nonempty.some (by
          rw [← Over.nonempty_over_trivialBundlesWithFiber_iff, ← objectPropertyOver_iff]
          refine ObjectProperty.of_precomp _ (Over.homMk (hi.lift (pullback.fst _ _) ?_) ?_) hi'
          · rw [← hV₂, ← hV₂']
            rintro _ ⟨b, rfl⟩
            dsimp at b ⊢
            simp only [Set.mem_preimage, SetLike.mem_coe]
            convert (pullback.snd X₂.hom W.hom b).2
            exact congr_fun ((forget _).congr_map
              (pullback.condition (f := X₂.hom) (g := W.hom))) b
          · dsimp
            rw [← Over.w i, hi.lift_comp_assoc, pullback.condition])) (Nonempty.some (by
          rw [← Over.nonempty_over_trivialBundlesWithFiber_iff, ← objectPropertyOver_iff]
          exact ObjectProperty.of_precomp _
            (Over.homMk (pullback.fst _ _) (by simp [pullback.condition])) h₃))
      rw [← Over.nonempty_over_trivialBundlesWithFiber_iff, ← objectPropertyOver_iff] at this
      exact ObjectProperty.of_precomp _ (by exact Over.homMk (pullback.lift W.hom (𝟙 _))) this
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
      (U := ?_) ?_ ?_ ?_ ?_ ?_ ?_
    · rw [objectPropertyOver_iff,
        Over.nonempty_over_trivialBundlesWithFiber_iff]
      exact ⟨(τ (j ≫ a)).map (SSet.toDeltaGenerated)⟩
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry

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
