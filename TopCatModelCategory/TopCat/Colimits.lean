import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

universe w v' u' u

open CategoryTheory Limits Topology

namespace TopCat

variable {J : Type u'} [Category.{v'} J] {F : J ⥤ TopCat.{u}}
  (c : Cocone F)

-- fixed in #28770
lemma continuous_iff_of_isColimit' (hc : IsColimit c)
    {X : Type w} [TopologicalSpace X] (f : c.pt → X) :
    Continuous f ↔ ∀ (j : J), Continuous (f ∘ c.ι.app j) := by
  simp only [continuous_def, isOpen_iff_of_isColimit _ hc]
  tauto

lemma nonempty_isColimit_iff :
    Nonempty (IsColimit c) ↔
      Nonempty (IsColimit ((forget _).mapCocone c)) ∧
        c.pt.str = ⨆ j, (F.obj j).str.coinduced (c.ι.app j) := by
  constructor
  · rintro ⟨hc⟩
    exact ⟨⟨isColimitOfPreserves _ hc⟩ , coinduced_of_isColimit _ hc⟩
  · rintro ⟨⟨hc⟩, hc'⟩
    exact ⟨IsColimit.ofIsoColimit (isColimitCoconeOfForget _ hc)
      (Cocones.ext (isoOfHomeo (Homeomorph.mk (.refl _) ⟨by aesop⟩
        ⟨by aesop⟩)) (by aesop))⟩

section

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} (t : X₁ ⟶ X₂) (l : X₁ ⟶ X₃)
  (r : X₂ ⟶ X₄) (b : X₃ ⟶ X₄)

lemma isPushout_iff :
    IsPushout t l r b ↔
      IsPushout ((forget _).map t) ((forget _).map l)
        ((forget _).map r) ((forget _).map b) ∧
        X₄.str = X₂.str.coinduced r ⊔ X₃.str.coinduced b := by
  wlog H : CommSq t l r b
  · constructor
    · intro h
      rwa [this] at h
      exact ⟨h.w⟩
    · intro h
      rwa [this]
      exact ⟨(forget _).map_injective h.1.w⟩
  let c := (PushoutCocone.mk _ _ H.w)
  have : X₂.str.coinduced r ⊔ X₃.str.coinduced b =
      ⨆ j, ((span t l).obj j).str.coinduced (c.ι.app j) := by
    apply le_antisymm
    · rw [sup_le_iff]
      let φ (j) : TopologicalSpace c.pt := ((span t l).obj j).str.coinduced (c.ι.app j)
      exact ⟨le_iSup φ .left, le_iSup φ .right⟩
    · rw [iSup_le_iff]
      rintro (_ | _ | _)
      · refine le_trans ?_ le_sup_left
        dsimp [c]
        rw [← coinduced_compose]
        apply coinduced_mono
        apply Continuous.coinduced_le
        continuity
      · apply le_sup_left
      · apply le_sup_right
  rw [this]
  trans Nonempty (IsColimit c)
  · exact ⟨fun h ↦ ⟨h.isColimit⟩, fun ⟨h⟩ ↦ { w := H.w, isColimit' := ⟨h⟩ }⟩
  · rw [nonempty_isColimit_iff]
    refine and_congr_left (fun _ ↦ ⟨fun ⟨h⟩ ↦
      { w := (forget _).congr_map H.w
        isColimit' := ⟨PushoutCocone.isColimitMapCoconeEquiv _ _ h⟩ },
      fun h ↦ ⟨(PushoutCocone.isColimitMapCoconeEquiv _ _).2 h.isColimit⟩⟩)

variable {t l r b}

lemma isOpen_iff_of_isPushout (h : IsPushout t l r b) (F : Set X₄) :
    IsOpen F ↔ IsOpen (r ⁻¹' F) ∧ IsOpen (b ⁻¹' F) := by
  rw [isPushout_iff] at h
  rw [h.2]
  rfl

lemma isClosed_iff_of_isPushout (h : IsPushout t l r b) (F : Set X₄) :
    IsClosed F ↔ IsClosed (r ⁻¹' F) ∧ IsClosed (b ⁻¹' F) := by
  simp only [← isOpen_compl_iff, isOpen_iff_of_isPushout h, Set.preimage_compl]

end

namespace IsColimit

variable {c} (hc : IsColimit c)

include hc

lemma isQuotientMap :
    IsQuotientMap (Y := c.pt) (fun (x : Σ (j : J), F.obj j) ↦ c.ι.app x.1 x.2) where
  surjective y := by
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget _) hc) y
    exact ⟨⟨j, x⟩, rfl⟩
  eq_coinduced := by
    ext U
    rw [isOpen_iff_of_isColimit _ hc, isOpen_coinduced, isOpen_sigma_iff]
    rfl

variable {T : Type w}

lemma funext {f g : c.pt → T}
    (h : ∀ (j : J), f.comp (c.ι.app j).hom = g.comp (c.ι.app j).hom) :
    f = g := by
  have hc' : ((Functor.coconeTypesEquiv _).symm ((forget TopCat).mapCocone c)).IsColimit :=
    (Functor.CoconeTypes.isColimit_iff _).2 ⟨isColimitOfPreserves (forget _) hc⟩
  ext x
  obtain ⟨j, y, rfl⟩ := hc'.ι_jointly_surjective x
  exact congr_fun (h j) y

variable [TopologicalSpace T]

lemma continuousMap_ext {f g : C(c.pt, T)}
    (h : ∀ (j : J), f.comp (c.ι.app j).hom = g.comp (c.ι.app j).hom) :
    f = g := by
  have : f.toFun = g.toFun :=
    funext hc (fun j ↦ by
      ext x
      exact DFunLike.congr_fun (h j) x)
  simpa using this

variable (φ : ∀ (j : J), C(F.obj j, T))
  (hφ : ∀ ⦃j j' : J⦄ (f : j ⟶ j'), (φ j').comp (F.map f).hom = φ j)

include hφ in
lemma existsUnique :
    ∃! (f : C(c.pt, T)), ∀ (j : J), f.comp (c.ι.app j).hom = φ j := by
  refine existsUnique_of_exists_of_unique ?_
    (fun _ _ hf hg ↦ continuousMap_ext hc (fun j ↦ by rw [hf, hg]))
  have hc' : ((Functor.coconeTypesEquiv _).symm ((forget TopCat).mapCocone c)).IsColimit :=
    (Functor.CoconeTypes.isColimit_iff _).2 ⟨isColimitOfPreserves (forget _) hc⟩
  let d : (F ⋙ forget TopCat).CoconeTypes :=
    { pt := T
      ι j := (φ j).toFun
      ι_naturality g := by
        ext x
        exact DFunLike.congr_fun (hφ g) x }
  obtain ⟨f : c.pt → T, hf⟩ := hc'.exists_desc d
  refine ⟨⟨f, ?_⟩, fun j ↦ by ext x; exact congr_fun (hf j) x⟩
  rw [continuous_iff_of_isColimit' _ hc]
  intro j
  have : f ∘ c.ι.app j = φ j := by
    ext x
    exact congr_fun (hf j) x
  rw [this]
  exact (φ j).continuous

noncomputable def descContinuousMap : C(c.pt, T) :=
  (existsUnique hc φ hφ).exists.choose

@[simp]
lemma descContinuousMap_comp_ι_app_hom (j : J) :
    (descContinuousMap hc φ hφ).comp (c.ι.app j).hom = φ j :=
  (existsUnique hc φ hφ).exists.choose_spec j

@[simp]
lemma descContinuousMap_apply (j : J) (x : F.obj j):
    (descContinuousMap hc φ hφ) (c.ι.app j x) = φ j x :=
  DFunLike.congr_fun (descContinuousMap_comp_ι_app_hom hc φ hφ j) x

end IsColimit

end TopCat
