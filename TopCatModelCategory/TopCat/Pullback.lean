import TopCatModelCategory.PullbackTypes
import TopCatModelCategory.Pullback
import TopCatModelCategory.Convenient.GrothendieckTopology
import TopCatModelCategory.Convenient.Open
import TopCatModelCategory.Convenient.Colimits
import TopCatModelCategory.TopCat.Colimits

universe w' w t' t v u

open CategoryTheory Topology Limits

namespace TopCat

variable {X : Type u} [TopologicalSpace X]

section

variable (U : Set X)

@[simps]
def overPullbackSet : Over (of X) ⥤ Over (of U) where
  obj Z := Over.mk (Y := of (Z.hom ⁻¹' U)) (ofHom ⟨fun z ↦ ⟨Z.hom z, z.2⟩, by continuity⟩)
  map {Z₁ Z₂} f :=
    Over.homMk (ofHom ⟨fun z ↦ ⟨f.left z.1, by simpa only [← Over.w f] using z.2⟩,
      by continuity⟩) (by
        ext
        dsimp
        simp only [← Over.w f]
        rfl)

@[simps]
def overPullbackSetι : overPullbackSet U ⋙ Over.forget _ ⟶ Over.forget _ where
  app Z := ofHom ⟨fun z ↦ z.1, by continuity⟩

lemma overPullbackSet_isPullback (Z : Over (of X)) :
    IsPullback ((overPullbackSetι U).app Z) ((overPullbackSet U).obj Z).hom
      Z.hom (ofHom ⟨fun u ↦ u.1, by continuity⟩) :=
  isPullbackRestrictPreimage _ _

noncomputable def overPullbackSetIso :
    overPullbackSet U ≅ Over.pullback (ofHom ⟨fun u ↦ u.1, by continuity⟩) :=
  NatIso.ofComponents (fun Z ↦
    Over.isoMk (IsPullback.isoIsPullback _ _ (overPullbackSet_isPullback U Z)
      (IsPullback.of_hasPullback _ _))) (fun {Z₁ Z₂} f ↦ by
        ext : 1
        dsimp
        ext : 1
        · aesop
        · simp only [Category.assoc, IsPullback.isoIsPullback_hom_snd, limit.lift_π,
            PullbackCone.mk_pt, PullbackCone.mk_π_app, ← Over.w f]
          rfl)

def overPullbackSetForgetIso :
    overPullbackSet U ⋙ Over.forget _ ⋙ forget _ ≅
      Over.post (forget _) ⋙
        Types.overPullback (fun u => u.1) ⋙ Over.forget (U : Type _) :=
  Iso.symm (NatIso.ofComponents (fun Z ↦ Equiv.toIso
    { toFun x := ⟨x.1.1, by
        have := x.2
        dsimp at this
        simp [this]⟩
      invFun x := ⟨⟨x.1, Z.hom x.1, x.2⟩, rfl⟩
      left_inv x := by
        dsimp
        ext
        · rfl
        · exact x.2
      right_inv _ := rfl }))

end

instance {J : Type t} [Category.{w} J] (U : TopologicalSpace.Opens X) :
    PreservesColimitsOfShape J (overPullbackSet U.1) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨by
    apply isColimitOfReflects (Over.forget _)
    apply Nonempty.some
    rw [TopCat.nonempty_isColimit_iff]
    refine ⟨⟨?_⟩, ?_⟩
    · refine (IsColimit.equivOfNatIsoOfIso
        (Functor.isoWhiskerLeft K (overPullbackSetForgetIso U.1)) _ _ ?_).2
        (isColimitOfPreserves (Over.post (forget _) ⋙
          Types.overPullback (fun (u : U.1) ↦ u.1) ⋙ Over.forget _) hc)
      exact Iso.symm (Cocones.ext ((overPullbackSetForgetIso U.1).symm.app c.pt))
    · dsimp
      ext V
      let ι : (c.pt.hom) ⁻¹' U.1 → c.pt.left := Subtype.val
      obtain ⟨W, hW, rfl⟩ :
          ∃ (W : Set c.pt.left) (hW : W ⊆ (c.pt.hom) ⁻¹' U.1), V = ι ⁻¹' W :=
        ⟨ι '' V, by simp [ι], Set.preimage_val_image_val_eq_self.symm⟩
      have hU' : IsOpen ((c.pt.hom) ⁻¹' U.1) := IsOpen.preimage (by continuity) U.2
      rw [isOpen_iSup_iff, hU'.isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen,
        isOpen_iff_of_isColimit _ (isColimitOfPreserves (Over.forget _) hc)]
      refine forall_congr' (fun j ↦ ?_)
      dsimp
      conv_rhs => rw [isOpen_coinduced]
      rw [(IsOpen.preimage (by continuity) U.2).isOpenEmbedding_subtypeVal.isOpen_iff_image_isOpen]
      convert Iff.rfl
      ext x
      have := Over.w (c.ι.app j)
      dsimp at this
      simp [← ConcreteCategory.comp_apply, this]⟩⟩

instance {J : Type t} [Category.{w} J] (U : TopologicalSpace.Opens X) :
    PreservesColimitsOfShape J
      (Over.pullback (ofHom ⟨fun (u : U) ↦ u.1, by continuity⟩)) := by
  have : PreservesColimitsOfShape J (overPullbackSet U.1) := inferInstance
  exact preservesColimitsOfShape_of_natIso (overPullbackSetIso U.1)

lemma openImmersions.preservesColimitsOfShape_overPullback
    {X Y : TopCat.{u}} {f : X ⟶ Y} (hf : openImmersions f) (J : Type t) [Category.{w} J] :
    PreservesColimitsOfShape J (Over.pullback f) := by
  obtain ⟨U, e, he⟩ := hf.exists_iso
  let e' : Arrow.mk f ≅ Arrow.mk (ofHom ⟨fun (u : U) ↦ u.1, by continuity⟩) :=
    Arrow.isoMk e (Iso.refl _)
  have : PreservesColimitsOfShape J
    (Over.pullback (ofHom ⟨fun (u : U) ↦ u.1, by continuity⟩)) := inferInstance
  exact preservesColimitsOfShape_of_natIso (Over.pullbackIsoOfArrowIso e'.symm).symm

end TopCat

namespace GeneratedByTopCat

variable {J : Type t} [Category.{v} J]
  {ι : Type w} {X : ι → Type t} [∀ i, TopologicalSpace (X i)]
  {Y Z : GeneratedByTopCat.{v} X} {f : Y ⟶ Z}
  [PreservesLimitsOfShape WalkingCospan (GeneratedByTopCat.toTopCat.{v} (X := X))]

lemma openImmersions.preservesColimitsOfShape_overPullback (hf : openImmersions f) :
    PreservesColimitsOfShape J (Over.pullback f) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨isColimitOfReflects (Over.post toTopCat) (by
    have := TopCat.openImmersions.preservesColimitsOfShape_overPullback hf J
    let e := Over.pullbackPostIso toTopCat f
    refine (IsColimit.equivOfNatIsoOfIso
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft K e) _ _ ?_).2
      (isColimitOfPreserves (Over.post toTopCat ⋙ Over.pullback (toTopCat.map f)) hc)
    refine Cocones.ext (e.app _) (fun j ↦ ?_)
    have := e.hom.naturality (c.ι.app j)
    dsimp at this
    simp [this])⟩⟩

end GeneratedByTopCat
