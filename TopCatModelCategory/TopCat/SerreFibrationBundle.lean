module

public import TopCatModelCategory.TopCat.SerreFibrationLocal
public import TopCatModelCategory.Convenient.GrothendieckTopology
public import TopCatModelCategory.Convenient.Fibrations
public import TopCatModelCategory.MorphismPropertyLocally
public import TopCatModelCategory.TrivialBundleGluing

@[expose] public section

universe u

open CategoryTheory HomotopicalAlgebra TopCat.modelCategory Limits
  MorphismProperty MonoidalCategory CartesianMonoidalCategory

namespace DeltaGenerated'

variable {E B : DeltaGenerated'.{u}} {p : E ⟶ B}

lemma fibration_toTopCat_map_of_locallyTarget
    (hp : ((fibrations TopCat).inverseImage toTopCat).locallyTarget
      GeneratedByTopCat.grothendieckTopology p) : Fibration (toTopCat.map p) := by
  obtain ⟨c, hc⟩ := hp
  have h (i : c.ι) := (c.hp i).exists_iso
  choose V e fac using h
  have hV : TopologicalSpace.IsOpenCover V := .mk (by
    ext b
    simp only [ObjectProperty.ι_obj, TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion,
      SetLike.mem_coe, TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    obtain ⟨i, u, rfl⟩ := c.exists_eq b
    refine ⟨i, ?_⟩
    rw [← fac]
    exact ((e i).hom u).2)
  refine TopCat.fibration_of_isOpenCover hV (fun i ↦ ?_)
  rw [TopCat.IsSerreFibrationOver.iff_fibration]
  let W : DeltaGenerated' := GeneratedByTopCat.of (V i)
  let j : W ⟶ B := TopCat.ofHom ⟨_, continuous_subtype_val⟩
  have hπ : c.sieve j := by
    let e' : c.U i ≅ W := fullyFaithfulToTopCat.preimageIso (e i)
    convert c.sieve.downward_closed (Sieve.ofArrows_mk _ _ _) e'.inv
    rw [← cancel_epi e'.hom, e'.hom_inv_id_assoc]
    exact fac i
  replace hπ := hc _ hπ
  rw [mem_sieveLocallyTarget_iff] at hπ
  obtain ⟨hπ⟩ := hπ
  have : Limits.PreservesLimit (Limits.cospan j p) toTopCat :=
    GeneratedByTopCat.openImmersions.preservesLimit_cospan
      (by exact ((V i).isOpen.isOpenEmbedding_subtypeVal)) _
  obtain ⟨iso, h₁, h₂⟩ := IsPullback.exists_iso_of_isos (hπ.sq.flip.map (toTopCat))
    (TopCat.isPullbackRestrictPreimage (toTopCat.map p) (V i)).flip
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp)
  dsimp at h₁ h₂
  rw [Category.comp_id] at h₁ h₂
  have := hπ.hl
  rw [fibration_iff]
  exact (arrow_mk_iso_iff _ (Arrow.isoMk iso (Iso.refl _))).1 hπ.hl

open MorphismProperty

instance (F : TopCat.{u}) (p : F ⟶ 𝟙_ TopCat) : Fibration p := by
  rw [← isFibrant_iff_of_isTerminal _ isTerminalTensorUnit]
  infer_instance

instance (S F : TopCat.{u}) : Fibration (fst S F) := by
  rw [fibration_iff]
  refine of_isPullback (IsPullback.of_isLimit_binaryFan_of_isTerminal
    (tensorProductIsBinaryProduct S F) isTerminalTensorUnit).flip ?_
  rw [← fibration_iff]
  infer_instance

def arrowIsoToTopCatFst (S F : DeltaGenerated'.{u}) :
    Arrow.mk (TopCat.toDeltaGenerated'.map (fst (toTopCat.obj S) (toTopCat.obj F))) ≅
      Arrow.mk (fst S F) :=
  Iso.symm (Arrow.isoMk (Iso.refl _) (adjUnitIso.app _))

instance (S F : DeltaGenerated'.{u}) :
    Fibration (toTopCat.map (fst S F)) := by
  have h : Fibration (fst (toTopCat.obj S) (toTopCat.obj F)) := inferInstance
  rw [← fibration_toTopCat_map_toDeltaGenerated'_map_iff] at h
  rw [fibration_iff] at h ⊢
  refine (((fibrations TopCat).inverseImage toTopCat).arrow_mk_iso_iff ?_).2 h
  exact Arrow.isoMk (Iso.refl _) (adjUnitIso.app _)

lemma fibration_toTopCat_map_of_locallyTarget_trivialBundle
    (hp : (trivialBundles.locallyTarget GeneratedByTopCat.grothendieckTopology p)) :
      Fibration (toTopCat.map p) := by
  apply fibration_toTopCat_map_of_locallyTarget
  refine locallyTarget_monotone ?_ _ _ hp
  intro X S f hf
  rw [mem_trivialBundles_iff] at hf
  obtain ⟨F, ⟨hf⟩⟩ := hf
  let e : Arrow.mk f ≅ Arrow.mk (fst S F) := Arrow.isoMk hf.isoTensor (Iso.refl _)
  refine (((fibrations TopCat).inverseImage toTopCat).arrow_iso_iff e).2 ?_
  dsimp
  simp only [inverseImage_iff, ← fibration_iff]
  infer_instance

end DeltaGenerated'
