import TopCatModelCategory.TopCat.SerreFibrationLocal
import TopCatModelCategory.Convenient.GrothendieckTopology
import TopCatModelCategory.Convenient.Fibrations
import TopCatModelCategory.MorphismPropertyLocally

universe u

open CategoryTheory HomotopicalAlgebra TopCat.modelCategory Limits

namespace DeltaGenerated'

variable {E B : DeltaGenerated'.{u}} {p : E ⟶ B}

lemma fibration_toTopCat_map_of_locally
    (hp : ((fibrations TopCat).inverseImage toTopCat).locally
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
  rw [MorphismProperty.mem_sieveLocally_iff] at hπ
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
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk iso (Iso.refl _))).1 hπ.hl

end DeltaGenerated'
