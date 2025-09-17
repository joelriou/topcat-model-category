import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import TopCatModelCategory.IsTerminal
import TopCatModelCategory.TopCat.ToTopEqualizers
import TopCatModelCategory.TopCat.ToTopProducts
import TopCatModelCategory.Convenient.Fibrations
import TopCatModelCategory.CommSq

open CategoryTheory Limits Simplicial HomotopicalAlgebra TopCat.modelCategory

namespace SSet

instance : PreservesLimitsOfShape (Discrete PEmpty.{1}) toTop.{u} :=
  IsTerminal.preservesTerminal stdSimplex.isTerminalObj₀
    isTerminalToTopObjStdSimplex₀

instance (J : Type*) [Category J] [PreservesLimitsOfShape J toTop.{u}] :
    PreservesLimitsOfShape J toDeltaGenerated.{u} where
  preservesLimit {F} := by
    have : PreservesLimit F (toDeltaGenerated.{u} ⋙ DeltaGenerated'.toTopCat) :=
      preservesLimit_of_natIso _ toDeltaGeneratedCompIso.symm
    exact preservesLimit_of_reflects_of_preserves _ DeltaGenerated'.toTopCat

instance : PreservesFiniteProducts toDeltaGenerated.{u} :=
  PreservesFiniteProducts.of_preserves_binary_and_terminal _

instance : PreservesFiniteLimits toDeltaGenerated.{u} :=
  preservesFiniteLimits_of_preservesEqualizers_and_finiteProducts _

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.toDeltaGenerated') := by
  exact preservesFiniteLimits_of_natIso SSet.toDeltaGeneratedIso

instance :
    PreservesFiniteLimits (toDeltaGenerated.{u} ⋙ DeltaGenerated'.toTopCat ⋙ TopCat.toSSet) :=
  comp_preservesFiniteLimits _ _

instance : PreservesFiniteLimits (toTop.{u} ⋙ TopCat.toSSet) :=
  preservesFiniteLimits_of_natIso ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight SSet.toDeltaGeneratedCompIso TopCat.toSSet.{u})

instance {S S' : SSet.{u}} (p : S' ⟶ S) (A : S.Subcomplex) :
    PreservesLimit (cospan A.ι p) toTop := by
  let φ : |A.preimage p| ⟶ pullback (toTop.map A.ι) (toTop.map p) :=
    pullback.lift (toTop.map (A.fromPreimage p)) (toTop.map ((A.preimage p).ι))
      (by simp [← Functor.map_comp]; rfl)
  have hφ₁ : φ ≫ pullback.fst _ _ = toTop.map (A.fromPreimage p) := by simp [φ]
  have hφ₂ : φ ≫ pullback.snd _ _ = toTop.map (A.preimage p).ι := by simp [φ]
  have h : TopCat.closedEmbeddings φ := by
    rw [← (MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (toTop.map A.ι) (toTop.map p))
        ((closedEmbeddings_toObj_map_of_mono A.ι))).precomp_iff, hφ₂]
    apply closedEmbeddings_toObj_map_of_mono
  have h' : Function.Bijective φ := by
    change Function.Bijective ((forget _).map φ)
    rw [← CategoryTheory.isIso_iff_bijective]
    have sq₁ := (A.preimage_isPullback p).flip.map (toTop ⋙ forget _)
    have sq₂ := (IsPullback.of_hasPullback (toTop.map A.ι) (toTop.map p)).map (forget _)
    refine sq₁.isIso_of_preservesLimit (forget _) sq₂ _
      (by simpa using (forget _).congr_map hφ₁)
      (by simpa using (forget _).congr_map hφ₂)
  have : IsIso φ := h.isIso h'.2
  exact (A.preimage_isPullback p).flip.preservesLimit_of_iso toTop
    (IsPullback.of_hasPullback (toTop.map A.ι) (toTop.map p)) (asIso φ) hφ₁ hφ₂

instance {X₁ X₂ S : SSet.{u}} (f₁ : X₁ ⟶ S) [Mono f₁] (f₂ : X₂ ⟶ S) :
    PreservesLimit (cospan f₁ f₂) toTop := by
  let e : cospan f₁ f₂ ≅ cospan (Subcomplex.range f₁).ι f₂ :=
    cospanExt (asIso (toRangeSubcomplex f₁)) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  apply preservesLimit_of_iso_diagram _ e.symm

end SSet
