import TopCatModelCategory.TopCat.SdIso
import TopCatModelCategory.SSet.CoconeNPrime

universe u

open CategoryTheory Simplicial Limits

namespace SSet

variable (X : SSet.{u}) [IsWeaklyPolyhedralLike X]
  {Y : SSet.{u}} [IsWeaklyPolyhedralLike Y]

open Functor in
@[simps! hom_app inv_app]
noncomputable def functorN'CompSdCompToTopIso :
    X.functorN' ⋙ sd ⋙ toTop ≅ X.functorN' ⋙ toTop :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _ ≪≫
    isoWhiskerLeft _ ((associator _ _ _).symm ≪≫
    isoWhiskerRight stdSimplex.sdIso.{u} toTop) ≪≫
    SemiSimplexCategory.sdIso ≪≫
    (isoWhiskerLeft _ toTopSimplex.symm ≪≫ (associator _ _ _).symm)) ≪≫
    (associator _ _ _).symm

@[simps! pt ι_app]
noncomputable def toTopSdIsoCocone : Cocone (X.functorN' ⋙ toTop) :=
  (Cocones.precompose X.functorN'CompSdCompToTopIso.inv).obj
    ((sd ⋙ toTop).mapCocone X.coconeN')

noncomputable def isColimitToTopSdIsoCocone : IsColimit X.toTopSdIsoCocone :=
  (IsColimit.precomposeInvEquiv X.functorN'CompSdCompToTopIso _).2
    (isColimitOfPreserves (sd ⋙ toTop) X.isColimitCoconeN')

noncomputable def toTopSdIso : |sd.obj X| ≅ |X| :=
  IsColimit.coconePointUniqueUpToIso X.isColimitToTopSdIsoCocone
    (isColimitOfPreserves toTop X.isColimitCoconeN')

variable {X} in
@[reassoc]
lemma N.toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom (x : X.N) :
    toTop.map (sd.map (yonedaEquiv.symm x.simplex)) ≫ X.toTopSdIso.hom =
    toTop.map (stdSimplex.sdIso.hom.app _) ≫ SemiSimplexCategory.sdIso.hom.app ⦋x.dim⦌ₛ ≫
      toTopSimplex.inv.app ⦋x.dim⦌ ≫ toTop.map (yonedaEquiv.symm x.simplex) := by
  have := IsColimit.comp_coconePointUniqueUpToIso_hom X.isColimitToTopSdIsoCocone
    (isColimitOfPreserves toTop X.isColimitCoconeN') x
  dsimp at this ⊢
  simp only [toTopSdIsoCocone_ι_app, Category.assoc] at this
  simp only [toTopSdIso, ← this, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc]

@[reassoc]
lemma toTop_map_sd_map_yonedaEquiv_symm_comp_toTopSdIso_hom
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) :
    toTop.map (sd.map (yonedaEquiv.symm x)) ≫ X.toTopSdIso.hom =
    toTop.map (stdSimplex.sdIso.hom.app _) ≫ SemiSimplexCategory.sdIso.hom.app ⦋n⦌ₛ ≫
      toTopSimplex.inv.app ⦋n⦌ ≫ toTop.map (yonedaEquiv.symm x) :=
  (N.mk _ hx).toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom

variable {X} (f : X ⟶ Y)

@[reassoc]
lemma toTopSdIso_hom_naturality
    (hf : ∀ ⦃n : ℕ⦄ (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate _),
      f.app _ x ∈ Y.nonDegenerate _):
    toTop.map (sd.map f) ≫ Y.toTopSdIso.hom =
      X.toTopSdIso.hom ≫ toTop.map f := by
  apply X.isColimitToTopSdIsoCocone.hom_ext
  intro x
  obtain ⟨n, ⟨x, hx⟩, rfl⟩ := x.mk_surjective
  dsimp
  simp only [toTopSdIsoCocone_ι_app, Category.assoc]
  dsimp
  rw [toTop_map_sd_map_yonedaEquiv_symm_comp_toTopSdIso_hom_assoc _ _ hx]
  nth_rw 2 [← toTop.map_comp_assoc]
  rw [← sd.map_comp, yonedaEquiv_symm_comp,
    toTop_map_sd_map_yonedaEquiv_symm_comp_toTopSdIso_hom _ _ (hf _ hx),
    ← yonedaEquiv_symm_comp, Functor.map_comp]

@[reassoc (attr := simp)]
lemma Subcomplex.toTopSdIso_hom_naturality (A : X.Subcomplex) :
    toTop.map (sd.map A.ι) ≫ X.toTopSdIso.hom =
      A.toSSet.toTopSdIso.hom ≫ toTop.map A.ι :=
  SSet.toTopSdIso_hom_naturality A.ι (fun _ _ ↦ by
    simp [← nonDegenerate_iff_of_mono A.ι])

end SSet
