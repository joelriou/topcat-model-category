import TopCatModelCategory.TopCat.SdIso
import TopCatModelCategory.SSet.CoconeNPrime
import TopCatModelCategory.FunctorIterate

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
    SemiSimplexCategory.sdIso ≪≫ (associator _ _ _).symm) ≪≫
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
      toTop.map (yonedaEquiv.symm x.simplex) := by
  have := IsColimit.comp_coconePointUniqueUpToIso_hom X.isColimitToTopSdIsoCocone
    (isColimitOfPreserves toTop X.isColimitCoconeN') x
  dsimp at this ⊢
  simp only [toTopSdIsoCocone_ι_app, Category.assoc] at this
  simp only [toTopSdIso, ← this, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc]

@[reassoc]
lemma toTop_map_sd_map_yonedaEquiv_symm_comp_toTopSdIso_hom
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) :
    toTop.map (sd.map (yonedaEquiv.symm x)) ≫ X.toTopSdIso.hom =
    toTop.map (stdSimplex.sdIso.hom.app _) ≫ SemiSimplexCategory.sdIso.hom.app ⦋n⦌ₛ ≫
      toTop.map (yonedaEquiv.symm x) :=
  (N.mk _ hx).toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom

instance (n : ℕ) : ((sd.iter n).obj X).IsWeaklyPolyhedralLike := by
  induction n
  all_goals dsimp; infer_instance

noncomputable def toTopSdIterIso (n : ℕ) : |(sd.iter n).obj X| ≅ |X| := by
  induction n with
  | zero => rfl
  | succ n hn => exact toTopSdIso _ ≪≫ hn

@[simp]
lemma toTopSdIterIso_zero : X.toTopSdIterIso 0 = Iso.refl _ := rfl

@[simp]
lemma toTopSdIterIso_succ (n : ℕ) : X.toTopSdIterIso (n + 1) =
    toTopSdIso _ ≪≫ X.toTopSdIterIso n := rfl

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
    toTop_map_sd_map_yonedaEquiv_symm_comp_toTopSdIso_hom _ _ (hf _ hx)]
  dsimp
  rw [← yonedaEquiv_symm_comp, Functor.map_comp]

@[reassoc (attr := simp)]
lemma toTopSdIso_hom_naturality_of_mono [Mono f]:
    toTop.map (sd.map f) ≫ Y.toTopSdIso.hom =
      X.toTopSdIso.hom ≫ toTop.map f :=
  SSet.toTopSdIso_hom_naturality f (by simp [nonDegenerate_iff_of_mono])

@[reassoc]
lemma Subcomplex.toTopSdIso_hom_naturality (A : X.Subcomplex) :
    toTop.map (sd.map A.ι) ≫ X.toTopSdIso.hom =
      A.toSSet.toTopSdIso.hom ≫ toTop.map A.ι := by
  simp

instance (n : ℕ) [Mono f] : Mono ((sd.iter n).map f) := by
  induction n
  all_goals dsimp; infer_instance

@[reassoc (attr := simp)]
lemma toTopSdIterIso_hom_naturality_of_mono [Mono f] (n : ℕ) :
    toTop.map ((sd.iter n).map f) ≫ (Y.toTopSdIterIso n).hom =
    (X.toTopSdIterIso n).hom ≫ toTop.map f := by
  induction n <;> aesop

noncomputable def toTopSdIterArrowIso [Mono f] (n : ℕ) :
    Arrow.mk (toTop.map ((sd.iter n).map f)) ≅ Arrow.mk (toTop.map f) :=
  Arrow.isoMk (X.toTopSdIterIso n) (Y.toTopSdIterIso n)

end SSet
