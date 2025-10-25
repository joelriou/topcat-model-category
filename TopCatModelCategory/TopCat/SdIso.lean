import TopCatModelCategory.SemiSimplexCategory
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.Gluing
import TopCatModelCategory.SSet.AffineMap
import TopCatModelCategory.Homeomorph

universe u

open CategoryTheory SSet NNReal Simplicial Topology Limits

namespace SimplexCategory

section

variable (n : ℕ)

noncomputable def affineMap : AffineMap.{_, u} Δ[n] (Fin (n + 1) → ℝ) where
  f s := ⦋n⦌.toTopHomeo s
  isAffine := by
    rw [isAffine_iff_eq_top, stdSimplex.subcomplex_eq_top_iff, mem_isAffine_iff,
      IsAffineAt, AffineMap.isAffineAtφ_toTopHomeo]
    exact stdSimplex.isAffine_dFunLikeCoe _

namespace affineMap

lemma f_eq_comp : (affineMap n).f = Function.comp toTopObjι ⦋n⦌.toTopHomeo := rfl

lemma isClosedEmbedding_f :
    IsClosedEmbedding (affineMap n).f :=
  isClosedEmbedding_toTopObjι.comp ⦋n⦌.toTopHomeo.isClosedEmbedding

end affineMap

end

noncomputable abbrev sdToTop : CosimplicialObject TopCat.{u} :=
  sd ⋙ SSet.toTop

lemma affineMap_stdSimplex_f (n : ℕ) :
    (AffineMap.stdSimplex n).f = DFunLike.coe ∘ toTopHomeo _ := rfl

lemma affineMap_stdSimplex_range_f (n : ℕ) :
    Set.range (AffineMap.stdSimplex n).f = stdSimplex _ _ := by
  simp [affineMap_stdSimplex_f, Set.range_comp]
  change Set.range Subtype.val = _
  simp

end SimplexCategory

namespace SemiSimplexCategory

@[simps!]
noncomputable def toTop : SemiCosimplicialObject TopCat.{u} :=
  CosimplicialObject.toSemiCosimplicialObject (stdSimplex ⋙ SSet.toTop)

noncomputable def sdToTop : SemiCosimplicialObject TopCat.{u} :=
  SimplexCategory.sdToTop.toSemiCosimplicialObject

namespace BIso

section

variable (n : ℕ)

noncomputable abbrev ι := (B.{u}.obj Δ[n]).N

noncomputable def F : ι.{u} n ⥤ TopCat.{u} := (B.{u}.obj Δ[n]).functorN ⋙ SSet.toTop

noncomputable def cocone₁ := SSet.toTop.mapCocone (B.{u}.obj Δ[n]).coconeN

noncomputable def isColimit₁ : IsColimit (cocone₁.{u} n) :=
  isColimitOfPreserves _ (B.obj Δ[n]).isColimitCoconeN

lemma isColimit₁' : ((Functor.coconeTopEquiv _).symm (cocone₁.{u} n)).IsColimit :=
  (TopCat.isColimit_iff_coconeTopIsColimit (c := cocone₁.{u} n)).1 ⟨isColimit₁ n⟩

@[simps]
noncomputable def toStdSimplex (n : ℕ) :
    C(|B.obj (Δ[n] : SSet.{u})|, stdSimplex ℝ (Fin (n + 1))) where
  toFun x := ⟨(AffineMap.stdSimplex n).b.f x, by
    rw [← SimplexCategory.affineMap_stdSimplex_range_f.{u}]
    exact (AffineMap.stdSimplex.{u} n).range_b_f_subset_range_f (by simp)⟩
  continuous_toFun := (AffineMap.stdSimplex n).b.continuous.subtype_mk _

noncomputable def cocone₂ : (F.{u} n).CoconeTop :=
  ((Functor.coconeTopEquiv _).symm (cocone₁.{u} n)).postcomp (toStdSimplex.{u} n)

lemma isColimit₂ : (cocone₂.{u} n).IsColimit := sorry

noncomputable def homeomorph :
    |B.obj (Δ[n] : SSet.{u})| ≃ₜ stdSimplex ℝ (Fin (n + 1)) :=
  (isColimit₁'.{u} n).ptUnique (isColimit₂ _)

lemma homeomorph_apply (x) : homeomorph.{u} n x = toStdSimplex.{u} n x := by
  apply (isColimit₁'.{u} n).funext'
  intro i
  ext x
  dsimp [homeomorph]
  erw [Functor.CoconeTop.IsColimit.ptUnique_ι]
  rfl

lemma isHomeomorph : IsHomeomorph (toStdSimplex.{u} n) := by
  convert (homeomorph.{u} n).isHomeomorph
  ext x : 1
  exact (homeomorph_apply.{u} n x).symm

end

lemma toStdSimplex_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) (x : |B.{u}.obj Δ[n]|) :
    toStdSimplex m (SSet.toTop.map (B.map (toSSet.map f)) x) =
      stdSimplex.map f.toOrderEmbedding (toStdSimplex n x) := by
  sorry

noncomputable def toStdSimplex' (n : ℕ) :
    |B.obj (Δ[n] : SSet.{u})| ⟶ toTop.obj ⦋n⦌ₛ :=
  TopCat.ofHom (⦋n⦌.toTopHomeo.symm.continuousMap.comp (toStdSimplex n))

lemma f_comp_toStdSimplex' (n : ℕ) :
    (AffineMap.stdSimplex n).f ∘ toStdSimplex' n =
      (AffineMap.stdSimplex n).b.f := by
  ext f : 1
  dsimp [toStdSimplex']
  erw [AffineMap.stdSimplex_f_toTopHomeo_symm]
  rfl

lemma f_comp_toStdSimplex'_apply {n : ℕ} (x) :
    (AffineMap.stdSimplex n).f (toStdSimplex' n x) =
      (AffineMap.stdSimplex n).b.f x :=
  congr_fun (f_comp_toStdSimplex' n) x

lemma toStdSimplex'_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) :
    SSet.toTop.map (B.map (toSSet.map f)) ≫ toStdSimplex' m =
      toStdSimplex' n ≫ toTop.map f := by
  ext x
  dsimp [toStdSimplex']
  erw [toStdSimplex_naturality f x,
    SimplexCategory.toTopHomeo_symm_naturality_apply (toSimplexCategory.map f)]
  rfl

instance (n : ℕ) : IsIso (toStdSimplex'.{u} n) :=
  (TopCat.isoOfHomeo ((isHomeomorph.{u} n).homeomorph.trans ⦋n⦌.toTopHomeo.symm)).isIso_hom

end BIso

noncomputable def BIso : toSSet ⋙ B ⋙ SSet.toTop ≅ toTop :=
  NatIso.ofComponents (fun n ↦ by
    induction n using SemiSimplexCategory.rec with | _ n =>
    exact asIso (BIso.toStdSimplex' n)) (by
    intro n m f
    induction n using SemiSimplexCategory.rec with | _ n =>
    induction m using SemiSimplexCategory.rec with | _ m =>
    exact BIso.toStdSimplex'_naturality f)

open Functor in
noncomputable def sdIso : sdToTop.{u} ≅ toTop :=
  isoWhiskerLeft _ (isoWhiskerRight stdSimplexCompBIso.symm _ ≪≫ (associator _ _ _)) ≪≫
    (associator _ _ _).symm ≪≫ BIso

end SemiSimplexCategory
