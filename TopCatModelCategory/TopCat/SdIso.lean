import TopCatModelCategory.SemiSimplexCategory
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.AffineMap

universe u

open CategoryTheory SSet NNReal Simplicial Topology

namespace SimplexCategory

section

variable (n : ℕ)

lemma isAffineMap_aux :
    (IsAffineAt.φ (fun s i ↦ ((⦋n⦌.toTopHomeo s).1 i).1)
      (SSet.yonedaEquiv.{u} (𝟙 _))) = toTopObjι := by
  dsimp [IsAffineAt.φ]
  ext x i
  dsimp [toTopHomeo, toTopObjι]
  simp only [Equiv.symm_apply_apply, CategoryTheory.Functor.map_id, TopCat.hom_id,
    ContinuousMap.id_apply, coe_inj]
  exact congr_fun (congr_arg Subtype.val (congr_arg ULift.down
    (congr_fun ((forget _).congr_map ((toTopSimplex.{u}.app ⦋n⦌).inv_hom_id)) (ULift.up x)))) i

noncomputable def affineMap : AffineMap.{_, u} Δ[n] (Fin (n + 1) → ℝ) where
  f s i := ((⦋n⦌.toTopHomeo s).1 i).1
  isAffine := by
    rw [isAffine_iff_eq_top, stdSimplex.subcomplex_eq_top_iff, mem_isAffine_iff, IsAffineAt]
    erw [isAffineMap_aux]
    intro x
    ext i
    dsimp
    simp [toTopObj.vertex]
    rw [Finset.sum_eq_single i (by aesop) (by simp)]
    simp

namespace affineMap

lemma f_eq_comp : (affineMap n).f = Function.comp toTopObjι ⦋n⦌.toTopHomeo := rfl

lemma isClosedEmbedding_f :
    IsClosedEmbedding (affineMap n).f :=
  isClosedEmbedding_toTopObjι.comp ⦋n⦌.toTopHomeo.isClosedEmbedding

end affineMap

end

noncomputable abbrev sdToTop : CosimplicialObject TopCat.{u} :=
  sd ⋙ SSet.toTop

end SimplexCategory

namespace SemiSimplexCategory

@[simps!]
noncomputable def toTop : SemiCosimplicialObject TopCat.{u} :=
  CosimplicialObject.toSemiCosimplicialObject (stdSimplex ⋙ SSet.toTop)

noncomputable def sdToTop : SemiCosimplicialObject TopCat.{u} :=
  SimplexCategory.sdToTop.toSemiCosimplicialObject

namespace BIso

def homApp (n : ℕ) : |B.obj (Δ[n] : SSet.{u})| ⟶ toTop.obj ⦋n⦌ₛ := by
  sorry

@[reassoc (attr := simp)]
lemma homApp_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) :
    SSet.toTop.map (B.map (toSSet.map f)) ≫ homApp m  =
      homApp n ≫ toTop.map f :=
  sorry

instance (n : ℕ) : IsIso (homApp.{u} n) := sorry

end BIso

noncomputable def BIso : toSSet ⋙ B ⋙ SSet.toTop ≅ toTop :=
  NatIso.ofComponents (fun n ↦ by
    induction n using SemiSimplexCategory.rec with | _ n =>
    exact asIso (BIso.homApp n)) (by
    intro n m f
    induction n using SemiSimplexCategory.rec with | _ n =>
    induction m using SemiSimplexCategory.rec with | _ m =>
    exact BIso.homApp_naturality f)

open Functor in
noncomputable def sdIso : sdToTop.{u} ≅ toTop :=
  isoWhiskerLeft _ (isoWhiskerRight stdSimplexCompBIso.symm _ ≪≫ (associator _ _ _)) ≪≫
    (associator _ _ _).symm ≪≫ BIso

end SemiSimplexCategory
