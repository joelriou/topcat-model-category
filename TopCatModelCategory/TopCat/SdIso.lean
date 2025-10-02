import TopCatModelCategory.SemiSimplexCategory
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.SSet.AffineMap
import TopCatModelCategory.Homeomorph

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

def toTopObj' (n : SimplexCategory) : Set ((Fin (n.len + 1) → ℝ)) :=
  { f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

def toTopObjHomeo' (n : SimplexCategory) :
    n.toTopObj ≃ₜ n.toTopObj' where
  toFun x := ⟨fun i ↦ x i, by
    obtain ⟨x, hx⟩ := x
    dsimp [toTopObj] at hx
    simp [toTopObj', ← NNReal.coe_sum, hx]⟩
  invFun x := ⟨fun i ↦ ⟨x.1 i, x.2.1 i⟩, by
    obtain ⟨x, _, hx⟩ := x
    ext
    simpa⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by continuity
  continuous_invFun := Isometry.continuous (fun _ => congrFun rfl)

lemma affineMap_stdSimplex_f (n : ℕ) :
    (AffineMap.stdSimplex n).f = Subtype.val ∘ toTopObjHomeo' ⦋n⦌ ∘ toTopHomeo _ := rfl

lemma affineMap_stdSimplex_range_f (n : ℕ) :
    Set.range (AffineMap.stdSimplex n).f = ⦋n⦌.toTopObj' := by
  simp [affineMap_stdSimplex_f, Set.range_comp]

end SimplexCategory

namespace SemiSimplexCategory

@[simps!]
noncomputable def toTop : SemiCosimplicialObject TopCat.{u} :=
  CosimplicialObject.toSemiCosimplicialObject (stdSimplex ⋙ SSet.toTop)

noncomputable def sdToTop : SemiCosimplicialObject TopCat.{u} :=
  SimplexCategory.sdToTop.toSemiCosimplicialObject

namespace BIso

noncomputable def homApp (n : ℕ) :
    |B.obj (Δ[n] : SSet.{u})| ⟶ toTop.obj ⦋n⦌ₛ :=
  TopCat.ofHom (⦋n⦌.toTopHomeo.symm.continuousMap.comp
    (⦋n⦌.toTopObjHomeo'.symm.continuousMap.comp ⟨fun x ↦
    ⟨(AffineMap.stdSimplex n).b.f x, by
      rw [← SimplexCategory.affineMap_stdSimplex_range_f.{u}]
      exact (AffineMap.stdSimplex.{u} n).range_b_f_subset_range_f (by simp)⟩,
    (AffineMap.stdSimplex n).b.continuous.subtype_mk _⟩))

lemma f_comp_homApp (n : ℕ) :
    (AffineMap.stdSimplex n).f ∘ homApp n =
      (AffineMap.stdSimplex n).b.f := by
  ext x
  simp [homApp, SimplexCategory.toTopObjHomeo', AffineMap.stdSimplex]

lemma f_comp_homApp_apply {n : ℕ} (x) :
    (AffineMap.stdSimplex n).f (homApp n x) =
      (AffineMap.stdSimplex n).b.f x :=
  congr_fun (f_comp_homApp n) x

lemma homApp_naturality {n m : ℕ} (f : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ) :
    SSet.toTop.map (B.map (toSSet.map f)) ≫ homApp m =
      homApp n ≫ toTop.map f := by
  ext x
  apply AffineMap.injective_stdSimplex_f
  dsimp
  erw [f_comp_homApp_apply]
  have := f_comp_homApp_apply x
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
