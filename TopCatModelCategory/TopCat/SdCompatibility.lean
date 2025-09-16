import TopCatModelCategory.TopCat.ToTopSdIso
import TopCatModelCategory.SSet.Mesh

universe u

open CategoryTheory Simplicial Limits

namespace SSet

namespace AffineMap

variable {X : SSet.{u}} [X.IsWeaklyPolyhedralLike]
  {E : Type v} [AddCommGroup E] [Module ℝ E] (f : X.AffineMap E)

lemma b_f_toTop_map_b_map_apply (x : X.N) (y) :
    f.b.f ((ConcreteCategory.hom (toTop.map (B.map (yonedaEquiv.symm x.simplex)))) y) =
      f.f (toTop.map (yonedaEquiv.symm x.simplex)
        (SemiSimplexCategory.BIso.{u}.hom.app ⦋x.dim⦌ₛ y)) :=
  sorry

lemma sd_f_toTop_map_sd_map_apply (x : X.N) (y : |sd.obj Δ[x.dim]|) :
    f.sd.f ((ConcreteCategory.hom (toTop.map (sd.map (yonedaEquiv.symm x.simplex)))) y) =
      f.f (toTop.map (yonedaEquiv.symm x.simplex)
        (SemiSimplexCategory.sdIso.hom.app ⦋x.dim⦌ₛ
        (toTop.map (stdSimplex.sdIso.hom.app ⦋x.dim⦌) y))) := by
  dsimp [AffineMap.sd, AffineMap.precomp, SemiSimplexCategory.sdIso]
  trans f.b.f ((ConcreteCategory.hom (toTop.map (B.map (yonedaEquiv.symm x.simplex))))
    (toTop.map (sdToB.app _) y))
  · apply congr_arg
    simpa only [Functor.map_comp, CategoryTheory.comp_apply] using
      ConcreteCategory.congr_hom (toTop.congr_map (sdToB.naturality (yonedaEquiv.symm x.simplex))) y
  · rw [b_f_toTop_map_b_map_apply]
    congr 3
    apply congr_fun
    rw [sdToB_app_stdSimplex_obj, Functor.map_comp]
    rfl

@[simp]
lemma f_comp_toTopSdIso_hom : f.f ∘ (toTopSdIso X).hom = f.sd.f := by
  have (x : X.N) :
      f.f ∘ (toTopSdIso X).hom ∘ toTop.map (sd.map (yonedaEquiv.symm x.simplex)) =
        f.sd.f ∘ toTop.map (sd.map (yonedaEquiv.symm x.simplex)) := by
    ext y
    dsimp
    rw [sd_f_toTop_map_sd_map_apply]
    exact (congr_arg f.f (ConcreteCategory.congr_hom
      (N.toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom.{u} x) y))
  ext x
  obtain ⟨x, y, rfl⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (sd ⋙ toTop ⋙ forget _) X.isColimitCoconeN')) x
  exact congr_fun (this x) y

@[simp]
lemma f_comp_toTopSdIterIso_hom (n : ℕ) :
    f.f ∘ (toTopSdIterIso X n).hom = (f.sdIter n).f := by
  induction n with
  | zero =>
    dsimp
  | succ n hn =>
    dsimp
    rw [← Function.comp_assoc, hn, f_comp_toTopSdIso_hom]

end AffineMap

end SSet
