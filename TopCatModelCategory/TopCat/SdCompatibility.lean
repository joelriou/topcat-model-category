import TopCatModelCategory.TopCat.ToTopSdIso
import TopCatModelCategory.SSet.Mesh

universe u

open CategoryTheory Simplicial

namespace SSet

namespace AffineMap

variable {X : SSet.{u}} [X.IsWeaklyPolyhedralLike]
  {E : Type v} [AddCommGroup E] [Module ℝ E] (f : X.AffineMap E)

@[simp]
lemma f_comp_toTopSdIso_hom : f.f ∘ (toTopSdIso X).hom = f.sd.f := by
  have (x : X.N) :
      f.f ∘ (toTopSdIso X).hom ∘ toTop.map (sd.map (yonedaEquiv.symm x.simplex)) =
        f.sd.f ∘ toTop.map (sd.map (yonedaEquiv.symm x.simplex)) := by
    ext y
    refine (congr_arg f.f (ConcreteCategory.congr_hom
      (N.toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom.{u} x) y)).trans ?_
    dsimp
    sorry
  have := @N.toTop_map_sd_map_yonedaEquiv_symm_simplex_comp_toTopSdIso_hom.{u}
  sorry

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
