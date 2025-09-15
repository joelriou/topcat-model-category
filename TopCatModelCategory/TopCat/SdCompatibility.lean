import TopCatModelCategory.TopCat.ToTopSdIso
import TopCatModelCategory.SSet.Mesh

universe u

open Simplicial

namespace SSet

namespace AffineMap

variable {X : SSet.{u}} [X.IsWeaklyPolyhedralLike]
  {E : Type v} [AddCommGroup E] [Module ℝ E] (f : X.AffineMap E)

@[simp]
lemma f_comp_toTopSdIso_hom : f.f ∘ (toTopSdIso X).hom = f.sd.f := by
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
