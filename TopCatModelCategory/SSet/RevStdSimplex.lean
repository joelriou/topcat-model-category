import TopCatModelCategory.SSet.Rev
import TopCatModelCategory.SSet.StandardSimplex

universe u

open CategoryTheory

namespace SSet

namespace stdSimplex

def revIso {n : SimplexCategory} : (stdSimplex.{u}.obj n).rev ≅ stdSimplex.obj n :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso
    { toFun x := objEquiv.symm (SimplexCategory.rev.map (objEquiv x))
      invFun y := objEquiv.symm (SimplexCategory.rev.map (objEquiv y))
      left_inv _ := objEquiv.injective (by aesop)
      right_inv _ := objEquiv.injective (by aesop)}) (fun f ↦ by
        ext g
        apply objEquiv.injective
        dsimp
        rw [Equiv.apply_symm_apply]
        ext i : 3
        rw [SimplexCategory.rev_map_apply]
        dsimp [objEquiv, stdSimplex, uliftFunctor]
        rw [Fin.rev_rev])

def subcomplexRev {n : SimplexCategory}
    (A : (stdSimplex.{u}.obj n).Subcomplex) :
      (stdSimplex.obj n).Subcomplex :=
  A.rev.preimage revIso.inv

/-lemma subcomplexRev_horn {n : ℕ} (i : Fin (n + 1)) :
    subcomplexRev (horn n i) = horn n i.rev := by
  sorry-/

end stdSimplex

end SSet
