import TopCatModelCategory.SSet.StandardSimplex

universe v u

open CategoryTheory Simplicial

namespace SSet

namespace stdSimplex

def uliftIso (n : ℕ) : uliftFunctor.{v, u}.obj Δ[n] ≅ Δ[n] :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso (Equiv.ulift.trans (objEquiv.trans objEquiv.symm)))

end stdSimplex

namespace horn

variable (n : ℕ) (i : Fin (n + 1))

def uliftIso : uliftFunctor.{v, u}.obj Λ[n, i] ≅ Λ[n, i] :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso
    { toFun := fun ⟨a, ha⟩ ↦ ⟨stdSimplex.objEquiv.symm (stdSimplex.objEquiv a), by
        obtain ⟨a, rfl⟩ := stdSimplex.objEquiv.{u}.symm.surjective a
        exact ha⟩
      invFun := fun ⟨a, ha⟩ ↦ ⟨stdSimplex.objEquiv.symm (stdSimplex.objEquiv a), by
        obtain ⟨a, rfl⟩ := stdSimplex.objEquiv.{max v u}.symm.surjective a
        exact ha⟩
      left_inv _ := rfl
      right_inv _ := rfl })

def arrowUliftIso :
    Arrow.mk (uliftFunctor.{v, u}.map Λ[n, i].ι) ≅ Arrow.mk Λ[n, i].ι :=
  Arrow.isoMk (uliftIso n i) (stdSimplex.uliftIso n)

end horn

namespace boundary

variable (n : ℕ)

def uliftIso : uliftFunctor.{v, u}.obj ∂Δ[n] ≅ ∂Δ[n] :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso
    { toFun := fun ⟨a, ha⟩ ↦ ⟨stdSimplex.objEquiv.symm (stdSimplex.objEquiv a), by
        obtain ⟨a, rfl⟩ := stdSimplex.objEquiv.{u}.symm.surjective a
        exact ha⟩
      invFun := fun ⟨a, ha⟩ ↦ ⟨stdSimplex.objEquiv.symm (stdSimplex.objEquiv a), by
        obtain ⟨a, rfl⟩ := stdSimplex.objEquiv.{max v u}.symm.surjective a
        exact ha⟩
      left_inv _ := rfl
      right_inv _ := rfl })

def arrowUliftIso :
    Arrow.mk (uliftFunctor.{v, u}.map ∂Δ[n].ι) ≅ Arrow.mk ∂Δ[n].ι :=
  Arrow.isoMk (uliftIso n) (stdSimplex.uliftIso n)

end boundary

end SSet
