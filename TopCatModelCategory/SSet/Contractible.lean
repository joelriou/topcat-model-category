import TopCatModelCategory.SSet.KanComplexWHomotopy
import TopCatModelCategory.SSet.KanComplexKeyLemma
import TopCatModelCategory.SSet.PiZero

open CategoryTheory Simplicial HomotopicalAlgebra SSet.modelCategoryQuillen

universe u

namespace SSet

open KanComplex

instance (n : ℕ) (x : Δ[0] _⦋0⦌) : Subsingleton (π.{u} n Δ[0] x) where
  allEq s s' := by
    obtain ⟨s, rfl⟩ := s.mk_surjective
    obtain ⟨s', rfl⟩ := s'.mk_surjective
    obtain rfl : s = s' := by
      ext : 1
      apply stdSimplex.isTerminalObj₀.hom_ext
    rfl

instance : Subsingleton (π₀ Δ[0]) where
  allEq s s' := by
    obtain ⟨s, rfl⟩ := s.mk_surjective
    obtain ⟨s', rfl⟩ := s'.mk_surjective
    obtain rfl := Subsingleton.elim s s'
    rfl

variable (X : SSet.{u})

structure Contractible where
  pt : X _⦋0⦌
  h : Homotopy (const pt) (𝟙 X)

namespace Contractible

variable {X} (c : X.Contractible)

@[simps]
noncomputable def homotopyEquiv : HomotopyEquiv X Δ[0] where
  hom := stdSimplex.isTerminalObj₀.from X
  inv := const c.pt
  homInvId := c.h
  invHomId := .ofEq (by simp)

variable [IsFibrant X]

include c

lemma subsingleton_π₀ : Subsingleton X.π₀ :=
  (W.homotopyEquivInv c.homotopyEquiv).bijective_mapπ₀.symm.1.subsingleton

lemma subsingleton_kanComplexπ (n : ℕ) (x : X _⦋0⦌) : Subsingleton (π n X x) :=
  ((W.homotopyEquivHom c.homotopyEquiv).bijective n x _ rfl).1.subsingleton

end Contractible

abbrev IsContractible : Prop := Nonempty X.Contractible

noncomputable def Contractible.ofIsContractible [X.IsContractible] :
    Contractible X := Classical.arbitrary _

variable [X.IsContractible] [IsFibrant X]

instance : Subsingleton X.π₀ := (Contractible.ofIsContractible X).subsingleton_π₀

instance (n : ℕ) (x : X _⦋0⦌) : Subsingleton (π n X x) :=
  (Contractible.ofIsContractible X).subsingleton_kanComplexπ n x

end SSet
