import TopCatModelCategory.TopCat.Adj
import Mathlib.Analysis.Normed.Module.Basic

open CategoryTheory Simplicial

universe v u

namespace SimplexCategory.toTopObj

variable {n : ℕ} {E : Type v} [AddCommGroup E] [Module ℝ E]
  (f : ⦋n⦌.toTopObj → E)

def vertex (i : Fin (n + 1)) : ⦋n⦌.toTopObj :=
  ⟨fun j ↦ if j = i then 1 else 0, by simp [toTopObj]⟩

def IsAffine : Prop :=
  ∀ (x : ⦋n⦌.toTopObj), f x = ∑ (i : Fin (n + 1)), (x.1 i : ℝ) • f (vertex i)

end SimplexCategory.toTopObj

namespace SSet

variable {X : SSet.{u}} {E : Type v} [AddCommGroup E] [Module ℝ E]
  (f : |X| → E)

namespace IsAffineAt

noncomputable def map {n : ℕ} (x : X _⦋n⦌) : ⦋n⦌.toTopObj → E :=
  f.comp
    (Function.comp (toTopSimplex.inv.app _ ≫ toTop.map (yonedaEquiv.symm x)) ULift.up)

end IsAffineAt

def IsAffineAt {n : ℕ} (x : X _⦋n⦌) : Prop :=
  SimplexCategory.toTopObj.IsAffine (IsAffineAt.map f x)

def IsAffine : Prop := ∀ ⦃n : ℕ⦄ (x : X _⦋n⦌), IsAffineAt f x

end SSet
