module

public import Mathlib.CategoryTheory.Functor.Basic

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace Functor

variable (F : C ⥤ C)

def iter : ℕ → C ⥤ C
  | .zero => 𝟭 C
  | .succ n => iter n ⋙ F

@[simp]
lemma iter_zero : F.iter 0 = 𝟭 C := rfl

@[simp]
lemma iter_succ (n : ℕ) : F.iter (n + 1) = F.iter n ⋙ F := rfl

end Functor

end CategoryTheory
