import Mathlib.CategoryTheory.Functor.Basic

namespace CategoryTheory

variable {C : Type*} [Category C]

namespace Functor

variable (F : C ⥤ C)

def iter : ℕ → C ⥤ C
  | .zero => 𝟭 C
  | .succ n => iter n ⋙ F

@[simp]
lemma iter_zero : F.iter 0 = 𝟭 C := rfl

lemma iter_succ (n : ℕ) : F.iter (n + 1) = F.iter n ⋙ F := rfl

@[simp]
lemma iter_succ_obj (n : ℕ) (X : C) :
    (F.iter (n + 1)).obj X = F.obj ((F.iter n).obj X) := rfl

end Functor

end CategoryTheory
