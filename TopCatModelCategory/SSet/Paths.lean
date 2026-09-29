module

public import Mathlib.AlgebraicTopology.SimplicialSet.Path
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

@[expose] public section

universe u

open Simplicial CategoryTheory MonoidalCategory

namespace SSet

@[simps arrow]
def pathOfArrows (X : SSet.{u}) {n : ℕ} (ar : Fin (n + 1) → X _⦋1⦌)
    (h : ∀ (i : Fin n), X.δ 0 (ar i.castSucc) = X.δ 1 (ar i.succ)) :
    Path X (n + 1) where
  vertex j := match j with
    | 0 => X.δ 1 (ar 0)
    | ⟨j + 1, hj⟩ => X.δ 0 (ar ⟨j, by omega⟩)
  arrow := ar
  arrow_src j := match j with
    | 0 => rfl
    | ⟨j + 1, hj⟩ => (h ⟨j, by omega⟩).symm
  arrow_tgt _ := rfl

@[simps!]
noncomputable def Path.tensor {X Y : SSet.{u}} {n : ℕ} (p : Path X n) (q : Path Y n) :
    Path (X ⊗ Y) n where
  vertex i := ⟨p.vertex i, q.vertex i⟩
  arrow i := ⟨p.arrow i, q.arrow i⟩
  arrow_src i := by
    dsimp
    rw [← p.arrow_src i, ← q.arrow_src i]
    rfl
  arrow_tgt i := by
    dsimp
    rw [← p.arrow_tgt i, ← q.arrow_tgt i]
    rfl

end SSet
