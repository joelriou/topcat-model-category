import TopCatModelCategory.SSet.FibrationSequenceAdj
import TopCatModelCategory.SSet.SingularConnected

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  Simplicial

namespace SSet

namespace KanComplex

variable (X : SSet.{0})

instance : IsFibrant ((toTop ⋙ TopCat.toSSet).obj X) := by dsimp; infer_instance

instance [IsFibrant X] : IsFibrant ((𝟭 _).obj X) := by dsimp; infer_instance

lemma W.sSetTopAdj_unit_app [IsFibrant X] :
    W (sSetTopAdj.unit.app X) := by
  revert X
  suffices ∀ (n : ℕ), ∀ (X : SSet.{0}) [IsFibrant X] (x : X _⦋0⦌),
      Function.Bijective (mapπ (sSetTopAdj.unit.app X) n x _ rfl) by
    intro X _
    have hX : IsFibrant ((𝟭 _).obj X) := by dsimp; infer_instance
    rw [W_iff]
    exact ⟨bijective_mapπ₀_sSetTopAdj_unit_app _,
      by rintro n x _ rfl; exact this _ _ _⟩
  intro n
  induction n with
  | zero =>
    intro X _ x
    rw [bijective_mapπ₀_iff_bijective_mapπ_zero]
    apply bijective_mapπ₀_sSetTopAdj_unit_app
  | succ n hn =>
    intro X _ x
    constructor
    · rw [Group.injective_iff_of_map_mul _ (by simp [mapπ_mul])]
      dsimp
      intro y hy
      have := (FibrationSequence.δ_naturality_apply
        ((FibrationSequence.loop X x).ιtoTopToSSet) y).symm
      dsimp at this
      obtain ⟨z, rfl⟩ := (FibrationSequence.loop X x).exact₃ y
        ((hn (X.loop x) (X.loopBasePoint x)).1 (a₂ := 1) (by simp [this, hy]))
      obtain rfl : z = 1 := by dsimp; apply Subsingleton.elim
      simp
    · intro y
      obtain ⟨z, hz⟩ := (hn _ _).2 ((FibrationSequence.loop X x).toTopToSSet.δ n y)
      dsimp at y z hz
      obtain ⟨w, rfl⟩ := (FibrationSequence.loop X x).exact₁ z
        (by dsimp; apply Subsingleton.elim)
      refine ⟨w, (FibrationSequence.bijective_δ_toTopToSSet_loop X x n).1 ?_⟩
      have := (FibrationSequence.δ_naturality_apply
        ((FibrationSequence.loop X x).ιtoTopToSSet) w).symm
      dsimp at w this
      rw [← hz, this]

end KanComplex

end SSet
