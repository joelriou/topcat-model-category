import TopCatModelCategory.SSet.FibrationSequenceAdj
import TopCatModelCategory.SSet.SingularConnected

open CategoryTheory HomotopicalAlgebra SSet.modelCategoryQuillen
  Simplicial

lemma Group.injective_iff_of_map_mul {α β : Type*} [Group α] [Group β]
    (f : α → β) (hf : ∀ x y, f (x * y) = f x * f y) :
    Function.Injective f ↔ ∀ x, f x = 1 → x = 1 := by
  let φ : α →* β := MonoidHom.mk' f hf
  have f_one : f 1 = 1 := φ.map_one
  constructor
  · intro hf' x hx
    exact hf' (by rw [f_one, hx])
  · intro hf' x y hxy
    obtain ⟨u, rfl⟩ : ∃ u, x * u = y := ⟨_, mul_inv_cancel_left x y⟩
    rw [hf' u (by simpa only [hf, left_eq_mul] using hxy), mul_one]

namespace SSet

namespace KanComplex

variable (X : SSet.{0})

instance : IsFibrant ((toTop ⋙ TopCat.toSSet).obj X) := by dsimp; infer_instance

instance [IsFibrant X] : IsFibrant ((𝟭 _).obj X) := by dsimp; infer_instance

instance [IsFibrant X] (n : ℕ) (x : X _⦋0⦌) :
    Subsingleton (π n (X.path₀ x) (X.path₀BasePoint x)) := sorry

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
      have : Function.Injective ((FibrationSequence.loop X x).toTopToSSet.δ n) := sorry
      refine ⟨w, this ?_⟩
      have := (FibrationSequence.δ_naturality_apply
        ((FibrationSequence.loop X x).ιtoTopToSSet) w).symm
      dsimp at w this
      rw [← hz, this]

end KanComplex

end SSet
