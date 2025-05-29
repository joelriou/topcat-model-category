import TopCatModelCategory.SSet.FundamentalGroupoidPiOne
import TopCatModelCategory.SSet.SmallObject

universe u

open CategoryTheory Limits HomotopicalAlgebra SSet.modelCategoryQuillen

namespace SSet

namespace KanComplex

open SSet.modelCategoryQuillen in
lemma of_isColimit {K : Type*} [Category K] [IsFiltered K]
    [Small.{u} K] [LocallySmall.{u} K] {F : K ⥤ SSet.{u}}
    [hF : ∀ j, IsFibrant (F.obj j)]
    {c : Cocone F} (hc : IsColimit c) : IsFibrant c.pt where
  mem := by
    rw [fibrations_eq]
    intro A B f hf
    have : A.IsFinite := by
      simp [J] at hf
      obtain ⟨n, ⟨i⟩⟩ := hf
      infer_instance
    have : B.IsFinite := by
      simp [J] at hf
      obtain ⟨n, ⟨i⟩⟩ := hf
      infer_instance
    constructor
    intro t b sq
    obtain ⟨k, t, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (coyoneda.obj (Opposite.op A)) hc) t
    dsimp at t sq
    simp only [fibration_iff] at hF
    have := hF k f hf
    have sq' : CommSq t f (terminal.from _) (terminal.from _) := ⟨by simp⟩
    exact ⟨⟨{ l := sq'.lift ≫ c.ι.app k }⟩⟩

namespace W

variable (J : Type*) [Category J]

lemma isStableUnderColimitsOfShape [Small.{u} J] [LocallySmall.{u} J]  [IsFiltered J] :
    W.{u}.IsStableUnderColimitsOfShape J := by
  intro F₁ F₂ c₁ c₂ hc₁ hc₂ f hf
  have (j) := (hf j).isFibrant_src
  have (j) := (hf j).isFibrant_tgt
  have : IsFibrant c₁.pt := of_isColimit hc₁
  have : IsFibrant c₂.pt := of_isColimit hc₂
  generalize hφ : hc₁.desc { ι := f ≫ c₂.ι } = φ
  dsimp at φ
  replace hf (j) := hf j
  -- use a characterization using pullback squares instead
  simp only [W_iff] at hf ⊢
  sorry

end W

end KanComplex

end SSet
