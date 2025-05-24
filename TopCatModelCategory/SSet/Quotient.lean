import TopCatModelCategory.SSet.Monoidal

universe u

open CategoryTheory Limits Simplicial

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

noncomputable def quotient : SSet.{u} := pushout A.ι (stdSimplex.isTerminalObj₀.from _)

noncomputable def toQuotient : X ⟶ A.quotient := pushout.inl _ _

noncomputable def quotient₀ : A.quotient _⦋0⦌ := yonedaEquiv (pushout.inr _ _)

@[reassoc (attr := simp)]
lemma ι_quotient : A.ι ≫ A.toQuotient = const A.quotient₀ := by
  dsimp [quotient, toQuotient]
  rw [pushout.condition]
  have : stdSimplex.isTerminalObj₀.from A.toSSet = const (yonedaEquiv (𝟙 _)) :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  simp only [this, const_comp]
  rfl

lemma quotient_isPushout : IsPushout A.ι (stdSimplex.isTerminalObj₀.from _)
    A.toQuotient (yonedaEquiv.symm A.quotient₀) := by
  dsimp [quotient₀]
  rw [Equiv.symm_apply_apply]
  apply IsPushout.of_hasPushout

lemma quotient_hom_ext {T : SSet.{u}} {f g : A.quotient ⟶ T}
    (h : A.toQuotient ≫ f = A.toQuotient ≫ g)
    (h₀ : f.app _ A.quotient₀ = g.app _ A.quotient₀ ) : f = g :=
  A.quotient_isPushout.hom_ext h (yonedaEquiv.injective (by simpa))

section

variable {T : SSet.{u}} (f : X ⟶ T) (t₀ : T _⦋0⦌)
    (hf : A.ι ≫ f = const t₀)

def exists_descQuotient :
    ∃ (g : A.quotient ⟶ T), A.toQuotient ≫ g = f ∧ g.app _ A.quotient₀ = t₀ := by
  obtain ⟨g, h, h₀⟩ := A.quotient_isPushout.exists_desc f (yonedaEquiv.symm t₀)
    (by simp [hf])
  exact ⟨g, h, yonedaEquiv.symm.injective (by simp [← h₀])⟩

noncomputable def descQuotient : A.quotient ⟶ T :=
  (A.exists_descQuotient f t₀ hf).choose

@[reassoc (attr := simp)]
lemma toQuotient_descQuotient : A.toQuotient ≫ A.descQuotient f t₀ hf = f :=
  (A.exists_descQuotient f t₀ hf).choose_spec.1

lemma descQuotient_app_quotient₀ :
    (A.descQuotient f t₀ hf).app _ A.quotient₀ = t₀ :=
  (A.exists_descQuotient f t₀ hf).choose_spec.2

end

end Subcomplex

end SSet
