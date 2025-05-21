import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X Y Z : SSet.{u}}

def π₀Rel (x₀ x₁ : X _⦋0⦌) : Prop :=
  ∃ (e : X _⦋1⦌), X.δ 1 e = x₀ ∧ X.δ 0 e = x₁

variable (X) in
def π₀ : Type u := Quot (π₀Rel (X := X))

def π₀.mk : X _⦋0⦌ → X.π₀ := Quot.mk _

lemma π₀.mk_surjective : Function.Surjective (π₀.mk (X := X)) := Quot.mk_surjective

lemma π₀.sound {x₀ x₁ : X _⦋0⦌} (e : X _⦋1⦌) (h₀ : X.δ 1 e = x₀) (h₁ : X.δ 0 e = x₁) :
    π₀.mk x₀ = π₀.mk x₁ :=
  Quot.sound ⟨e, h₀, h₁⟩

def mapπ₀ (f : X ⟶ Y) : π₀ X → π₀ Y :=
  Quot.lift (fun x ↦ π₀.mk (f.app _ x)) (by
    rintro _ _ ⟨e, rfl, rfl⟩
    apply π₀.sound (f.app _ e)
    all_goals simp only [δ_naturality_apply])

@[simp]
lemma mapπ₀_mk (f : X ⟶ Y) (x₀ : X _⦋0⦌) : mapπ₀ f (π₀.mk x₀) = π₀.mk (f.app _ x₀) := rfl

@[simp]
lemma mapπ₀_id_apply (x : π₀ X) : mapπ₀ (𝟙 X) x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [mapπ₀_mk, NatTrans.id_app, types_id_apply]

@[simp]
lemma mapπ₀_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (x : π₀ X) :
    mapπ₀ (f ≫ g) x = mapπ₀ g (mapπ₀ f x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  simp

end SSet
