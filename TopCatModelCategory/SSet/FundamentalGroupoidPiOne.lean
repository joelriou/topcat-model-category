import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.PiZero

universe u

open CategoryTheory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen

namespace SSet

variable {X Y : SSet.{u}}

namespace KanComplex

namespace FundamentalGroupoid

def toπ₀ (x : FundamentalGroupoid X) : π₀ X := π₀.mk x.pt

lemma toπ₀_surjective : Function.Surjective (toπ₀ (X := X)) := by
  intro p
  obtain ⟨_, rfl⟩ := p.mk_surjective
  exact ⟨_, rfl⟩

@[simp]
lemma toπ₀_mk (x : X _⦋0⦌) : toπ₀ (.mk x) = .mk x := rfl

variable [IsFibrant X]

lemma congr_toπ₀_of_hom {x y : FundamentalGroupoid X} (f : x ⟶ y) :
    toπ₀ x = toπ₀ y := by
  obtain ⟨f, rfl⟩ := homMk_surjective f
  apply π₀.sound (yonedaEquiv f.map)
  · -- this is suboptimal...
    simp only [← f.comm₀']
    dsimp only [SimplicialObject.δ]
    rw [← yonedaEquiv_map_comp]
    dsimp [yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex, uliftFunctor]
    apply congr_arg
    ext i
    fin_cases i
    rfl
  · simp only [← f.comm₁']
    dsimp only [SimplicialObject.δ]
    rw [← yonedaEquiv_map_comp]
    dsimp [yonedaEquiv, yonedaCompUliftFunctorEquiv, stdSimplex, uliftFunctor]
    apply congr_arg
    ext i
    fin_cases i
    rfl

lemma toπ₀_eq_toπ₀_iff (x y : FundamentalGroupoid X) :
    toπ₀ x = toπ₀ y ↔ Nonempty (x ≅ y) := by
  refine ⟨fun h ↦ ?_, fun ⟨f⟩ ↦ congr_toπ₀_of_hom f.hom⟩
  obtain ⟨x, rfl⟩ := objEquiv.symm.surjective x
  obtain ⟨y, rfl⟩ := objEquiv.symm.surjective y
  simp only [objEquiv, Equiv.coe_fn_symm_mk, toπ₀_mk] at h
  replace h := Quot.eqvGen_exact h
  induction h with
  | rel x y r =>
    obtain ⟨e, hx, hy⟩ := r
    let f : mk x ⟶ mk y := homMk (.mk (yonedaEquiv.symm e)
      (yonedaEquiv.injective (by simp [← hx, ← yonedaEquiv_symm_δ]))
      (yonedaEquiv.injective (by simp [← hy, ← yonedaEquiv_symm_δ])))
    exact ⟨asIso f⟩
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ e => exact ⟨e.some.symm⟩
  | trans _ _ _ _ _ e₁ e₂ => exact ⟨e₁.some.trans e₂.some⟩

lemma π₀_mk_eq_π₀_mk_iff (x y : X _⦋0⦌) :
    π₀.mk x = π₀.mk y ↔ Nonempty (mk x ≅ mk y) := by
  apply toπ₀_eq_toπ₀_iff

section

variable (f : X ⟶ Y) [IsFibrant Y]

lemma mapπ₀_surjective_iff :
    Function.Surjective (mapπ₀ f) ↔
      (mapFundamentalGroupoid f).EssSurj := by
  constructor
  · refine fun hf ↦ ⟨fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hf (π₀.mk y.pt)
    obtain ⟨x, rfl⟩ := x.mk_surjective
    exact ⟨.mk x, by rwa [← toπ₀_eq_toπ₀_iff]⟩
  · intro _ y
    obtain ⟨y, rfl⟩ := y.mk_surjective
    obtain ⟨x, ⟨e⟩⟩ :
        ∃ (x : X _⦋0⦌), Nonempty ((mapFundamentalGroupoid f).obj (.mk x) ≅ .mk y) :=
      ⟨_, ⟨(mapFundamentalGroupoid f).objObjPreimageIso (.mk y)⟩⟩
    exact ⟨π₀.mk x, congr_toπ₀_of_hom e.hom⟩

lemma mapπ₀_injective_iff :
    Function.Injective (mapπ₀ f) ↔
      (∀ (x x' : FundamentalGroupoid X)
        (_ : (mapFundamentalGroupoid f).obj x ≅ (mapFundamentalGroupoid f).obj x'),
        Nonempty (x ≅ x')) := by
  constructor
  · intro hf x x' e
    rw [← toπ₀_eq_toπ₀_iff]
    obtain ⟨x, rfl⟩ := objEquiv.symm.surjective x
    obtain ⟨x', rfl⟩ := objEquiv.symm.surjective x'
    apply hf
    simp only [objEquiv, Equiv.coe_fn_symm_mk, toπ₀_mk, mapπ₀_mk, π₀_mk_eq_π₀_mk_iff]
    exact ⟨e⟩
  · intro hf x x' h
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨x', rfl⟩ := x'.mk_surjective
    simp only [mapπ₀_mk] at h
    rw [π₀_mk_eq_π₀_mk_iff] at h ⊢
    exact hf _ _ h.some

lemma mapπ₀_injective_of_full [(mapFundamentalGroupoid f).Full] :
    Function.Injective (mapπ₀ f) := by
  rw [mapπ₀_injective_iff]
  intro x x' e
  exact ⟨asIso ((mapFundamentalGroupoid f).map_surjective e.hom).choose⟩

end

end FundamentalGroupoid

end KanComplex

end SSet
