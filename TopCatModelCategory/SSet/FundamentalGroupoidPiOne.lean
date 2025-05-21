import TopCatModelCategory.SSet.FundamentalGroupoid
import TopCatModelCategory.SSet.HomotopyGroup
import TopCatModelCategory.SSet.PiZero

universe u

open CategoryTheory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen MonoidalCategory

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

@[simps apply_map symm_apply_map]
def edgeEquiv {x : X _⦋0⦌} :
    Edge (.mk x) (.mk x) ≃ X.PtSimplex 1 x where
  toFun e := { map := e.map }
  invFun s := { map := s.map }
  left_inv _ := rfl
  right_inv _ := rfl

def homEquiv {x : X _⦋0⦌} : (mk x ⟶ mk x) ≃ π 1 X x where
  toFun := Quot.lift (fun e ↦ π.mk (edgeEquiv e)) (fun e₁ e₂ ⟨h⟩ ↦ by
    rw [π.mk_eq_mk_iff]
    refine ⟨PtSimplex.Homotopy.relStruct₀ ?_⟩
    exact
      { h := h.h
        h₀ := h.h₀
        h₁ := h.h₁
        rel := by apply boundary₁.hom_ext_rightTensor <;> simp })
  invFun := Quot.lift (fun s ↦ homMk (edgeEquiv.symm s)) (fun s₁ s₂ ⟨h⟩ ↦ by
    apply homMk_eq_of_homotopy
    exact
      { h := h.h
        h₀ := h.h₀
        h₁ := h.h₁
        rel := by apply boundary₁.hom_ext_rightTensor <;> simp })
  left_inv e := by
    obtain ⟨e, rfl⟩ := homMk_surjective e
    rfl
  right_inv s := by
    obtain ⟨s, rfl⟩ := s.mk_surjective
    rfl

@[simps]
def Edge.CompStruct.mulStruct {x : X _⦋0⦌} {f g fg : Edge (.mk x) (.mk x)}
    (h : Edge.CompStruct f g fg) :
    PtSimplex.MulStruct (edgeEquiv f) (edgeEquiv g) (edgeEquiv fg) 0 where
  map := h.map
  δ_map_of_gt j hj := by
    have : 2 < j.1 := by simpa [Fin.lt_iff_val_lt_val] using hj
    omega

lemma homEquiv_comp {x : X _⦋0⦌} (f g : mk x ⟶ mk x) :
    homEquiv (f ≫ g) = homEquiv f * homEquiv g := by
  obtain ⟨f, rfl⟩ := homMk_surjective f
  obtain ⟨g, rfl⟩ := homMk_surjective g
  exact (π.mul_eq_of_mulStruct (Edge.compStruct f g).mulStruct).symm

end FundamentalGroupoid

end KanComplex

end SSet
