import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

universe u

open CategoryTheory Opposite Simplicial

@[simp]
lemma SimplexCategory.mkOfSucc_zero :
    mkOfSucc (0 : Fin 1) = 𝟙 _ := by
  ext i
  fin_cases i <;> rfl

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y)

lemma σ_injective {n : ℕ} (i : Fin (n + 1)) : Function.Injective (X.σ i) := fun x₁ x₂ h ↦ by
  rw [← δ_comp_σ_self_apply i x₁, ← δ_comp_σ_self_apply i x₂, h]

lemma mono_iff_of_strictSegal [StrictSegal X] :
    Mono f ↔ Function.Injective (f.app (op (.mk 1))) := by
  rw [NatTrans.mono_iff_mono_app]
  simp only [mono_iff_injective]
  refine ⟨fun hf ↦ hf _, fun hf ⟨k⟩ ↦ ?_⟩
  induction' k using SimplexCategory.rec with k
  obtain _ | k := k
  · intro x y h
    apply σ_injective 0
    apply StrictSegal.spineInjective
    ext i
    fin_cases i
    apply hf
    dsimp [StrictSegal.spineEquiv]
    simp only [Fin.isValue, SimplexCategory.mkOfSucc_zero, op_id, FunctorToTypes.map_id_apply,
      σ_naturality_apply, h]
  · intro x y h
    apply StrictSegal.spineInjective
    ext i
    apply hf
    dsimp [StrictSegal.spineEquiv]
    simp only [FunctorToTypes.naturality, h]

namespace standardSimplex

instance (n i : ℕ) : DFunLike (Δ[n] _[i]) (Fin (i + 1)) (fun _ ↦ Fin (n + 1)) where
  coe x j := (objEquiv _ _ x).toOrderHom j
  coe_injective' j₁ j₂ h := by
    apply (objEquiv _ _).injective
    ext k : 3
    exact congr_fun h k

lemma monotone_apply {n i : ℕ} (x : Δ[n] _[i]) : Monotone (fun (j : Fin (i + 1)) ↦ x j) :=
  (objEquiv _ _ x).toOrderHom.monotone

@[ext]
lemma ext {n : ℕ} (x y : Δ[n] _[i]) (h : ∀ (i : Fin (i + 1)), x i = y i) : x = y := by
  apply (objEquiv _ _).injective
  ext i : 3
  apply h

@[simps]
def obj₀Equiv {n : ℕ} : Δ[n] _[0] ≃ Fin (n + 1) where
  toFun x := x 0
  invFun i := const _ i _
  left_inv x := by ext i : 1; fin_cases i; rfl
  right_inv _ := rfl

instance (n : SimplexCategory) : (standardSimplex.{u}.obj n).StrictSegal where
  spineToSimplex {j v} := objMk
    { toFun i := obj₀Equiv (v.vertex i)
      monotone' j₁ j₂ h := by
        dsimp [obj₀Equiv]
        sorry }
  spine_spineToSimplex := sorry
  spineToSimplex_spine := sorry

@[ext]
lemma path_ext {n i : ℕ} {x y : Path Δ[n] i} (h : x.vertex = y.vertex) : x = y := by
  obtain ⟨v, a, h₁, h₂⟩ := x
  obtain ⟨w, b, h₃, h₄⟩ := y
  obtain rfl := h
  dsimp at h₃ h₄
  simp only [Path.mk.injEq, true_and]
  ext j k : 2
  fin_cases k
  · exact (DFunLike.congr_fun (h₁ j) 0).trans (DFunLike.congr_fun (h₃ j) 0).symm
  · exact (DFunLike.congr_fun (h₂ j) 0).trans (DFunLike.congr_fun (h₄ j) 0).symm

lemma mono_iff (n : ℕ) (f : Δ[n] ⟶ Y) :
    Mono f ↔ Function.Injective (f.app (op [0])):= by
  constructor
  · intro hf
    rw [NatTrans.mono_iff_mono_app] at hf
    simp only [mono_iff_injective] at hf
    apply hf
  · intro hf
    rw [mono_iff_of_strictSegal]
    intro x₁ x₂ h
    apply StrictSegal.spineInjective
    ext i : 2
    apply hf
    dsimp [StrictSegal.spineEquiv, spine]
    simp only [FunctorToTypes.naturality, h]

end standardSimplex

end SSet
