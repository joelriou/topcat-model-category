import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import TopCatModelCategory.SSet.StandardSimplex

universe u

open CategoryTheory Simplicial Limits

lemma SimplexCategory.isIso_iff_len_eq_of_epi {n m : SimplexCategory} (f : n ⟶ m) [Epi f] :
    IsIso f ↔ n.len = m.len := by
  have hf := len_le_of_epi (f := f) inferInstance
  refine ⟨fun _ ↦ le_antisymm (len_le_of_mono (f := f) inferInstance) hf, fun h ↦ ?_⟩
  obtain rfl : n = m := by aesop
  have h := (epi_iff_surjective (f := f)).1 inferInstance
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], h⟩

namespace SSet

variable (X : SSet.{u})

def N : Type u := Sigma (fun (n : ℕ) ↦ X.nonDegenerate n)

namespace N

variable {X}

instance : LE X.N where
  le x y := Subcomplex.ofSimplex x.2.1 ≤ Subcomplex.ofSimplex y.2.1

lemma le_iff {x y : X.N} : x ≤ y ↔ Subcomplex.ofSimplex x.2.1 ≤ Subcomplex.ofSimplex y.2.1 :=
  Iff.rfl

lemma le_iff_exists {x y : X.N} :
    x ≤ y ↔ ∃ (f : ⦋x.1⦌ ⟶ ⦋y.1⦌) (_ : Mono f), X.map f.op y.2 = x.2 := by
  simp only [le_iff, CategoryTheory.Subpresheaf.ofSection_le_iff,
    Subcomplex.mem_ofSimplex_obj_iff]
  refine ⟨?_, by tauto⟩
  rintro ⟨f, hf⟩
  refine ⟨f, ?_, hf⟩
  have : IsIso (factorThruImage f) := by
    rw [SimplexCategory.isIso_iff_len_eq_of_epi]
    obtain h | h := (SimplexCategory.len_le_of_epi
      (f := factorThruImage f) inferInstance).eq_or_lt
    · exact h.symm
    · exfalso
      apply (mem_nonDegenerate_iff_not_mem_degenerate _ _).1 x.2.2
      rw [mem_degenerate_iff]
      refine ⟨_, h, factorThruImage f, inferInstance, ?_⟩
      rw [← image.fac f, op_comp, FunctorToTypes.map_comp_apply] at hf
      rw [← hf]
      apply Set.mem_range_self
  have := isIso_of_mono_of_epi (factorThruImage f)
  rw [← image.fac f]
  infer_instance

lemma le_of_le {x y : X.N} (h : x ≤ y) : x.1 ≤ y.1 := by
  rw [le_iff_exists] at h
  obtain ⟨f, hf, _⟩ := h
  exact SimplexCategory.len_le_of_mono hf

instance : PartialOrder X.N where
  le_refl x := by simp only [le_iff, le_refl]
  le_antisymm := by
    rintro ⟨n₁, x₁⟩ ⟨n₂, x₂⟩ h h'
    obtain rfl : n₁ = n₂ := le_antisymm (le_of_le h) (le_of_le h')
    rw [le_iff_exists] at h
    obtain ⟨f, hf, h⟩ := h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    aesop
  le_trans _ _ _ h h' := by
    simp only [le_iff] at h h' ⊢
    exact h.trans h'

end N

@[simps]
def orderEmbeddingN : X.N ↪o X.Subcomplex where
  toFun x := Subcomplex.ofSimplex x.2.1
  inj' _ _ h := by
    dsimp at h
    apply le_antisymm <;> rw [N.le_iff, h]
  map_rel_iff' := Iff.rfl

@[simps! obj]
def functorN : X.N ⥤ SSet.{u} :=
  X.orderEmbeddingN.monotone.functor ⋙ Subcomplex.toPresheafFunctor

variable {X} in
@[simp]
lemma functorN_map {x₁ x₂ : X.N} (f : x₁ ⟶ x₂) :
    X.functorN.map f = Subcomplex.homOfLE (X.orderEmbeddingN.monotone (leOfHom f)) := rfl

@[simps]
def coconeN : Cocone X.functorN where
  pt := X
  ι := { app _ := Subcomplex.ι _ }

--def isColimitCoconeN : IsColimit X.coconeN := sorry

end SSet
