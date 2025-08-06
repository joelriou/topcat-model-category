import TopCatModelCategory.SSet.Pairing

universe v u

open CategoryTheory Simplicial

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

structure PairingCore where
  ι : Type v
  d (s : ι) : ℕ
  type₁ (s : ι) : X _⦋d s + 1⦌
  type₂ (s : ι) : X _⦋d s⦌
  nonDegenerate₁ (s : ι) : type₁ s ∈ X.nonDegenerate _
  nonDegenerate₂ (s : ι) : type₂ s ∈ X.nonDegenerate _
  notMem₁ (s : ι) : type₁ s ∉ A.obj _
  notMem₂ (s : ι) : type₂ s ∉ A.obj _
  index (s : ι) : Fin (d s)
  δ_type₁ (s : ι) : X.δ (index s) (type₁ s) = type₂ s
  injective_type₁ {s t : ι} (h : S.mk (type₁ s) = S.mk (type₁ t)) : s = t
  injective_type₂ {s t : ι} (h : S.mk (type₂ s) = S.mk (type₂ t)) : s = t
  type₁_neq_type₂ (s t : ι) : S.mk (type₁ s) ≠ S.mk (type₂ t)
  surjective' (x : A.N) :
    ∃ (s : ι), x.toS = S.mk (type₁ s) ∨ x.toS = S.mk (type₂ s)

namespace PairingCore

variable {A} (h : A.PairingCore)

@[simps!]
def type₁N (s : h.ι) : A.N :=
  Subcomplex.N.mk (h.type₁ s) (h.nonDegenerate₁ s) (h.notMem₁ s)

@[simps!]
def type₂N (s : h.ι) : A.N :=
  Subcomplex.N.mk (h.type₂ s) (h.nonDegenerate₂ s) (h.notMem₂ s)

lemma injective_type₁N : Function.Injective h.type₁N :=
  fun _ _ hst ↦ h.injective_type₁ (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

lemma injective_type₂N : Function.Injective h.type₂N :=
  fun _ _ hst ↦ h.injective_type₂ (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

lemma surjective (x : A.N) :
    ∃ (s : h.ι), x = h.type₁N s ∨ x = h.type₂N s := by
  obtain ⟨s, _ | _⟩ := h.surjective' x
  · exact ⟨s, Or.inl (by ext; assumption)⟩
  · exact ⟨s, Or.inr (by ext; assumption)⟩

def I : Set A.N := Set.range h.type₁N

def II : Set A.N := Set.range h.type₂N

@[simps! apply_coe]
noncomputable def equivI : h.ι ≃ h.I := Equiv.ofInjective _ h.injective_type₁N

@[simps! apply_coe]
noncomputable def equivII : h.ι ≃ h.II := Equiv.ofInjective _ h.injective_type₂N

@[simps I II]
noncomputable def pairing : A.Pairing where
  I := h.I
  II := h.II
  inter := by
    ext s
    simp only [I, II, Set.mem_inter_iff, Set.mem_range, Set.mem_empty_iff_false, iff_false, not_and,
      not_exists, forall_exists_index]
    rintro t rfl s
    rw [Subcomplex.N.ext_iff, SSet.N.ext_iff]
    exact (h.type₁_neq_type₂ t s).symm
  union := by
    ext s
    have := h.surjective s
    simp only [I, II, Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    aesop
  p := h.equivII.symm.trans h.equivI

@[simp]
lemma pairing_p_type₁N (x : h.ι) :
    DFunLike.coe (α := h.II) (β := fun _ ↦ h.I)
      (h.pairing.p) (h.equivII x) = h.equivI x := by
  simp [pairing]

@[simp]
lemma pairing_p_symm_type₁N (x : h.ι) :
    DFunLike.coe (α := h.I) (β := fun _ ↦ h.II)
      h.pairing.p.symm (h.equivI x) = h.equivII x := by
  simp [pairing]

end PairingCore

end Subcomplex

end SSet
