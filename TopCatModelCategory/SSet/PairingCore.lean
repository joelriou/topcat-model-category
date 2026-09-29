module

public import TopCatModelCategory.SSet.Pairing

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

structure PairingCore where
  ι : Type v
  d (s : ι) : ℕ
  type₁ (s : ι) : X _⦋d s + 1⦌
  index (s : ι) : Fin (d s + 2)
  nonDegenerate₁ (s : ι) : type₁ s ∈ X.nonDegenerate _
  nonDegenerate₂ (s : ι) : X.δ (index s) (type₁ s) ∈ X.nonDegenerate _
  notMem₁ (s : ι) : type₁ s ∉ A.obj _
  notMem₂ (s : ι) : X.δ (index s) (type₁ s) ∉ A.obj _
  injective_type₁ {s t : ι} (h : S.mk (type₁ s) = S.mk (type₁ t)) : s = t
  injective_type₂ {s t : ι}
    (h : S.mk (X.δ (index s) (type₁ s)) = S.mk (X.δ (index t) (type₁ t))) : s = t
  type₁_neq_type₂ (s t : ι) : S.mk (type₁ s) ≠ S.mk (X.δ (index t) (type₁ t))
  surjective' (x : A.N) :
    ∃ (s : ι), x.toS = S.mk (type₁ s) ∨ x.toS = S.mk (X.δ (index s) (type₁ s))

namespace PairingCore

variable {A} (h : A.PairingCore)

@[simps!]
def type₁N (s : h.ι) : A.N :=
  Subcomplex.N.mk (h.type₁ s) (h.nonDegenerate₁ s) (h.notMem₁ s)

@[simps!]
def type₂N (s : h.ι) : A.N :=
  Subcomplex.N.mk (X.δ (h.index s) (h.type₁ s)) (h.nonDegenerate₂ s)
    (h.notMem₂ s)

lemma injective_type₁N : Function.Injective h.type₁N :=
  fun _ _ hst ↦ h.injective_type₁ (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

lemma injective_type₂N : Function.Injective h.type₂N :=
  fun s t hst ↦ h.injective_type₂ (by rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff] at hst)

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

@[simp]
lemma pairing_p_type₁N' (x : h.ι) :
    DFunLike.coe (α := h.II) (β := fun _ ↦ h.I)
      (h.pairing.p) ⟨h.type₂N x, ⟨x, rfl⟩⟩ = h.equivI x :=
  h.pairing_p_type₁N x

class IsProper where
  isUniquelyCodimOneFace (s : h.ι) :
    IsUniquelyCodimOneFace (X.δ (h.index s) (h.type₁ s)) (h.type₁ s)

lemma isUniquelyCodimOneFace [h.IsProper] (s : h.ι) :
    IsUniquelyCodimOneFace (X.δ (h.index s) (h.type₁ s)) (h.type₁ s) :=
  IsProper.isUniquelyCodimOneFace _

instance [h.IsProper] : h.pairing.IsProper where
  isUniquelyCodimOneFace := by
    rintro ⟨_, s, rfl⟩
    dsimp
    rw [pairing_p_type₁N']
    exact h.isUniquelyCodimOneFace _

lemma isUniquelyCodimOneFace_index [h.IsProper] (s : h.ι) :
    (h.isUniquelyCodimOneFace s).index = h.index s :=
  ((h.isUniquelyCodimOneFace s).index_unique rfl).symm


lemma isProper_pairing_iff : h.pairing.IsProper ↔ h.IsProper := by
  refine ⟨fun _ ↦ ⟨fun s ↦ ?_⟩, fun _ ↦ inferInstance⟩
  have := h.pairing.isUniquelyCodimOneFace (h.equivII s)
  dsimp at this ⊢
  erw [pairing_p_type₁N'] at this
  exact this

def IsInner : Prop :=
  ∀ (s : h.ι), h.index s ≠ 0 ∧ h.index s ≠ Fin.last _

@[simp]
lemma pairing_index [h.IsProper] (s : h.ι) :
    (h.pairing.isUniquelyCodimOneFace (h.equivII s)).index =
      h.index s := by
  ext
  rw [← isUniquelyCodimOneFace_index]
  apply IsUniquelyCodimOneFace.congr_index
  · simp
  · dsimp
    erw [h.pairing_p_type₁N']
    rfl

variable {h} in
lemma IsInner.pairing [h.IsProper] (H : h.IsInner) :
    (h.pairing).IsInner := by
  intro x
  obtain ⟨s, rfl⟩ := h.equivII.surjective x
  simpa using H s

def AncestralRel (s t : h.ι) : Prop :=
  s ≠ t ∧ IsFace (X.δ (h.index s) (h.type₁ s)) (h.type₁ t)

lemma ancestralRel_iff (s t : h.ι) :
    h.AncestralRel s t ↔ h.pairing.AncestralRel (h.equivII s) (h.equivII t) := by
  dsimp [AncestralRel, Pairing.AncestralRel]
  rw [pairing_p_type₁N]
  simp

class IsRegular extends h.IsProper where
  wf : WellFounded h.AncestralRel

instance [h.IsRegular] : h.pairing.IsRegular where
  wf := by
    have := IsRegular.wf (h := h)
    rw [wellFounded_iff_isEmpty_descending_chain] at this ⊢
    exact ⟨fun ⟨f, hf⟩ ↦ this.false
      ⟨fun n ↦ h.equivII.symm (f n), fun n ↦ by simpa [ancestralRel_iff] using hf n⟩⟩

lemma isRegular_pairing_iff : h.pairing.IsRegular ↔ h.IsRegular := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : h.IsProper := by
    rw [← isProper_pairing_iff]
    infer_instance
  constructor
  have := h.pairing.wf
  rw [wellFounded_iff_isEmpty_descending_chain, isEmpty_iff] at this ⊢
  rintro ⟨f, hf⟩
  exact this ⟨fun n ↦ h.equivII (f n), fun n ↦ by simpa [ancestralRel_iff] using hf n⟩

lemma isRegular_iff [h.IsProper] :
    h.IsRegular ↔
      ∃ (φ : h.ι → ℕ),
        ∀ (x y : h.ι) (_ : h.d x = h.d y), h.AncestralRel x y → φ x < φ y := by
  rw [← isRegular_pairing_iff, Pairing.isRegular_iff]
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨fun s ↦ φ (h.equivII s), fun s t h₁ h₂ ↦
      hφ (h.equivII s) (h.equivII t) h₁ (by simpa only [← ancestralRel_iff])⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨fun x ↦ φ (h.equivII.symm x), fun x y h₁ h₂ ↦ ?_⟩
    obtain ⟨s, rfl⟩ := h.equivII.surjective x
    obtain ⟨t, rfl⟩ := h.equivII.surjective y
    rw [← ancestralRel_iff] at h₂
    simpa using hφ _ _ h₁ h₂

end PairingCore

end Subcomplex

namespace horn

variable {n : ℕ} (i : Fin (n + 2))

@[simps]
def pairingCore : (horn (n + 1) i).PairingCore where
  ι := Unit
  d := n
  type₁ _ := yonedaEquiv (𝟙 _)
  index _ := i
  nonDegenerate₁ _ := stdSimplex.id_nonDegenerate (n + 1)
  nonDegenerate₂ _ := by
    rw [stdSimplex.mem_nonDegenerate_iff_mono]
    exact inferInstanceAs (Mono (SimplexCategory.δ i))
  notMem₁ _ := SSet.objEquiv_symm_notMem_horn_of_isIso _ _
  notMem₂ _ := (objEquiv_symm_δ_notMem_horn_iff _ _).2 rfl
  injective_type₁ := by aesop
  injective_type₂ := by aesop
  type₁_neq_type₂ _ _ := by simp
  surjective' s := by
    obtain ⟨d, x, h₁, h₂, rfl⟩ := s.mk_surjective
    obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
    rw [stdSimplex.mem_nonDegenerate_iff_mono, Equiv.apply_symm_apply] at h₁
    dsimp at f
    obtain hd | rfl := (SimplexCategory.le_of_mono f).lt_or_eq
    · rw [Nat.lt_succ] at hd
      obtain hd | rfl := hd.lt_or_eq
      · exact (h₂ (by simp [horn_obj_eq_top i (m := d) (by omega)])).elim
      · obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono f
        obtain rfl := (objEquiv_symm_δ_notMem_horn_iff _ _).1 h₂
        exact ⟨⟨⟩, Or.inr rfl⟩
    · obtain rfl := SimplexCategory.eq_id_of_mono f
      exact ⟨⟨⟩, Or.inl rfl⟩

instance : (pairingCore i).IsProper where
  isUniquelyCodimOneFace _ := .mk (⟨i, rfl, fun _ hj ↦ SimplexCategory.δ_injective (
    stdSimplex.objEquiv.symm.injective hj)⟩)

instance : (pairingCore i).IsRegular := by
  rw [Subcomplex.PairingCore.isRegular_iff]
  exact ⟨fun _ ↦ 0, fun _ _ _ h ↦ (h.1 rfl).elim⟩

noncomputable abbrev pairing := (pairingCore i).pairing

end horn

end SSet
