import TopCatModelCategory.SSet.PairingCore
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.SSet.NonDegenerateProdSimplex

open CategoryTheory Simplicial MonoidalCategory Opposite

universe u

namespace SSet

lemma mem_horn_iff_notMem_range {n d : ℕ} (s : Δ[n] _⦋d⦌) (i : Fin (n + 1)) :
    s ∈ (horn _ i).obj _ ↔ ∃ (j : Fin (n + 1)) (_ : j ≠ i), j ∉ Set.range s := by
  rw [horn_eq_iSup]
  simp

lemma mem_boundary_iff_notMem_range {n d : ℕ} (s : Δ[n] _⦋d⦌) :
    s ∈ (boundary n).obj _ ↔ ∃ (j : Fin (n + 1)), j ∉ Set.range s := by
  rw [boundary_eq_iSup]
  simp

namespace prodStdSimplex

lemma nonDegenerate_δ {m n d : ℕ} {x : (Δ[m] ⊗ Δ[n] : SSet.{u}) _⦋d + 1⦌}
    (hx : x ∈ SSet.nonDegenerate _ _) (i : Fin (d + 2)) :
      (Δ[m] ⊗ Δ[n]).δ i x ∈ SSet.nonDegenerate _ _ := by
  rw [objEquiv_nonDegenerate_iff] at hx ⊢
  exact hx.comp (by
    rw [← SimplexCategory.mono_iff_injective]
    dsimp
    infer_instance)

lemma isUniquelyCodimOneFace {m n d : ℕ} {x : (Δ[m] ⊗ Δ[n] : SSet.{u}) _⦋d + 1⦌}
    (hx : x ∈ SSet.nonDegenerate _ _) (i : Fin (d + 2)) :
    IsUniquelyCodimOneFace ((Δ[m] ⊗ Δ[n]).δ i x) x :=
  .mk (⟨i, rfl, fun j hij ↦ SimplexCategory.δ_injective (by
    rw [objEquiv_nonDegenerate_iff] at hx
    ext k : 3
    exact hx (DFunLike.congr_fun (congr_arg objEquiv.toFun hij) k))⟩)

variable {m : ℕ} (k : Fin (m + 1)) (n : ℕ)

namespace pairingCore

@[ext]
structure ι where
  d : ℕ
  simplex : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}).nonDegenerate (d + 1)
  notMem₁ : simplex.1 ∉ ((horn (m + 1) k.castSucc).unionProd (boundary n)).obj _
  l : Fin (d + 1)
  hl₀ : simplex.1.1 l.castSucc = k.castSucc
  hl₁ : simplex.1.1 l.succ = k.succ
  hl₂ : simplex.1.2 l.succ = simplex.1.2 l.castSucc

namespace ι

variable {k n} (s : ι.{u} k n)

abbrev type₁ : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋s.d + 1⦌ := s.simplex.1

@[simp]
lemma type₁_left_castSucc : s.type₁.1 s.l.castSucc = k.castSucc := s.hl₀

@[simp]
lemma type₁_left_succ : s.type₁.1 s.l.succ = k.succ := s.hl₁

@[simp]
lemma type₁_right_succ : s.type₁.2 s.l.succ = s.type₁.2 s.l.castSucc := s.hl₂

abbrev index : Fin (s.d + 2) := s.l.castSucc

noncomputable abbrev type₂ : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋s.d⦌ :=
  (Δ[m + 1] ⊗ Δ[n] : SSet.{u}).δ s.index s.type₁

lemma nonDegenerate₁ : s.type₁ ∈ SSet.nonDegenerate _ _ := s.simplex.2

lemma nonDegenerate₂ : s.type₂ ∈ SSet.nonDegenerate _ _ :=
  nonDegenerate_δ s.nonDegenerate₁ _

lemma notMem_left : s.type₁.1 ∉ (horn (m + 1) k.castSucc).obj _ := by
  have := s.notMem₁
  simp [Subcomplex.unionProd, Set.prod] at this
  tauto

lemma notMem_right : s.type₁.2 ∉ (boundary n).obj _ := by
  have := s.notMem₁
  simp [Subcomplex.unionProd, Set.prod] at this
  tauto

lemma mem_range_left (j : Fin (m + 2)) (hj : j ≠ k.castSucc) :
    j ∈ Set.range s.type₁.1 := by
  have := s.notMem_left
  simp [mem_horn_iff_notMem_range] at this
  tauto

lemma mem_range_right (j : Fin (n + 1)) : j ∈ Set.range s.type₁.2 := by
  have := s.notMem_right
  simp [mem_boundary_iff_notMem_range] at this
  tauto

lemma type₁_left_le_iff (i : Fin (s.d + 2)) :
    s.type₁.1 i ≤ k.castSucc ↔ i ≤ s.l.castSucc := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra!
    rw [Fin.castSucc_lt_iff_succ_le] at this
    replace this := stdSimplex.monotone_apply s.type₁.1 this
    simp only [type₁_left_succ, ← Fin.castSucc_lt_iff_succ_le] at this
    omega
  · rw [← s.type₁_left_castSucc]
    exact stdSimplex.monotone_apply s.type₁.1 h

@[simp]
lemma objEquiv_type₂_apply (i : Fin (s.d + 1)) :
    objEquiv s.type₂ i = objEquiv s.type₁ (s.index.succAbove i) := rfl

lemma type₂_left_apply (i : Fin (s.d + 1)) :
    s.type₂.1 i = s.type₁.1 (s.index.succAbove i) := rfl

lemma type₂_right_apply (i : Fin (s.d + 1)) :
    s.type₂.2 i = s.type₁.2 (s.index.succAbove i) := rfl

lemma type₂_left_le_iff (i : Fin (s.d + 1)) :
    s.type₂.1 i ≤ k.castSucc ↔ i < s.l := by
  rw [type₂_left_apply, type₁_left_le_iff]
  by_cases hi : i < s.l
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa),
      Fin.castSucc_le_castSucc_iff]
    simp [hi]
    omega
  · simp only [not_lt] at hi
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa),
      Fin.succ_le_castSucc_iff]

lemma le_type₂_left_le_iff (i : Fin (s.d + 1)) :
    k.succ ≤ s.type₂.1 i ↔ s.l ≤ i := by
  rw [← not_lt, ← Fin.le_castSucc_iff, type₂_left_le_iff, not_lt]

lemma notMem₂ :
    s.type₂ ∉ ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).obj _:= by
  intro h
  rw [Subcomplex.mem_unionProd_iff,
    mem_horn_iff_notMem_range,
    mem_boundary_iff_notMem_range] at h
  obtain ⟨j, h₁, h₂⟩ | ⟨j, h⟩ := h
  · obtain ⟨i, hi⟩ := s.mem_range_left j h₁
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove s.index i
    · exact h₁ (by rw [← hi, type₁_left_castSucc])
    · exact h₂ ⟨i, by rwa [← type₂_left_apply] at hi⟩
  · obtain ⟨i, hi⟩ := s.mem_range_right j
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove s.index i
    · refine h ⟨s.l, ?_⟩
      rw [← hi, type₂_right_apply, Fin.succAbove_castSucc_self, type₁_right_succ]
    · exact h ⟨i, by rwa [type₂_right_apply]⟩

noncomputable abbrev nonDeg : (Δ[m + 1] ⊗ Δ[n]).N := N.mk s.simplex.1 s.simplex.2

variable {d : ℕ} (hd : s.d = d)

@[simps d simplex_coe]
noncomputable def cast : ι k n where
  d := d
  simplex := ⟨_, (s.nonDeg.cast (by simp [hd])).2⟩
  l := Fin.cast (by omega) s.l
  notMem₁ := by
    subst hd
    exact s.notMem₁
  hl₀ := by
    subst hd
    exact s.hl₀
  hl₁ := by
    subst hd
    exact s.hl₁
  hl₂ := by
    subst hd
    exact s.hl₂

lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end ι

namespace surjective'

variable {n} (x : ((Λ[m + 1, k.castSucc] : Subcomplex.{u} _).unionProd ∂Δ[n]).N)
  {d : ℕ} (hd : x.dim = d)

def IsIndexI (l : Fin d) : Prop :=
  (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
  (x.cast hd).simplex.1 l.succ = k.succ ∧
  (x.cast hd).simplex.2 l.succ = (x.cast hd).simplex.2 l.castSucc

end surjective'

namespace surjective

variable {n} {d : ℕ}
  (x : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌)
  (hx : x ∈ SSet.nonDegenerate _ _)
  (hx' : x ∉ ((Λ[m + 1, k.castSucc]).unionProd ∂Δ[n]).obj _)

def IsIndexI (l : Fin d) : Prop :=
    x.1 l.castSucc = k.castSucc ∧ x.1 l.succ = k.succ ∧
      x.2 l.succ = x.2 l.castSucc

def finset : Finset (Fin (d + 1)) := { l : _ | x.1 l = k.succ }

@[simp]
lemma mem_finset_iff (l : Fin (d + 1)) :
    l ∈ finset k x ↔ x.1 l = k.succ := by
  simp [finset]

include hx' in
lemma nonempty_finset : Nonempty (finset k x) := by
  have hx' : x.1 ∉ (horn _ k.castSucc).obj _ := by
    simp [Subcomplex.unionProd, Set.prod] at hx'
    exact hx'.2
  simp only [mem_horn_iff_notMem_range, Set.mem_range, not_exists, ne_eq, exists_prop, not_and,
    not_forall, Decidable.not_not] at hx'
  obtain ⟨i, hi⟩ := hx' k.succ (fun h ↦ by simp [Fin.ext_iff] at h)
  exact ⟨i, by simpa⟩

end surjective

variable {k n}

lemma type₁_injective : Function.Injective (fun (s : ι.{u} k n) ↦ S.mk s.type₁) := by
  intro s t h
  dsimp at h
  generalize hds : s.d = d
  have hdt : t.d = d := by
    have := S.dim_eq_of_eq h
    dsimp at this
    omega
  sorry

lemma type₂_injective : Function.Injective (fun (s : ι.{u} k n) ↦ S.mk s.type₂) := by
  sorry


end pairingCore

open pairingCore

@[simps]
noncomputable def pairingCore :
    ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).PairingCore where
  ι := ι k n
  d s := s.d
  type₁ s := s.type₁
  index s := s.index
  nonDegenerate₁ s := s.nonDegenerate₁
  nonDegenerate₂ s := s.nonDegenerate₂
  notMem₁ s := s.notMem₁
  notMem₂ s := s.notMem₂
  injective_type₁ h := type₁_injective h
  injective_type₂ h := type₂_injective h
  type₁_neq_type₂ _ _ hst := by sorry
  surjective' x := by
    obtain ⟨d', x, hx, hx', rfl⟩ := x.mk_surjective
    by_cases h : ∃ i, surjective.IsIndexI k x i
    · obtain ⟨l, hl⟩ := h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_one.2 l.pos
      exact ⟨{
        d := d
        simplex := ⟨x, hx⟩
        notMem₁ := hx'
        l := l
        hl₀ := hl.1
        hl₁ := hl.2.1
        hl₂ := hl.2.2}, Or.inl rfl⟩
    · sorry

instance : (pairingCore k n).IsProper where
  isUniquelyCodimOneFace s := isUniquelyCodimOneFace s.nonDegenerate₁ _

lemma isInner_pairingCore (k : Fin m) :
    (pairingCore k.succ n).IsInner := by
  intro s
  refine ⟨fun hs ↦ ?_, s.l.castSucc_lt_last.ne⟩
  · dsimp at s hs
    simp only [Fin.castSucc_eq_zero_iff] at hs
    have h₁ := s.type₁_left_castSucc
    rw [hs, Fin.castSucc_zero] at h₁
    obtain ⟨i, hi⟩ := s.mem_range_left 0 (fun h ↦ by simp [Fin.ext_iff] at h)
    have h₂ := stdSimplex.monotone_apply s.type₁.1 (Fin.zero_le i)
    simp [Fin.ext_iff, hi, h₁] at h₂

end prodStdSimplex

end SSet
