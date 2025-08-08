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

variable {m : ℕ} (k : Fin (m + 1)) {n : ℕ}

namespace pairingCore

variable {x : ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N}

section

variable {d : ℕ} (hd : x.dim = d)

lemma mem_range_left (i : Fin (m + 2)) (hi : i ≠ k.castSucc) :
    i ∈ Set.range (x.cast hd).simplex.1 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range] at this
  tauto

lemma mem_range_right (i : Fin (n + 1)) :
    i ∈ Set.range (x.cast hd).simplex.2 := by
  subst hd
  have := x.notMem
  simp [Subcomplex.mem_unionProd_iff, mem_boundary_iff_notMem_range] at this
  tauto

def IsIndex : Fin (d + 1) → Prop :=
  Fin.cases False (fun l ↦
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
      (x.cast hd).simplex.1 l.succ = k.succ ∧
      (x.cast hd).simplex.2 l.succ =
        (x.cast hd).simplex.2 l.castSucc)

@[simp]
lemma isIndex_zero : IsIndex k hd 0 ↔ False := Iff.rfl

lemma isIndex_succ (l : Fin d) :
    IsIndex k hd l.succ ↔
    (x.cast hd).simplex.1 l.castSucc = k.castSucc ∧
      (x.cast hd).simplex.1 l.succ = k.succ ∧
      (x.cast hd).simplex.2 l.succ =
        (x.cast hd).simplex.2 l.castSucc := Iff.rfl

namespace IsIndex

variable {k hd} {l : Fin d} (hx : IsIndex k hd l.succ)

include hx

lemma left_castSucc :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    t.1 l.castSucc = k.castSucc :=
  hx.1

lemma left_succ :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    t.1 l.succ = k.succ :=
  hx.2.1

lemma right_succ :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    t.2 l.succ = t.2 l.castSucc :=
  hx.2.2

end IsIndex

noncomputable def finset :
    Finset (Fin (d + 1)) := { l : _ | (x.cast hd).simplex.1 l = k.succ }

@[simp]
lemma mem_finset_iff (l : Fin (d + 1)) :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    l ∈ finset k hd ↔ t.1 l = k.succ := by
  simp [finset]

lemma nonempty_finset : (finset k hd).Nonempty  := by
  obtain ⟨i, hi⟩ := mem_range_left k hd k.succ
    (fun h ↦ by simp [Fin.ext_iff] at h)
  exact ⟨i, by simpa using hi⟩

noncomputable def min : Fin (d + 1) := (finset k hd).min' (nonempty_finset k hd)

lemma min_left :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    t.1 (min k hd) = k.succ := by
  rw [← mem_finset_iff]
  apply Finset.min'_mem

lemma left_le_castSucc_iff (i : Fin (d + 1)) :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    t.1 i ≤ k.castSucc ↔ i < min k hd := by
  rw [← not_lt]
  conv_rhs => rw [← not_le]
  refine ⟨fun h ↦ (fun hi ↦ h ?_), fun h h' ↦ h ?_⟩
  · rw [Fin.castSucc_lt_iff_succ_le, ← min_left k hd]
    exact stdSimplex.monotone_apply _ hi
  · rw [Fin.castSucc_lt_iff_succ_le] at h'
    obtain h' | h' := h'.lt_or_eq
    · exfalso
      simp only [not_le] at h
      have := stdSimplex.monotone_apply (x.cast hd).simplex.1 h.le
      dsimp at this
      rw [min_left, ← not_lt] at this
      tauto
    · exact Finset.min'_le _ _ (by simpa using h'.symm)

namespace IsIndex

variable {k hd} {l : Fin d} (hl : IsIndex k hd l.succ)

include hl

lemma succ_le_left_iff (i : Fin (d + 1)) :
    letI t : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d⦌ := (x.cast hd).simplex
    k.succ ≤ t.1 i ↔ l.succ ≤ i := by
  refine ⟨fun hi ↦ ?_, fun hi ↦ ?_⟩
  · by_contra!
    rw [← not_lt] at hi
    apply hi
    rw [← Fin.le_castSucc_iff] at this ⊢
    conv_rhs => rw [← hl.left_castSucc]
    exact stdSimplex.monotone_apply _ this
  · rw [← hl.left_succ]
    exact stdSimplex.monotone_apply _ hi

lemma min_eq : min k hd = l.succ :=
  le_antisymm (Finset.min'_le _ _ (by simpa using hl.left_succ))
    ((Finset.le_min'_iff _ _ ).2 (fun i hi ↦ by
      rw [mem_finset_iff] at hi
      simp [← hl.succ_le_left_iff, ← hi]))

lemma unique {l' : Fin d} (hl' : IsIndex k hd l'.succ) : l = l' := by
  rw [← Fin.succ_inj, ← hl.min_eq, hl'.min_eq]

end IsIndex

end

namespace IsIndex

variable {k} {d : ℕ} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex k hd l.succ)

@[simps]
noncomputable def δ :
    ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N where
  dim := d
  simplex := (Δ[m + 1] ⊗ Δ[n]).δ l.castSucc (x.cast hd).simplex
  nonDegenerate := nonDegenerate_δ (x.cast hd).nonDegenerate _
  notMem := by
    simp [Subcomplex.mem_unionProd_iff, mem_horn_iff_notMem_range,
      mem_boundary_iff_notMem_range, stdSimplex.δ_apply]
    have := hl
    constructor
    · intro j hj
      obtain ⟨i, hi⟩ := mem_range_left k hd j hj
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · exact (hj (by rw [← hi, hl.left_castSucc])).elim
      · exact ⟨_, hi⟩
    · intro j
      obtain ⟨i, hi⟩ := mem_range_right k hd j
      dsimp at hi
      obtain rfl | ⟨i, rfl⟩ := Fin.eq_self_or_eq_succAbove l.castSucc i
      · exact ⟨l, by rw [Fin.succAbove_castSucc_self, ← hi, hl.right_succ]⟩
      · exact ⟨_, hi⟩

lemma min_δ : min (x := hl.δ) k rfl = l := by
  refine le_antisymm (Finset.min'_le _ _ ?_)
    ((Finset.le_min'_iff _ _).2 (fun i hi ↦ ?_))
  · rw [mem_finset_iff]
    dsimp
    rw [stdSimplex.δ_apply, Fin.succAbove_castSucc_self, hl.left_succ]
  · by_contra! hil
    rw [not_le] at hil
    rw [mem_finset_iff] at hi
    dsimp at hi
    rw [stdSimplex.δ_apply, Fin.succAbove_of_castSucc_lt _ _ (by simpa)] at hi
    have := (hl.succ_le_left_iff _).1 hi.symm.le
    simp at this
    omega

end IsIndex

section

variable (x) in
def NotIsIndex : Prop := ∀ (d : ℕ) (hd : x.dim = d) (l : Fin (d + 1)), ¬IsIndex k hd l

namespace NotIsIndex

variable (hx : NotIsIndex k x) {d : ℕ} (hd : x.dim = d) (l : Fin (d + 1))

def φ (i : Fin (d + 1 + 1)) :
    Fin (m + 1 + 1) × Fin (n + 1) :=
  if i = l.castSucc then ⟨k.castSucc, (x.cast hd).simplex.2 l⟩
  else objEquiv (x.cast hd).simplex (l.predAbove i)

lemma φ_castSucc : φ k hd l l.castSucc = ⟨k.castSucc, (x.cast hd).simplex.2 l⟩ := by
  simp [φ]

variable (hl : min k hd = l)

lemma φ_succAbove (i : Fin (d + 1)) :
    φ k hd l (l.castSucc.succAbove i) =
      objEquiv (x.cast hd).simplex i := by
  simp [φ, if_neg (Fin.succAbove_ne l.castSucc i)]

lemma φ_succ_right : (φ k hd l l.succ).2 = (φ k hd l l.castSucc).2 := by
  have := φ_succAbove k hd l l
  rw [Fin.succAbove_castSucc_self] at this
  rw [this, φ_castSucc]
  rfl

variable {k hd l}

include hl in
lemma φ_succ_left : (φ k hd l l.succ).1 = k.succ := by
  have := φ_succAbove k hd l l
  rw [Fin.succAbove_castSucc_self] at this
  rw [this]
  subst hl
  dsimp
  exact min_left k hd

include hx hl in
lemma strictMono_φ : StrictMono (φ k hd l) := by
  have hx' := strictMono_of_nonDegenerate ⟨_, (x.cast hd).nonDegenerate⟩
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  obtain hi | rfl | hi := lt_trichotomy i l
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
    have h₁ := φ_succAbove k hd l i.castSucc
    rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa)] at h₁
    obtain ⟨l, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hi)
    simp only [Fin.castSucc_lt_succ_iff] at hi
    obtain hi | rfl := hi.lt_or_eq
    · have h₂ := φ_succAbove k hd l.succ i.succ
      rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa),
        ← Fin.succ_castSucc] at h₂
      rw [h₁, h₂]
      exact hx' i.castSucc_lt_succ
    · rw [Fin.succ_castSucc, φ_castSucc, h₁]
      have h₂ := min_left k hd
      rw [hl] at h₂
      have h₃' := hx d hd i.castSucc
      simp at h₃'
      have h₃ := hx d hd i.succ
      simp only [isIndex_succ, S.cast_dim, h₂, true_and] at h₃
      have h₄ := (hx' i.castSucc_lt_succ).le
      have h₅ := hx' i.castSucc_lt_succ
      rw [Prod.le_def] at h₄
      rw [Prod.lt_iff] at h₅
      obtain ⟨h₄₁, h₄₂⟩ := h₄
      dsimp at h₄₁ h₄₂ h₅
      rw [h₂] at h₄₁ h₅
      sorry
  · rw [φ_castSucc]
    apply Prod.lt_of_lt_of_le
    · rw [φ_succ_left hl]
      exact k.castSucc_lt_succ
    · dsimp
      rw [φ_succ_right, φ_castSucc]
      rfl
  · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hi)
    rw [← Fin.le_castSucc_iff] at hi
    have h₁ := φ_succAbove k hd l i.castSucc
    have h₂ := φ_succAbove k hd l i.succ
    rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_castSucc] at h₁
    rw [Fin.succAbove_of_le_castSucc _ _ (by
      simpa only [Fin.castSucc_le_castSucc_iff]
        using hi.trans i.castSucc_le_succ)] at h₂
    rw [h₁, h₂]
    exact hx' i.castSucc_lt_succ

def simplex : (Δ[m + 1] ⊗ Δ[n] : SSet.{u}) _⦋d + 1⦌ :=
  objEquiv.symm ⟨φ k hd l, (hx.strictMono_φ hl).monotone⟩

@[simp]
lemma simplex_left (i : Fin (d + 2)) :
    (hx.simplex hl).1 i = (φ k hd l i).1 := rfl

@[simp]
lemma simplex_right (i : Fin (d + 2)) :
    (hx.simplex hl).2 i = (φ k hd l i).2 := rfl

lemma δ_simplex :
    (Δ[m + 1] ⊗ Δ[n]).δ l.castSucc (hx.simplex hl) = (x.cast hd).simplex := by
  apply objEquiv.injective
  ext i : 2
  simp [simplex, objEquiv_δ_apply, φ_succAbove]

@[simps]
noncomputable def type₁ :
    ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N where
  dim := d + 1
  simplex := hx.simplex hl
  nonDegenerate := by
    simpa only [nonDegenerate_iff_strictMono] using hx.strictMono_φ hl
  notMem h := (x.cast hd).notMem (by
    rw [← hx.δ_simplex hl]
    exact Subcomplex.map_mem_obj _ _ h)

end NotIsIndex

end

namespace IsIndex

variable {k} {d : ℕ} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hl : IsIndex k hd l.succ)

lemma notIsIndex_δ : NotIsIndex k hl.δ := by
  intro e he p hp
  obtain rfl := he
  induction p using Fin.cases with
  | zero => simp at hp
  | succ p =>
    dsimp at p
    obtain rfl : l = p.succ := by rw [← hp.min_eq, min_δ]
    apply (strictMono_of_nonDegenerate ⟨_, (x.cast hd).nonDegenerate⟩
      (Fin.castSucc_lt_succ p.castSucc)).ne
    have h₁ := hp.left_castSucc
    have h₂ := hl.left_castSucc
    have h₃ := hp.left_succ
    have h₄ := hl.right_succ
    have h₅ := hp.right_succ
    simp only [δ_dim, S.cast_simplex_rfl, δ_simplex, prod_δ_fst, stdSimplex.δ_apply,
      Fin.castSucc_succAbove_castSucc, Fin.succAbove_succ_self, Fin.succAbove_castSucc_self,
      prod_δ_snd] at h₁ h₂ h₃ h₄ h₅
    ext : 1
    · exact h₁.trans h₂.symm
    · exact h₅.symm.trans h₄

end IsIndex

variable (n)

structure ι where
  x : ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N
  d : ℕ
  hd : x.dim = d + 1
  l : Fin (d + 1)
  isIndex : IsIndex k hd l.succ

namespace ι

variable {k n} (s : ι k n)

lemma ext_iff (t : ι k n) :
    s = t ↔ s.x = t.x := by
  refine ⟨by rintro rfl; rfl, fun h ↦ ?_⟩
  have hs := s.isIndex.min_eq
  have ht := t.isIndex.min_eq
  obtain ⟨x, d, hd, l, isIndex⟩ := s
  obtain ⟨y, d', hd', l', isIndex'⟩ := t
  subst h
  dsimp at hs ht hd hd'
  obtain rfl : d = d' := by omega
  obtain rfl : l = l' := by rw [← Fin.succ_inj, ← hs, ← ht]
  rfl

end ι

namespace NotIsIndex

variable {k n} (hx : NotIsIndex k x) {d : ℕ} {hd : x.dim = d}
  {l : Fin (d + 1)} (hl : min k hd = l)

lemma isIndex : IsIndex k (hx.type₁_dim hl) l.succ := by
  simp [isIndex_succ, φ_castSucc, φ_succ_left hl, φ_succ_right]

include hl in
@[simps]
noncomputable def toι : ι k n where
  x := hx.type₁ hl
  d := d
  hd := rfl
  l := l
  isIndex := hx.isIndex hl

section

variable {y : ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N}
  {hdy : y.dim = d + 1} (l' : Fin (d + 1))
  (hy : IsIndex k hdy l'.succ) (hxy : hy.δ = x)

include hl hxy in
lemma l_eq_of_isIndex : l = l' := by
  subst hxy
  simpa only [hl] using hy.min_δ

end

end NotIsIndex

namespace IsIndex

variable {k n} {d : ℕ} {hd : x.dim = d + 1} {l : Fin (d + 1)} (hx : IsIndex k hd l.succ)
  {y : ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).N}
  (hxy : hx.δ = y) (hdy : y.dim = d)

include hxy in
lemma min_eq_of_δ_eq :
    min k hdy = l := by
  subst hxy
  exact hx.min_δ

include hx hxy in
lemma eq_toι (hy : NotIsIndex k y) {l' : Fin (d + 1)} (hl' : min k hdy = l') :
    (hy.toι hl').x = x := by
  have := hx
  have := hxy
  sorry

end IsIndex

end pairingCore

open pairingCore

variable (n)
@[simps]
noncomputable def pairingCore :
    ((horn.{u} (m + 1) k.castSucc).unionProd (boundary n)).PairingCore where
  ι := ι k n
  d s := s.d
  type₁ s := (s.x.cast s.hd).simplex
  index s := s.l.castSucc
  nonDegenerate₁ s := (s.x.cast s.hd).nonDegenerate
  nonDegenerate₂ s := s.isIndex.δ.nonDegenerate
  notMem₁ s := (s.x.cast s.hd).notMem
  notMem₂ s := s.isIndex.δ.notMem
  injective_type₁ h := by
    simpa [S.cast_eq_self, ι.ext_iff, Subcomplex.N.ext_iff, SSet.N.ext_iff] using h
  injective_type₂ {s t} h := by
    rw [ι.ext_iff]
    obtain ⟨d, hd, l, hl⟩ : ∃ (d : ℕ) (hd : s.x.dim = d + 1) (l : Fin (d + 1)),
      IsIndex k hd l.succ := ⟨s.d, s.hd, _, s.isIndex⟩
    have hds : s.d = d := by
      rw [← Nat.add_left_inj (n := 1), ← hd, s.hd]
    have hdt : t.d = d := by
      rw [← hds]
      exact (S.dim_eq_of_eq h).symm
    have hd' : t.x.dim = d + 1 := by
      rw [t.hd, hdt]
    obtain ⟨l', hl'⟩ : ∃ (l' : Fin (d + 1)), IsIndex k hd' l'.succ := by
      obtain rfl : t.d = d := hdt
      exact ⟨_, t.isIndex⟩
    generalize hu₁ : hl.δ = u
    have hu₀ : u.dim = d := by subst hu₁; rfl
    have hu₁' : hl'.δ = u := by
      rw [← hu₁, Subcomplex.N.ext_iff, SSet.N.ext_iff]
      convert h.symm using 1
      · subst hdt
        obtain rfl := hl'.unique t.isIndex
        rfl
      · subst hds
        obtain rfl := hl.unique s.isIndex
        rfl
    have hu₂ : NotIsIndex k u := by
      subst hu₁
      exact hl.notIsIndex_δ
    rw [← hl.eq_toι hu₁ hu₀ hu₂ rfl, hl'.eq_toι hu₁' hu₀ hu₂ rfl]
  type₁_neq_type₂ s t := fun h ↦ by
    have h₁ : s.x = t.isIndex.δ := by
      dsimp at h
      rw [S.cast_eq_self] at h
      rwa [Subcomplex.N.ext_iff, SSet.N.ext_iff]
    have h₂ := t.isIndex.notIsIndex_δ
    rw [← h₁] at h₂
    exact h₂ _ _ _ s.isIndex
  surjective' x := by
    by_cases hx : NotIsIndex k x
    · generalize hd : x.dim = d
      generalize hl : min k hd = l
      refine ⟨hx.toι hl, Or.inr ?_⟩
      dsimp
      rw [hx.δ_simplex hl, S.mk_simplex, ← (x.toS.cast_eq_self hd)]
    · simp only [NotIsIndex, not_forall, not_not] at hx
      obtain ⟨d, hd, l, hx⟩ := hx
      obtain rfl | ⟨l, rfl⟩ := l.eq_zero_or_eq_succ
      · simp at hx
      · obtain ⟨d, rfl⟩ := Nat.exists_add_one_eq.2 l.pos
        exact ⟨{
          x := x
          d := d
          hd := hd
          l := l
          isIndex := hx }, Or.inl (x.toS.cast_eq_self hd).symm ⟩

instance : (pairingCore k n).IsProper where
  isUniquelyCodimOneFace s :=
    isUniquelyCodimOneFace (s.x.cast s.hd).nonDegenerate _

lemma isInner_pairingCore (k : Fin m) :
    (pairingCore k.succ n).IsInner := by
  intro s
  refine ⟨fun hs ↦ ?_, s.l.castSucc_lt_last.ne⟩
  dsimp at hs
  rw [Fin.castSucc_eq_zero_iff] at hs
  have h₁ := s.isIndex
  rw [hs, isIndex_succ] at h₁
  replace h₁ := h₁.1
  obtain ⟨i, hi⟩ := mem_range_left _ s.hd 0 (by simp [Fin.ext_iff])
  have h₂ := stdSimplex.monotone_apply (s.x.cast s.hd).simplex.1 i.zero_le
  dsimp at h₁ h₂ hi
  rw [h₁, hi] at h₂
  simp [Fin.le_def] at h₂

end prodStdSimplex

end SSet
