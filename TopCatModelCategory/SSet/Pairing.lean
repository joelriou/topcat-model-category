import TopCatModelCategory.SSet.NonDegeneratePartialOrder
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Order.ConditionallyCompleteLattice.Finset

-- Sean Moss, Another approach to the Kan-Quillen model structure

open CategoryTheory Simplicial

universe u

namespace Order

lemma iSup_lt_iff_of_isLimit_of_finite_of_bot_lt
    {α ι : Type*} [ConditionallyCompleteLinearOrderBot ι]
    (f : α → ι) (x : ι) [Finite α] (hx : ⊥ < x) :
    ⨆ a, f a < x ↔ ∀ (a : α), f a < x := by
  dsimp [iSup]
  by_cases Nonempty α
  · simp [Set.Finite.csSup_lt_iff (Set.finite_range _) (Set.range_nonempty _)]
  · refine ⟨fun h a ↦ lt_of_le_of_lt (le_ciSup (Finite.bddAbove_range f) a) h, fun h ↦ ?_⟩
    convert hx
    convert ConditionallyCompleteLinearOrderBot.csSup_empty
    simpa [← not_nonempty_iff]

end Order

namespace SSet

variable {X : SSet.{u}}

def IsFace {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌) : Prop :=
  ∃ (f : ⦋n⦌ ⟶ ⦋m⦌), Mono f ∧ X.map f.op y = x

namespace IsFace

variable {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌} (hxy : IsFace x y)

noncomputable def f : ⦋n⦌ ⟶ ⦋m⦌ := hxy.choose

instance : Mono hxy.f := hxy.choose_spec.1

@[simp]
lemma eq : X.map hxy.f.op y = x := hxy.choose_spec.2

include hxy in
lemma mem_ofSimplex : x ∈ (Subcomplex.ofSimplex y).obj _ :=
  ⟨hxy.f.op, by simp⟩

end IsFace

def IsUniquelyCodimOneFace {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌) : Prop :=
  m = n + 1 ∧ ∃! (f : ⦋n⦌ ⟶ ⦋m⦌), Mono f ∧ X.map f.op y = x

namespace IsUniquelyCodimOneFace

variable {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌} (hxy : IsUniquelyCodimOneFace x y)

include hxy

lemma dim_eq : m = n + 1 := hxy.1

lemma isFace : IsFace x y := hxy.2.exists

end IsUniquelyCodimOneFace

namespace Subcomplex

variable (A : X.Subcomplex)

/-- The type of nondegenerate simplices of `X` which do not belong to `A`. -/
def N : Type u := { x : X.N // x.2.1 ∉ A.obj _ }

structure Pairing where
  I : Set A.N
  II : Set A.N
  inter : I ∩ II = ∅
  union : I ∪ II = Set.univ
  p : II ≃ I

namespace Pairing

variable {A} (P : A.Pairing)

lemma exists_or (x : A.N) :
    ∃ (y : P.II), x = y ∨ x = P.p y := by
  have := Set.mem_univ x
  rw [← P.union, Set.mem_union] at this
  obtain h | h := this
  · obtain ⟨y, hy⟩ := P.p.surjective ⟨x, h⟩
    exact ⟨y, Or.inr (by rw [hy])⟩
  · exact ⟨⟨_, h⟩, Or.inl rfl⟩

class IsProper where
  h (x : P.II) : IsUniquelyCodimOneFace x.1.1.2.1 (P.p x).1.1.2.1

lemma isUniquelyCodimOneFace [P.IsProper] (x : P.II) :
    IsUniquelyCodimOneFace x.1.1.2.1 (P.p x).1.1.2.1 :=
  IsProper.h x

def AncestralRel (x y : P.II) : Prop :=
  x ≠ y ∧ IsFace x.1.1.2.1 (P.p y).1.1.2.1

def ancestersSet (y : P.II) : Set P.II := { x : P.II | P.AncestralRel x y }

lemma finite_ancesters (y : P.II) :
    Set.Finite (P.ancestersSet y) := by
  let φ : { x : P.II | P.AncestralRel x y } →
      Σ (i : Fin ((P.p y).1.1.1 + 1)), ⦋i⦌ ⟶ ⦋(P.p y).1.1.1⦌ :=
    fun ⟨x, hxy⟩ ↦ ⟨⟨x.1.1.1, by
      simp only [Nat.lt_succ]
      exact SimplexCategory.len_le_of_mono (f := hxy.2.f) inferInstance⟩, hxy.2.f⟩
  apply Finite.of_injective φ
  rintro ⟨⟨⟨⟨n₁, x₁, h₁⟩, h₁'⟩, h₁''⟩, hx₁⟩ ⟨⟨⟨⟨n₂, x₂, h₂⟩, h₂'⟩, h₂''⟩, hx₂⟩ h
  dsimp [φ] at h
  simp only [Sigma.mk.injEq, Fin.mk.injEq, φ] at h
  obtain rfl := h.1
  simp only [heq_eq_eq, true_and, φ] at h
  obtain rfl : x₁ = x₂ := by
    have eq₁ := hx₁.2.eq
    have eq₂ := hx₂.2.eq
    dsimp at eq₁ eq₂
    rw [← eq₁, ← eq₂, h]
  rfl

instance (y : P.II) : Finite (P.ancestersSet y) := P.finite_ancesters y

class IsRegular extends P.IsProper where
  wf : WellFounded P.AncestralRel

variable [P.IsRegular]

lemma wf : WellFounded P.AncestralRel := IsRegular.wf

instance : IsWellFounded _ P.AncestralRel where
  wf := P.wf

noncomputable def rank (x : P.II) : Ordinal.{u} := IsWellFounded.rank P.AncestralRel x

lemma rank_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank x < P.rank y :=
  IsWellFounded.rank_lt_of_rel h

instance (y : P.II) : Finite { x // P.AncestralRel x y } := P.finite_ancesters y

lemma rank_lt_omega (x : P.II) :
    P.rank x < Ordinal.omega0 := by
  induction x using IsWellFounded.induction P.AncestralRel with
  | ind y hy =>
    dsimp only [rank] at hy ⊢
    rw [IsWellFounded.rank_eq,
      Order.iSup_lt_iff_of_isLimit_of_finite_of_bot_lt _ _ Ordinal.omega0_pos]
    rintro ⟨x, hx⟩
    have := hy _ hx
    rw [Ordinal.lt_omega0] at this ⊢
    obtain ⟨n, hn⟩ := this
    exact ⟨n + 1, by simp [hn]⟩

noncomputable def rank' (x : P.II) : ℕ :=
  (Ordinal.lt_omega0.1 (P.rank_lt_omega x)).choose

@[simp]
lemma coe_rank' (x : P.II) : (P.rank' x : ℕ) = P.rank x :=
  (Ordinal.lt_omega0.1 (P.rank_lt_omega x)).choose_spec.symm

lemma rank'_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank' x < P.rank' y := by
  simpa only [← coe_rank', Nat.cast_lt] using P.rank_lt h

def filtration (n : ℕ) : X.Subcomplex :=
  A ⊔ ⨆ (x : { y : P.II // P.rank' y < n }), Subcomplex.ofSimplex (P.p x.1).1.1.2.1

lemma le_filtration (n : ℕ) : A ≤ P.filtration n := le_sup_left

lemma filtration_zero : P.filtration 0 = A :=
  le_antisymm (by simp [filtration]) (P.le_filtration 0)

lemma filtration_monotone : Monotone P.filtration := by
  intro n m h
  dsimp [filtration]
  simp only [sup_le_iff, le_sup_left, true_and, iSup_le_iff]
  intro i
  exact (le_iSup (f := fun (x : { y : P.II // P.rank' y < m }) ↦
    Subcomplex.ofSimplex (P.p x.1).1.1.2.1)
      ⟨i.1, lt_of_lt_of_le i.2 (by simpa)⟩).trans le_sup_right

lemma mem_filtration_I (x : P.II) :
    (P.p x).1.1.2.1 ∈ (P.filtration (P.rank' x + 1)).obj _ := by
  dsimp [filtration]
  simp only [Subpresheaf.iSup_obj, Set.mem_union, Set.mem_iUnion]
  exact Or.inr ⟨⟨x, by simp⟩, mem_ofSimplex_obj _⟩

lemma mem_filtration_II (x : P.II) :
    x.1.1.2.1 ∈ (P.filtration (P.rank' x + 1)).obj _ := by
  have := P.mem_filtration_I x
  rw [← Subcomplex.ofSimplex_le_iff] at this
  exact this _ (P.isUniquelyCodimOneFace x).isFace.mem_ofSimplex

lemma iSup_filtration :
    ⨆ (n : ℕ), P.filtration n = ⊤ :=
  le_antisymm le_top (by
    rw [le_iff_contains_nonDegenerate]
    intro n ⟨x, hx⟩ _
    simp only [Subpresheaf.iSup_obj, Set.mem_iUnion]
    by_cases h : x ∈ A.obj _
    · exact ⟨0, P.le_filtration _ _ h⟩
    · obtain ⟨y, hy | hy⟩ := P.exists_or ⟨⟨n, ⟨x, hx⟩⟩, h⟩
      · have := P.mem_filtration_II y
        exact ⟨P.rank' y + 1, by rwa [← hy] at this⟩
      · have := P.mem_filtration_I y
        exact ⟨P.rank' y + 1, by rwa [← hy] at this⟩)

end Pairing

end Subcomplex

end SSet
