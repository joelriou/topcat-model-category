import TopCatModelCategory.SSet.NonDegeneratePartialOrder
import TopCatModelCategory.SSet.AnodyneExtensionsDefs
import TopCatModelCategory.SSet.Evaluation
import TopCatModelCategory.SSet.Monomorphisms
import TopCatModelCategory.SSet.Skeleton
import TopCatModelCategory.ColimitsType
import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.ConditionallyCompleteLattice.Finset

-- Sean Moss, Another approach to the Kan-Quillen model structure

open HomotopicalAlgebra CategoryTheory Simplicial Limits Opposite

namespace SSet

variable (X : SSet.{u})

protected def S : Type u := Sigma (fun n ↦ X _⦋n⦌)

variable {X}
abbrev S.mk {n : ℕ} (x : X _⦋n⦌) : X.S := ⟨_, x⟩

lemma S.dim_eq_of_mk_eq {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (h : S.mk x = S.mk y) : n = m :=
  congr_arg Sigma.fst h

@[simp]
lemma S.eq_iff {n : ℕ} (x y : X _⦋n⦌) :
    S.mk x = S.mk y ↔ x = y := by
  rw [Sigma.ext_iff]
  simp

end SSet

namespace SSet.Subcomplex

instance {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (n : SimplexCategoryᵒᵖ) :
    Mono (f.app n) := inferInstance

instance {X : SSet.{u}} {A B : X.Subcomplex} (h : A ≤ B) (n : SimplexCategoryᵒᵖ) :
    Mono (((CategoryTheory.evaluation _ _).obj n).map (Subcomplex.homOfLE h)) :=
  inferInstanceAs (Mono ((Subcomplex.homOfLE h).app n))

end SSet.Subcomplex

lemma SimplexCategory.δ_injective {n : ℕ} :
    Function.Injective (δ (n := n)) := by
  intro i j hij
  wlog h : i < j
  · simp only [not_lt] at h
    obtain h | rfl := h.lt_or_eq
    · exact (this hij.symm h).symm
    · rfl
  obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  have : i.castSucc.succAbove i = j.succAbove i := by
    change δ i.castSucc i = δ j i
    rw [hij]
  simp [Fin.succAbove_of_castSucc_lt _ _ h, Fin.ext_iff] at this

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
  ∃ (f : ⦋n⦌ ⟶ ⦋m⦌), Mono f ∧ n ≠ m ∧ X.map f.op y = x

namespace IsFace

variable {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌} (hxy : IsFace x y)

noncomputable def f : ⦋n⦌ ⟶ ⦋m⦌ := hxy.choose

instance : Mono hxy.f := hxy.choose_spec.1

include hxy in
lemma lt : n < m :=
  Nat.lt_of_le_of_ne (SimplexCategory.len_le_of_mono (f := hxy.f) inferInstance)
    hxy.choose_spec.2.1

@[simp]
lemma eq : X.map hxy.f.op y = x := hxy.choose_spec.2.2

include hxy in
lemma mem_ofSimplex : x ∈ (Subcomplex.ofSimplex y).obj _ :=
  ⟨hxy.f.op, by simp⟩

lemma trans {p : ℕ} (z : X _⦋p⦌) (hxy : IsFace x y) (hyz : IsFace y z) :
    IsFace x z := by
  have ⟨f, _, hnm, hf⟩ := hxy
  have ⟨g, _, hmp, hg⟩ := hyz
  exact ⟨f ≫ g, inferInstance, (hxy.lt.trans hyz.lt).ne, by aesop⟩

variable {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌} (hxy : IsFace x y)
end IsFace

lemma eq_map_mono_of_mem_ofSimplex_of_mem_nonDegenerate
    {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (hxy : x ∈ (Subcomplex.ofSimplex y).obj _)
    (hx : x ∈ X.nonDegenerate _) :
    ∃ (f : ⦋n⦌ ⟶ ⦋m⦌), Mono f ∧ X.map f.op y = x := by
  obtain ⟨g, rfl⟩ := hxy
  exact ⟨g.unop, mono_of_nonDegenerate _ _ hx, rfl⟩

lemma isFace_iff_neq_and_mem_ofSimplex {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (hx : x ∈ X.nonDegenerate _) :
    IsFace x y ↔ (S.mk x ≠ S.mk y) ∧ x ∈ (Subcomplex.ofSimplex y).obj _ :=
  ⟨fun h ↦ ⟨fun h' ↦ by
    have := h.lt
    simp [S.dim_eq_of_mk_eq h'] at this, h.mem_ofSimplex⟩, by
    rintro ⟨h₁, ⟨f, hf⟩⟩
    obtain ⟨f, rfl⟩ := Quiver.Hom.op_surjective f
    have : Mono f := by
      subst hf
      exact mono_of_nonDegenerate _ _ hx
    refine ⟨f, inferInstance, ?_, hf⟩
    rintro rfl
    obtain rfl := SimplexCategory.eq_id_of_mono f
    obtain rfl : y = x := by simpa using hf
    simp at h₁⟩

def IsUniquelyCodimOneFace {n m : ℕ} (x : X _⦋n⦌) (y : X _⦋m⦌) : Prop :=
  m = n + 1 ∧ ∃! (f : ⦋n⦌ ⟶ ⦋m⦌), Mono f ∧ X.map f.op y = x

namespace IsUniquelyCodimOneFace

lemma mk {n : ℕ} {x : X _⦋n⦌} {y : X _⦋n + 1⦌}
    (h : ∃! (i : Fin (n + 2)), X.δ i y = x) :
    IsUniquelyCodimOneFace x y := by
  obtain ⟨i, h₁, h₂⟩ := h
  refine ⟨rfl, SimplexCategory.δ i, ⟨inferInstance, h₁⟩, fun f ⟨h₃, h₄⟩ ↦ ?_⟩
  obtain ⟨j, rfl⟩ := SimplexCategory.eq_δ_of_mono f
  rw [h₂ j h₄]

variable {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌} (hxy : IsUniquelyCodimOneFace x y)

include hxy

lemma dim_eq : m = n + 1 := hxy.1

lemma isFace : IsFace x y := by
  obtain ⟨f, _, hf⟩ := hxy.2.exists
  exact ⟨f, inferInstance, by simp [hxy.dim_eq], hf⟩

def cast : X _⦋n + 1⦌ := by
  obtain rfl := hxy.dim_eq
  exact y

@[simp]
lemma ofSimplex_cast :
    Subcomplex.ofSimplex hxy.cast = Subcomplex.ofSimplex y := by
  obtain rfl := hxy.dim_eq
  rfl

lemma existsUnique_index : ∃! (i : Fin (n + 2)), X.δ i hxy.cast = x := by
  obtain rfl := hxy.dim_eq
  dsimp only [cast]
  apply existsUnique_of_exists_of_unique
  · obtain ⟨φ, _, hφ⟩ := hxy.2.exists
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono φ
    exact ⟨i, hφ⟩
  · intro i j hi hj
    exact SimplexCategory.δ_injective
      (hxy.2.unique ⟨inferInstance, hi⟩ ⟨inferInstance, hj⟩)

noncomputable def index : Fin (n + 2) := hxy.existsUnique_index.exists.choose

@[simp]
lemma δ_index : X.δ hxy.index hxy.cast = x :=
  hxy.existsUnique_index.exists.choose_spec

end IsUniquelyCodimOneFace

namespace Subcomplex

variable (A : X.Subcomplex)

/-- The type of nondegenerate simplices of `X` which do not belong to `A`. -/
def N : Type u := { x : X.N // x.2.1 ∉ A.obj _ }

lemma N.induction
    {motive : ∀ {n : ℕ} (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate _), Prop}
    (h₀ : ∀ (x : X.N) (_ : x.2.1 ∈ A.obj _), motive x.2.1 x.2.2)
    (h₁ : ∀ (x : A.N), motive x.1.2.1 x.1.2.2)
    {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate _) : motive x hx := by
  apply SSet.N.induction
  intro x
  by_cases hx : x.2.1 ∈ A.obj _
  · exact h₀ _ hx
  · exact h₁ ⟨x, hx⟩

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

lemma neq (x : P.I) (y : P.II) :
    S.mk x.1.1.2.1 ≠ S.mk y.1.1.2.1 := by
  obtain ⟨⟨⟨n, x, h₁⟩, h₂⟩, hx⟩ := x
  obtain ⟨⟨⟨m, y, _⟩, _⟩, hy⟩ := y
  intro h
  obtain rfl := S.dim_eq_of_mk_eq h
  simp at h
  subst h
  have : ⟨⟨n, x, h₁⟩, h₂⟩ ∈ P.I ∩ P.II := by aesop
  simp [P.inter] at this

class IsProper where
  isUniquelyCodimOneFace (x : P.II) : IsUniquelyCodimOneFace x.1.1.2.1 (P.p x).1.1.2.1

lemma isUniquelyCodimOneFace [P.IsProper] (x : P.II) :
    IsUniquelyCodimOneFace x.1.1.2.1 (P.p x).1.1.2.1 :=
  IsProper.isUniquelyCodimOneFace x

def AncestralRel (x y : P.II) : Prop :=
  x ≠ y ∧ IsFace x.1.1.2.1 (P.p y).1.1.2.1

namespace AncestralRel

variable {P} {x y : P.II} (hxy : P.AncestralRel x y)

include hxy

lemma ne : x ≠ y := hxy.1

lemma isFace : IsFace x.1.1.2.1 (P.p y).1.1.2.1 := hxy.2

lemma le [P.IsProper] : x.1.1.1 ≤ y.1.1.1 := by
  simpa only [(P.isUniquelyCodimOneFace y).dim_eq, Nat.lt_succ_iff] using hxy.isFace.lt

end AncestralRel

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

section

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

end

lemma isRegular_iff [P.IsProper] :
    P.IsRegular ↔
      ∃ (φ : P.II → ℕ),
        ∀ (x y : P.II) (_ : x.1.1.1 = y.1.1.1), P.AncestralRel x y → φ x < φ y :=
  ⟨fun _ ↦ ⟨P.rank', fun x y _ h ↦ P.rank'_lt h⟩, fun ⟨φ, hφ⟩ ↦
    { wf := by
        rw [WellFounded.wellFounded_iff_no_descending_seq]
        refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
        let d (n : ℕ) := (f n).1.1.1
        obtain ⟨n₀, hn₀⟩ := (wellFoundedGT_iff_monotone_chain_condition (α := ℕᵒᵈ)).1
          inferInstance ⟨d, monotone_nat_of_le_succ (fun n ↦ (hf n).le)⟩
        dsimp at hn₀
        refine not_strictAnti_of_wellFoundedLT (fun n ↦ φ (f (n₀ + n)))
          (strictAnti_nat_of_succ_lt (fun n ↦ ?_))
        rw [← add_assoc]
        exact hφ _ _ ((hn₀ _ (by omega)).symm.trans (hn₀ _ (by omega))) (hf _) }⟩

section

variable [P.IsRegular]

def filtration (n : ℕ) : X.Subcomplex :=
  A ⊔ ⨆ (x : { y : P.II // P.rank' y < n }), Subcomplex.ofSimplex (P.p x.1).1.1.2.1

lemma le_filtration (n : ℕ) : A ≤ P.filtration n := le_sup_left

@[simp]
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

lemma mem_filtration_I_cast (x : P.II) :
    (P.isUniquelyCodimOneFace x).cast ∈ (P.filtration (P.rank' x + 1)).obj _ := by
  rw [← Subcomplex.ofSimplex_le_iff, IsUniquelyCodimOneFace.ofSimplex_cast,
    Subcomplex.ofSimplex_le_iff]
  exact P.mem_filtration_I x

lemma mem_filtration_II (x : P.II) :
    x.1.1.2.1 ∈ (P.filtration (P.rank' x + 1)).obj _ := by
  have := P.mem_filtration_I x
  rw [← Subcomplex.ofSimplex_le_iff] at this
  exact this _ (P.isUniquelyCodimOneFace x).isFace.mem_ofSimplex

lemma not_mem_filtation_II (x : P.II) :
    x.1.1.2.1 ∉ (P.filtration (P.rank' x)).obj _ := by
  simp only [filtration, Subpresheaf.max_obj, Subpresheaf.iSup_obj,
    Set.mem_union, Set.mem_iUnion, not_or, not_exists]
  rw [Subtype.forall]
  refine ⟨x.1.2, fun y hy ↦ ?_⟩
  intro h
  have : P.AncestralRel x y :=
    ⟨by rintro rfl; simp at hy, by
      rw [isFace_iff_neq_and_mem_ofSimplex x.1.1.2.2]
      exact ⟨(P.neq _ _).symm, h⟩⟩
  have := P.rank'_lt this
  omega

lemma mem_filtration_I_cast_of_rank'_lt (x : P.II) {n : ℕ} (hn : P.rank' x < n):
    (P.isUniquelyCodimOneFace x).cast ∈ (P.filtration n).obj _ :=
  P.filtration_monotone (by simpa) _ (P.mem_filtration_I_cast x)

@[simp]
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

def map' (x : P.II) : Δ[x.1.1.1 + 1] ⟶ X :=
  yonedaEquiv.symm (P.isUniquelyCodimOneFace x).cast

noncomputable abbrev index (x : P.II) : Fin (x.1.1.1 + 2) :=
  (P.isUniquelyCodimOneFace x).index

@[simp]
lemma map'_objEquiv_symm_δ_index (x : P.II) :
    (P.map' x).app (op ⦋_⦌) (stdSimplex.objEquiv.symm (SimplexCategory.δ (P.index x))) =
      x.1.1.2.1 :=
  (P.isUniquelyCodimOneFace x).δ_index

@[simp]
lemma map'_app_objEquiv_symm (x : P.II) {d : SimplexCategory}
    (f : d ⟶ ⦋x.1.1.1 + 1⦌) :
    (P.map' x).app _ (stdSimplex.objEquiv.symm f) =
      X.map f.op (P.isUniquelyCodimOneFace x).cast :=
  rfl

def Cells (n : ℕ) : Type u := { y : P.II // P.rank' y = n }

def mapToSucc {n : ℕ} (x : P.Cells n) :
    Δ[x.1.1.1.1 + 1] ⟶ P.filtration (n + 1) :=
  Subcomplex.lift (P.map' x.1) (by
    simp only [preimage_eq_top_iff]
    dsimp only [range]
    rw [Subcomplex.range_eq_ofSimplex, Subpresheaf.ofSection_le_iff, map',
      Equiv.apply_symm_apply]
    simpa only [← x.2] using P.mem_filtration_I_cast x.1)

lemma filtration_preimage_map' {n : ℕ} (x : P.Cells n) :
    (P.filtration n).preimage (P.map' x.1) = SSet.horn _ (P.index x.1) := by
  obtain ⟨x, hx⟩ := x
  dsimp
  refine le_antisymm ?_ ?_
  · rw [stdSimplex.subcomplex_le_horn_iff, stdSimplex.face_singleton_compl,
      Subpresheaf.ofSection_le_iff, preimage_obj, Set.mem_preimage]
    intro h
    refine P.not_mem_filtation_II x ?_
    rw [map'_objEquiv_symm_δ_index] at h
    rwa [hx]
  · rw [← Subcomplex.image_le_iff, le_iff_contains_nonDegenerate]
    rintro d ⟨y, hy₁⟩
    revert y hy₁
    fapply Subcomplex.N.induction
    · exact A
    · intro x hx _
      exact P.filtration_monotone (Nat.zero_le n) _ (by simpa)
    · intro y hy
      dsimp at hy ⊢
      obtain ⟨z, hz, hz'⟩ := hy
      obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective z
      dsimp at f
      rw [map'_app_objEquiv_symm] at hz'
      let σ := (P.isUniquelyCodimOneFace x).cast
      change X.map f.op σ = _ at hz'
      have hy := y.1.2.2
      rw [← hz'] at hy
      have : Mono f := mono_of_nonDegenerate _ _ hy
      obtain ⟨t, ht⟩ := P.exists_or y
      have htx : P.AncestralRel t x := by
        -- is this true?
        constructor
        · sorry
        · sorry
      replace htx := P.rank'_lt htx
      rw [hx] at htx
      replace htx := P.mem_filtration_I_cast_of_rank'_lt _ htx
      rw [← ofSimplex_le_iff] at htx ⊢
      refine le_trans ?_ htx
      rw [IsUniquelyCodimOneFace.ofSimplex_cast,
        Subpresheaf.ofSection_le_iff]
      obtain rfl | rfl := ht
      · exact (P.isUniquelyCodimOneFace t).isFace.mem_ofSimplex
      · exact mem_ofSimplex_obj _

noncomputable def map {n : ℕ} (x : P.Cells n) :
    (SSet.horn _ (P.index x.1) : SSet) ⟶ P.filtration n :=
  Subcomplex.lift ((SSet.horn _ (P.index x.1)).ι ≫ P.map' x.1) (by
    rw [Subcomplex.preimage_preimage, filtration_preimage_map', preimage_ι])

noncomputable abbrev sigmaHorn (n : ℕ) :=
  ∐ (fun (x : P.Cells n) ↦ (SSet.horn.{u} _ (P.index x.1) : SSet))

noncomputable abbrev ιSigmaHorn {n : ℕ} (x : P.Cells n) :
    (SSet.horn.{u} _ (P.index x.1) : SSet) ⟶ P.sigmaHorn n :=
  Limits.Sigma.ι (fun (x : P.Cells n) ↦ (SSet.horn.{u} _ (P.index x.1) : SSet)) x

lemma ιSigmaHorn_jointly_surjective {n d : ℕ} (a : (P.sigmaHorn n) _⦋d⦌) :
    ∃ (x : P.Cells n) (a' : (Λ[_, P.index x.1] : SSet) _⦋d⦌), (P.ιSigmaHorn x).app _ a' = a :=
  Types.jointly_surjective_of_isColimit_cofan
    (isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
    (coproductIsCoproduct _)) a

noncomputable abbrev sigmaStdSimplex (n : ℕ) :=
  ∐ (fun (x : P.Cells n) ↦ Δ[x.1.1.1.1 + 1])

noncomputable abbrev ιSigmaStdSimplex {n : ℕ} (x : P.Cells n) :
    Δ[x.1.1.1.1 + 1] ⟶ P.sigmaStdSimplex n :=
  Limits.Sigma.ι (fun (x : P.Cells n) ↦ Δ[x.1.1.1.1 + 1]) x

lemma ιSigmaStdSimplex_jointly_surjective {n d : ℕ} (a : (P.sigmaStdSimplex n) _⦋d⦌) :
    ∃ (x : P.Cells n) (a' : (Δ[x.1.1.1.1 + 1] : SSet) _⦋d⦌), (P.ιSigmaStdSimplex x).app _ a' = a :=
  Types.jointly_surjective_of_isColimit_cofan
    (isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
    (coproductIsCoproduct _)) a

noncomputable def m (n : ℕ) :
    P.sigmaHorn n ⟶ P.sigmaStdSimplex n :=
  Limits.Sigma.map (fun _ ↦ Subcomplex.ι _)

instance (n : ℕ) : Mono (P.m n) := by
  dsimp [m]
  infer_instance

@[reassoc (attr := simp)]
lemma ι_m {n : ℕ} (x : P.Cells n) :
    P.ιSigmaHorn x ≫ P.m n =
      Subcomplex.ι _ ≫ P.ιSigmaStdSimplex x :=
  ι_colimMap _ _

noncomputable def t (n : ℕ) : P.sigmaHorn n ⟶ P.filtration n :=
  Sigma.desc P.map

@[reassoc (attr := simp)]
lemma ι_t {n : ℕ} (x : P.Cells n) :
    P.ιSigmaHorn x ≫ P.t n = P.map x := by
  simp [t]

noncomputable def b (n : ℕ) : P.sigmaStdSimplex n ⟶ P.filtration (n + 1) :=
  Sigma.desc P.mapToSucc

@[reassoc (attr := simp)]
lemma ι_b {n : ℕ} (x : P.Cells n) :
    P.ιSigmaStdSimplex x ≫ P.b n = P.mapToSucc x := by
  simp [b]

@[reassoc]
lemma w (n : ℕ) :
    P.t n ≫ homOfLE (P.filtration_monotone (by simp)) = P.m n ≫ P.b n := by
  aesop_cat

lemma isPullback (n : ℕ) :
    IsPullback (P.t n) (P.m n) (homOfLE (P.filtration_monotone (by simp))) (P.b n) where
  w := P.w n
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨d⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).2
      (IsPullback.isLimit ?_)
    induction' d using SimplexCategory.rec with d
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (P.w n) (op ⦋d⦌), ?_, ?_⟩
    · intro a₁ a₂ ⟨ht, hm⟩
      have : Mono (P.m n) := inferInstance
      rw [NatTrans.mono_iff_mono_app] at this
      simp only [mono_iff_injective] at this
      exact this _ hm
    · intro y b h
      obtain ⟨x, b, rfl⟩ := P.ιSigmaStdSimplex_jointly_surjective b
      have hb : b ∈ Λ[_, P.index x.1].obj _ := by
        obtain ⟨y, hy⟩ := y
        rw [← filtration_preimage_map']
        rw [Subtype.ext_iff] at h
        dsimp at h
        subst h
        rwa [← FunctorToTypes.comp, ι_b] at hy
      refine ⟨(P.ιSigmaHorn x).app _ ⟨b, hb⟩, ?_, ?_⟩
      · rw [Subtype.ext_iff] at h
        dsimp at h
        rw [← FunctorToTypes.comp, ι_t]
        rw [← FunctorToTypes.comp, ι_b] at h
        ext
        exact h
      · rw [← FunctorToTypes.comp, ι_m, comp_app, types_comp_apply,
          Subpresheaf.ι_app])⟩

lemma range_homOfLE_sup_range_b (n : ℕ) :
    Subcomplex.range (Subcomplex.homOfLE (P.filtration_monotone (Nat.le_add_right n 1))) ⊔
      Subcomplex.range (P.b n) = ⊤ := by
  sorry

lemma range_homOfLE_app_union_range_b_app (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    Set.range ((Subcomplex.homOfLE (P.filtration_monotone (Nat.le_add_right n 1))).app d) ∪
      Set.range ((P.b n).app d) = Set.univ :=
  congr_fun (congr_arg Subpresheaf.obj (P.range_homOfLE_sup_range_b n)) d

lemma isPushout (n : ℕ) :
    IsPushout (P.t n) (P.m n) (homOfLE (P.filtration_monotone (by simp))) (P.b n) where
  w := P.w n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨d⟩ ↦ by
    induction' d using SimplexCategory.rec with d
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2
      (IsPushout.isColimit ?_)
    refine Limits.Types.isPushout_of_isPullback_of_mono'
      ((P.isPullback n).map ((CategoryTheory.evaluation _ _).obj _))
      (P.range_homOfLE_app_union_range_b_app n _) ?_
    sorry)⟩

include P

noncomputable def relativeCellComplex :
  RelativeCellComplex.{u}
    (basicCell := fun (n : ℕ) (x : Sigma (fun (d : ℕ) ↦ Fin (d + 2))) ↦ (SSet.horn.{u} _ x.2).ι) A.ι where
  F := P.filtration_monotone.functor ⋙ toPresheafFunctor
  isoBot := Subcomplex.isoOfEq (by simp)
  incl :=
    { app n := Subcomplex.ι _ }
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toPresheafFunctor
      ((CompleteLattice.colimitCocone P.filtration_monotone.functor).isColimit))
      (Cocones.ext ((Subcomplex.isoOfEq (by simp) ≪≫ Subcomplex.topIso _)))
  attachCells n _ :=
    { ι := P.Cells n
      π x := ⟨_, P.index x.1⟩
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := P.m n
      hm := P.ι_m
      g₁ := P.t n
      g₂ := P.b n
      isPushout := by
        dsimp
        sorry }

lemma anodyneExtensions : SSet.anodyneExtensions A.ι :=
  SSet.anodyneExtensions.transfiniteCompositionsOfShape_le _ _
    ⟨(P.relativeCellComplex.transfiniteCompositionOfShape).ofLE (by
      simp only [MorphismProperty.pushouts_le_iff,
        MorphismProperty.coproducts_le_iff]
      rintro _ _ _ ⟨i, d⟩
      exact anodyneExtensions.horn_ι_mem _ _)⟩

end

end Pairing

end Subcomplex

end SSet
