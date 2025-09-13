import TopCatModelCategory.TopCat.T1Inclusion
import TopCatModelCategory.TopCat.AttachCells
import TopCatModelCategory.AttachCells

universe w w' t v u

open CategoryTheory HomotopicalAlgebra Topology Limits

namespace TopCat

variable {X₁ X₂ X₃ X₄ : TopCat.{u}} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄}
  {b : X₃ ⟶ X₄} (sq : IsPushout t l r b)

end TopCat

namespace CategoryTheory.Types

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A : (j : J) → α j → Type u}
  {B : (j : J) → α j → Type u}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}

namespace RelativeInjectiveCellComplex

variable {h} {X₀ X : Type u}
  {f : X₀ ⟶ X} {hf : RelativeCellComplex.{w} basicCell f}
  (h : ∀ j i, Function.Injective (basicCell j i))

variable (c : hf.Cells)

def cell : Set X := Set.range c.ι

def boundaryCell : Set X := Set.range (c.ι ∘ basicCell c.j c.i)

lemma boundaryCell_subset :
    boundaryCell c ⊆ cell c := by
  dsimp only [boundaryCell, cell]
  grind

def boundaryCellCompl : Set X := c.ι '' (Set.range (basicCell c.j c.i))ᶜ

end RelativeInjectiveCellComplex

end CategoryTheory.Types

namespace TopCat

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A : (j : J) → α j → TopCat.{u}}
  {B : (j : J) → α j → TopCat.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i}
  {X₀ X : TopCat.{u}} {f : X₀ ⟶ X}
  (hf : RelativeCellComplex.{w} basicCell f)
  (h : ∀ j i, t₁Inclusions (basicCell j i))

namespace RelativeT₁CellComplex

include hf

section

include h

def t₁InclusionsTransfiniteCompositionOfShape :
    t₁Inclusions.TransfiniteCompositionOfShape J f where
  toTransfiniteCompositionOfShape := hf.toTransfiniteCompositionOfShape
  map_mem j hj := by
    refine (?_ : _ ≤ (_ : MorphismProperty _)) _ (hf.attachCells j hj).pushouts_coproducts
    simp only [MorphismProperty.pushouts_le_iff, MorphismProperty.coproducts_le_iff]
    rintro _ _ _ ⟨i⟩
    apply h

lemma isT₁Inclusion : IsT₁Inclusion f :=
  t₁Inclusions.transfiniteCompositionsOfShape_le _ _
    (t₁InclusionsTransfiniteCompositionOfShape hf h).mem

lemma isT₁Inclusion_incl_app (j : J) :
    IsT₁Inclusion (hf.incl.app j) :=
  (t₁InclusionsTransfiniteCompositionOfShape hf h).mem_incl_app j

lemma isT₁Inclusion_map {i j : J} (g : i ⟶ j) :
    IsT₁Inclusion (hf.F.map g) :=
  (t₁InclusionsTransfiniteCompositionOfShape hf h).mem_map g

end

-- all of this holds in `Type _` with injective maps instead
-- of `TopCat` with `t₁Inclusions`

variable {hf} (c : hf.Cells)

def cell : Set X := Set.range c.ι

lemma ι_mem_cell (x) : c.ι x ∈ cell c := by simp [cell]

def boundaryCell : Set X := Set.range (c.ι ∘ basicCell c.j c.i)

lemma boundaryCell_subset :
    boundaryCell c ⊆ cell c := by
  dsimp only [boundaryCell, cell]
  grind

def interiorCell : Set X := c.ι '' (Set.range (basicCell c.j c.i))ᶜ

lemma interiorCell_subset :
    interiorCell c ⊆ cell c := by
  dsimp only [interiorCell, cell]
  grind

lemma boundaryCell_union_interiorCell_eq_cell :
    boundaryCell c ∪ interiorCell c = cell c := by
  dsimp only [boundaryCell, interiorCell, cell]
  grind

lemma range_le_range_incl (j : J) :
    Set.range f ⊆ Set.range (hf.incl.app j) := by
  rintro _ ⟨x₀, rfl⟩
  refine ⟨hf.F.map (homOfLE bot_le) (hf.isoBot.inv x₀), ?_⟩
  simp only [← ConcreteCategory.comp_apply]
  simp

variable (hf) in
lemma range_incl_app_monotone :
    Monotone (fun j ↦ (Set.range (hf.incl.app j) : Set X)) := by
  rintro j₁ j₂ hj _ ⟨x, rfl⟩
  refine ⟨hf.F.map (homOfLE hj) x, ?_⟩
  simp only [← ConcreteCategory.comp_apply]
  simp

lemma interiorCell_subset_range_incl_app_succ :
    interiorCell c ⊆ Set.range (hf.incl.app (Order.succ c.j)) := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨_, rfl⟩

variable (hf) in
lemma iUnion_range_incl_app_eq_univ :
    ⋃ (j : J), (Set.range (hf.incl.app j) : Set X) = Set.univ := by
  ext x
  simp only [Functor.const_obj_obj, Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  exact Types.jointly_surjective_of_isColimit ((hf.map (forget _)).isColimit) x

variable (hf) in
lemma iUnion_range_incl_app_of_isSuccLimit (j : J) (hj : Order.IsSuccLimit j) :
    ⋃ (i : Set.Iio j), (Set.range (hf.incl.app i) : Set X) = Set.range (hf.incl.app j) := by
  apply subset_antisymm
  · simp only [Set.iUnion_coe_set, Set.mem_Iio, Set.iUnion_subset_iff]
    intro i hij
    exact range_incl_app_monotone _ hij.le
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨i, hij⟩, y, rfl⟩ := Types.jointly_surjective_of_isColimit
      ((hf.F ⋙ forget _).isColimitOfIsWellOrderContinuous j hj) x
    dsimp
    simp only [Set.iUnion_coe_set, Set.mem_Iio, homOfLE_leOfHom, Set.mem_iUnion, Set.mem_range,
      exists_prop]
    refine ⟨i, hij, y, ?_⟩
    rw [← ConcreteCategory.comp_apply]
    simp

variable (hf) in
@[simp]
lemma range_incl_app_bot :
    letI φ : _ ⟶ X := hf.incl.app ⊥
    Set.range φ = Set.range f := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    use hf.isoBot.hom y
    simp only [← ConcreteCategory.comp_apply, ← hf.fac, Iso.hom_inv_id_assoc]
  · rintro ⟨x₀, rfl⟩
    use hf.isoBot.inv x₀
    simp only [← ConcreteCategory.comp_apply, ← hf.fac]

variable (hf) in
include h in
lemma range_incl_app_eq_union (j : J) :
    Set.range (hf.incl.app j) =
      Set.range f ∪ ⋃ (σ : { c : hf.Cells // c.j < j }), interiorCell σ.1 := by
  refine subset_antisymm ?_ ?_
  · induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      obtain rfl := hj.eq_bot
      rw [range_incl_app_bot]
      apply Set.subset_union_left
    | succ j hj hj' =>
      rintro _ ⟨x, rfl⟩
      by_cases hx : x ∈ Set.range (hf.F.map (homOfLE (Order.le_succ j)))
      · obtain ⟨y, rfl⟩ := hx
        simp only [← ConcreteCategory.comp_apply, NatTrans.naturality, Functor.const_obj_map,
          Functor.const_obj_obj, Category.comp_id]
        refine (hj'.trans ?_) (Set.mem_range_self y)
        simp only [Functor.const_obj_obj, Set.union_subset_iff, Set.subset_union_left,
          Set.iUnion_subset_iff, Subtype.forall, true_and]
        intro c hc
        exact subset_trans (subset_trans (by rfl)
          (Set.subset_iUnion _ ⟨c, lt_of_lt_of_le hc (Order.le_succ j)⟩))
            Set.subset_union_right
      · let H := ((hf.attachCells j hj).map (forget _))
        obtain ⟨⟨i, ⟨b, hb⟩⟩, hi⟩ := (H.equiv (fun _ ↦ (h _ _).injective)).surjective ⟨x, hx⟩
        rw [Subtype.ext_iff] at hi
        dsimp at hi
        subst hi
        simp only [Set.mem_union, Set.mem_iUnion]
        right
        refine ⟨⟨{ j := j, hj := hj, k := i }, Order.lt_succ_of_not_isMax hj⟩, ?_⟩
        simp only [interiorCell, homOfLE_leOfHom, Set.mem_image, Set.mem_compl_iff]
        exact ⟨b, hb, rfl⟩
    | isSuccLimit j hj hj' =>
      rw [← iUnion_range_incl_app_of_isSuccLimit hf j hj, Set.iUnion_subset_iff]
      rintro ⟨i, hij⟩
      simp only [Set.mem_Iio] at hij
      refine (hj' i hij).trans ?_
      simp only [Functor.const_obj_obj, Set.union_subset_iff, Set.subset_union_left,
        Set.iUnion_subset_iff, Subtype.forall, true_and]
      intro c hc
      exact subset_trans (subset_trans (by rfl)
        (Set.subset_iUnion _ ⟨c, hc.trans hij⟩)) Set.subset_union_right
  · intro (x : X) hx
    simp only [Set.mem_union, Set.mem_iUnion] at hx
    obtain hx | ⟨⟨c, hc⟩, hc'⟩ := hx
    · exact range_le_range_incl _ hx
    · exact range_incl_app_monotone _ (Order.succ_le_of_lt hc)
        (interiorCell_subset_range_incl_app_succ _ hc')

include h in
variable (hf) in
lemma range_union_iUnion_eq_univ :
    Set.range f ∪ ⋃ (c : hf.Cells), interiorCell c = Set.univ := by
  ext x
  refine ⟨by simp, fun hx ↦ ?_⟩
  simp only [← iUnion_range_incl_app_eq_univ hf, Set.mem_iUnion,
    range_incl_app_eq_union hf h, Set.mem_union] at hx ⊢
  tauto

section

include h

variable {c} in
lemma notMem_range_incl_app
    (b : B c.j c.i) (hb : b ∉ Set.range (basicCell c.j c.i)) :
    c.ι b ∉ Set.range (hf.incl.app c.j) := by
  rintro ⟨a, ha⟩
  let H := (hf.attachCells c.j c.hj).map (forget _)
  refine (H.equiv (fun _ ↦ (h _ _).injective) ⟨c.k, ⟨b, hb⟩⟩).2
    ⟨a, (isT₁Inclusion_incl_app hf h (Order.succ c.j)).injective ?_⟩
  dsimp
  rw [← ConcreteCategory.comp_apply, NatTrans.naturality]
  exact ha

variable {c} in
lemma ι_mem_boundaryCell_iff (b : B c.j c.i) :
    c.ι b ∈ boundaryCell c ↔
      b ∈ Set.range (basicCell c.j c.i) := by
  have := h
  constructor
  · rintro ⟨a, ha⟩
    by_contra! hb
    let H := hf.attachCells c.j c.hj
    refine notMem_range_incl_app h b hb ⟨H.g₁ (H.cofan₁.inj c.k a), ?_⟩
    rw [← ha]
    dsimp
    simp only [← ConcreteCategory.comp_apply]
    congr 2
    simp only [Category.assoc]
    dsimp [RelativeCellComplex.Cells.ι, RelativeCellComplex.Cells.i]
    rw [H.cell_def, Category.assoc, ← H.hm_assoc c.k, ← H.isPushout.w_assoc]
    simp
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

lemma disjoint_boundaryCell_interiorCell :
    Disjoint (boundaryCell c) (interiorCell c) := by
  rw [Set.disjoint_iff]
  rintro _ ⟨hb₁, ⟨b, hb₂, rfl⟩⟩
  rw [ι_mem_boundaryCell_iff h] at hb₁
  tauto

variable {c} in
lemma ι_mem_interiorCell_iff (b : B c.j c.i) :
    c.ι b ∈ interiorCell c ↔
      b ∉ Set.range (basicCell c.j c.i) := by
  simp only [← ι_mem_boundaryCell_iff h]
  have hb := ι_mem_cell c b
  rw [← boundaryCell_union_interiorCell_eq_cell, Set.mem_union] at hb
  have := disjoint_boundaryCell_interiorCell h c
  rw [Set.disjoint_iff] at this
  tauto

lemma ι_injective_on_compl {b₁ b₂ : B c.j c.i} (hb : c.ι b₁ = c.ι b₂)
    (hb₁ : b₁ ∉ Set.range (basicCell c.j c.i))
    (hb₂ : b₂ ∉ Set.range (basicCell c.j c.i)) :
    b₁ = b₂ :=
  ((hf.attachCells c.j c.hj).map (forget _)).cell_injective_on
    (fun a ↦ (h _ a).injective)
    ((isT₁Inclusion_incl_app hf h (Order.succ c.j)).injective hb) hb₁ hb₂

noncomputable def equivinteriorCell :
    ((Set.range (basicCell c.j c.i))ᶜ : Set _) ≃ interiorCell c := by
  refine Equiv.ofBijective (fun ⟨b, hb⟩ ↦ ⟨c.ι b, ?_⟩) ⟨?_, ?_⟩
  · rwa [ι_mem_interiorCell_iff h]
  · rintro ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ hb
    rw [Subtype.ext_iff] at hb ⊢
    exact ι_injective_on_compl h _ hb hb₁ hb₂
  · rintro ⟨_, b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

lemma disjoint_interiorCell_range :
    Disjoint (interiorCell c) (Set.range f) := by
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨b, hb, rfl⟩ _ ⟨x₀, rfl⟩ hx₀
  exact notMem_range_incl_app h b hb (range_le_range_incl _ (by tauto))

lemma disjoint_interiorCell_range_incl :
    Disjoint (interiorCell c) (Set.range (hf.incl.app c.j)) := by
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨b, hb, rfl⟩ _ hb' rfl
  exact notMem_range_incl_app h b hb hb'

variable {c} in
lemma disjoint_interiorCell {c' : hf.Cells} (hcc' : c ≠ c') :
    Disjoint (interiorCell c) (interiorCell c') := by
  by_cases hjj' : c.j = c'.j
  · rw [Set.disjoint_iff_forall_ne]
    rintro x hx _ hx' rfl
    obtain ⟨x₀, rfl⟩ := interiorCell_subset_range_incl_app_succ c hx
    obtain ⟨b, hb₁, hb₂⟩ := hx
    obtain ⟨b', hb'₁, hb'₂⟩ := hx'
    obtain ⟨j, hj, k⟩ := c
    obtain ⟨j', hj', k'⟩ := c'
    obtain rfl : j = j' := hjj'
    replace hb₂ := (isT₁Inclusion_incl_app hf h _).injective hb₂
    replace hb'₂ := (isT₁Inclusion_incl_app hf h _).injective hb'₂
    dsimp [RelativeCellComplex.Cells.i] at b hb₁ hb₂ b' hb'₁ hb'₂ hcc'
    replace hcc' : k ≠ k' := by simpa using hcc'
    let H := (hf.attachCells j hj).map (forget _)
    refine (Set.disjoint_iff_forall_ne.1
      (H.disjoint_interiorCell (fun _ ↦ (h _ _).injective) hcc')) (a := x₀) (b := x₀)
      ⟨⟨b, hb₂⟩, ?_⟩ ⟨⟨b', hb'₂⟩, ?_⟩ rfl
    · rw [← hb₂]
      intro hb
      exact hb₁ ((H.cell_mem_boundaryCell_iff (fun j ↦ (h _ _).injective) b).1 hb)
    · rw [← hb'₂]
      intro hb
      exact hb'₁ ((H.cell_mem_boundaryCell_iff (fun j ↦ (h _ _).injective) b').1 hb)
  · wlog hj' : c'.j < c.j generalizing c c'
    · exact (this hcc'.symm (Ne.symm hjj')
        (lt_of_le_of_ne (by simpa using hj') hjj')).symm
    refine Set.disjoint_of_subset_right ?_ (disjoint_interiorCell_range_incl h c)
    exact (interiorCell_subset_range_incl_app_succ c').trans
      (range_incl_app_monotone _ (Order.succ_le_of_lt hj'))

end

end RelativeT₁CellComplex

end TopCat
