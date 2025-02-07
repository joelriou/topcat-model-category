import TopCatModelCategory.SSet.Degenerate
import TopCatModelCategory.SSet.StandardSimplex
import TopCatModelCategory.Fin

open CategoryTheory Simplicial MonoidalCategory Opposite

universe u

namespace SSet

section

variable (X Y : SSet.{u})

section

variable {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n) (z : (X ⊗ Y).obj m)
@[simp] lemma prod_map_fst : ((X ⊗ Y).map f z).1 = X.map f z.1 := rfl
@[simp] lemma prod_map_snd : ((X ⊗ Y).map f z).2 = Y.map f z.2 := rfl

end

@[simp] lemma prod_δ_fst {n : ℕ} (i : Fin (n + 2)) (z : (X ⊗ Y : SSet.{u}) _[n + 1]) :
    ((X ⊗ Y).δ i z).1 = X.δ i z.1 := rfl
@[simp] lemma prod_δ_snd {n : ℕ} (i : Fin (n + 2)) (z : (X ⊗ Y : SSet.{u}) _[n + 1]) :
    ((X ⊗ Y).δ i z).2 = Y.δ i z.2 := rfl
@[simp] lemma prod_σ_fst {n : ℕ} (i : Fin (n + 1)) (z : (X ⊗ Y : SSet.{u}) _[n]) :
    ((X ⊗ Y).σ i z).1 = X.σ i z.1 := rfl
@[simp] lemma prod_σ_snd {n : ℕ} (i : Fin (n + 1)) (z : (X ⊗ Y : SSet.{u}) _[n]) :
    ((X ⊗ Y).σ i z).2 = Y.σ i z.2 := rfl

end

namespace standardSimplex

lemma objMk_injective {n : SimplexCategory} {m : SimplexCategoryᵒᵖ} :
    Function.Injective (objMk (n := n) (m := m)) := fun _ _ ↦
  congr_arg (SimplexCategory.Hom.toOrderHom ∘ objEquiv _ _)

def objMk₁ {n : ℕ} (i : Fin (n + 2)) : Δ[1] _[n] :=
  objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        by_cases hi : j₁.castSucc < i
        · simp [if_pos hi]
        · rw [if_neg hi, if_neg (fun hj' ↦ hi (lt_of_le_of_lt (by simpa using h) hj'))] }

lemma objMk₁_injective {n : ℕ} : Function.Injective (objMk₁ (n := n)) := by
  intro i j h
  wlog hij : i < j generalizing i j
  · simp only [not_lt] at hij
    obtain hij | rfl := hij.lt_or_eq
    · exact (this h.symm hij).symm
    · rfl
  have := DFunLike.congr_fun (objMk_injective h)
    ⟨i.1, lt_of_lt_of_le hij (by dsimp; omega)⟩
  simp [if_pos hij] at this

lemma objMk₁_surjective {n : ℕ} : Function.Surjective (objMk₁ (n := n)) := by
  intro f
  let S : Finset (Fin (n + 1)) := { i | f i = 1}
  by_cases hS : S.Nonempty
  · refine ⟨(S.min' hS).castSucc, ?_⟩
    ext i : 1
    dsimp [objMk₁]
    split_ifs with h
    · have hi : i ∉ S := fun hi ↦ by
        have := S.min'_le _ hi
        rw [Fin.le_iff_val_le_val] at this
        rw [Fin.lt_iff_val_lt_val] at h
        dsimp at h
        omega
      obtain ⟨j, hj⟩ : ∃ (j : Fin 2), f i = j := ⟨_, rfl⟩
      fin_cases j
      · exact hj.symm
      · exfalso
        exact hi (by simpa [S])
    · simp only [Fin.castSucc_lt_castSucc_iff, Finset.lt_min'_iff, not_forall, Classical.not_imp,
        not_lt] at h
      obtain ⟨j, hj, hij⟩ := h
      replace hj : f j = 1 := by simpa [S] using hj
      have : f j ≤ f i := (objEquiv _ _ f).toOrderHom.monotone hij
      exact le_antisymm (by simpa [hj] using this) (by omega)
  · refine ⟨Fin.last _, ?_⟩
    ext i : 1
    dsimp [objMk₁]
    rw [if_pos (by simp [Fin.lt_iff_val_lt_val])]
    obtain ⟨j, hj⟩ : ∃ (j : Fin 2), f i = j := ⟨_, rfl⟩
    fin_cases j
    · simp [hj]
    · exact (hS ⟨i, by simpa [S]⟩).elim

end standardSimplex

namespace prodStandardSimplex

variable {p q : ℕ}

def objEquiv {n : ℕ} :
    (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n] ≃ (Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) where
  toFun := fun ⟨x, y⟩ ↦ OrderHom.prod
      ((standardSimplex.objEquiv _ _ x).toOrderHom)
      ((standardSimplex.objEquiv _ _ y).toOrderHom)
  invFun f :=
    ⟨(standardSimplex.objEquiv _ _ ).symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      (standardSimplex.objEquiv _ _ ).symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ ↦ by simp
  right_inv _ := rfl

@[simp]
lemma objEquiv_apply_fst {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) (i : Fin (n + 1)) :
    (objEquiv x i).1 = x.1 i := rfl

@[simp]
lemma objEquiv_apply_snd {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) (i : Fin (n + 1)) :
    (objEquiv x i).2 = x.2 i := rfl

lemma objEquiv_naturality {m n : ℕ} (f : ([m] : SimplexCategory) ⟶ [n])
    (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) :
    (objEquiv z).comp f.toOrderHom = objEquiv ((Δ[p] ⊗ Δ[q]).map f.op z) :=
  rfl

lemma objEquiv_map_apply {n m : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) (f : ([m] : SimplexCategory) ⟶ [n]) (i : Fin (m + 1)) :
      objEquiv ((Δ[p] ⊗ Δ[q]).map f.op x) i =  objEquiv x (f.toOrderHom i) :=
  rfl

def obj₀Equiv : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[0] ≃ Fin (p + 1) × Fin (q + 1) :=
  objEquiv.trans Fin.oneOrderHomEquiv

noncomputable abbrev subsimplex {n : ℕ} (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) :
    (Δ[p] ⊗ Δ[q] : SSet.{u}).Subcomplex :=
  Subcomplex.ofSimplex (objEquiv.symm f)

lemma subsimplex_obj_zero {n : ℕ} (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) :
    (subsimplex f).obj (op [0]) =
      Set.image (obj₀Equiv.{u}).symm (Set.range f) := by
  ext x
  simp [subsimplex]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, rfl⟩ := standardSimplex.obj₀Equiv.symm.surjective x
    exact ⟨i, rfl⟩
  · rintro ⟨i, hx⟩
    exact ⟨standardSimplex.obj₀Equiv.symm i, obj₀Equiv.injective (by rw [← hx]; rfl)⟩

lemma mem_subsimplex_iff {n : ℕ} (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)) {m : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[m]) :
    x ∈ (subsimplex f).obj _ ↔ Set.range (objEquiv x) ⊆ Set.range f := by
  constructor
  · rintro ⟨x, rfl⟩ _ ⟨i, rfl⟩
    obtain ⟨g, rfl⟩ := (standardSimplex.objEquiv _ _).symm.surjective x
    exact ⟨g.toOrderHom i, rfl⟩
  · intro hf
    let S (i : Fin (m + 1)) : Finset (Fin (n + 1)) := { j | f j = objEquiv x i }
    have hS (i : Fin (m + 1)) : (S i).Nonempty := by
      obtain ⟨j, hj⟩ := hf (Set.mem_range_self i)
      exact ⟨j, by simpa [S] using hj⟩
    let φ (i : Fin (m + 1)) : Fin (n + 1) := (S i).min' (hS i)
    have hφ (i : Fin (m + 1)) : f (φ i) = objEquiv x i := by
      simpa [S] using (S i).min'_mem (hS i)
    refine ⟨standardSimplex.objMk { toFun := φ, monotone' := ?_ }, ?_⟩
    · intro i₁ i₂ h₁
      obtain h₂ | h₂ := ((objEquiv x).monotone h₁).lt_or_eq
      · simp only [← hφ] at h₂
        by_contra! h₃
        have h₄ := lt_of_lt_of_le h₂ (f.monotone h₃.le)
        simp at h₄
      · simp [φ, S, h₂]
    · apply objEquiv.injective
      ext i : 2
      rw [← hφ]
      rfl

lemma mem_ofSimplex_iff {n : ℕ} (y : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) {m : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[m]) :
    x ∈ (Subcomplex.ofSimplex y).obj _ ↔
      Set.range (objEquiv x) ⊆ Set.range (objEquiv y) := by
  rw [← mem_subsimplex_iff]
  rfl

lemma subsimplex_le_subsimplex_iff {n m : ℕ}
    (f : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1))
    (g : Fin (m + 1) →o Fin (p + 1) × Fin (q + 1)) :
    subsimplex.{u} f ≤ subsimplex.{u} g ↔
      Set.range f ⊆ Set.range g := by
  constructor
  · intro h
    simpa [subsimplex_obj_zero] using h (op [0])
  · rintro h ⟨k⟩ x
    induction' k using SimplexCategory.rec with k
    simp only [mem_subsimplex_iff]
    intro h'
    exact h'.trans h

lemma objEquiv_non_degenerate_iff {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) :
    z ∈ (Δ[p] ⊗ Δ[q]).NonDegenerate n ↔ Function.Injective (objEquiv z) := by
  rw [Fin.orderHom_injective_iff, ← not_iff_not,
    ← mem_degenerate_iff_non_mem_nondegenerate]
  simp only [not_forall, ne_eq, Decidable.not_not]
  obtain _ | n := n
  · simp
  · simp only [degenerate_eq_iUnion_range_σ, Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_range]
    apply exists_congr
    intro i
    constructor
    · rintro ⟨x, rfl⟩
      simp [SimplicialObject.σ, ← objEquiv_naturality, SimplexCategory.σ]
    · intro h₁
      refine ⟨SimplicialObject.δ (Δ[p] ⊗ Δ[q] : SSet.{u}) i.castSucc z, ?_⟩
      apply objEquiv.injective
      ext j : 2
      dsimp [SimplicialObject.σ, SimplicialObject.δ,
        SimplexCategory.σ, SimplexCategory.δ]
      rw [← objEquiv_naturality, ← objEquiv_naturality]
      dsimp
      by_cases h₂ : j = i.castSucc
      · simpa [h₂] using h₁.symm
      · rw [Fin.succAbove_predAbove h₂]

lemma non_degenerate_iff' (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) :
    z ∈ (Δ[p] ⊗ Δ[q]).NonDegenerate n ↔
      Function.Injective (((SSet.yonedaEquiv _ _ ).symm z).app (op [0])) := by
  have this : ((((Δ[p] ⊗ Δ[q]).yonedaEquiv [n]).symm z).app (op [0])) =
      obj₀Equiv.{u}.invFun.comp ((objEquiv z).toFun.comp
        standardSimplex.obj₀Equiv.{u}.toFun) := by
    ext i
    exact obj₀Equiv.injective (by rfl)
  simp [objEquiv_non_degenerate_iff, this]

lemma strictMono_of_nonDegenerate {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate n) :
    StrictMono (objEquiv x.1) := by
  obtain ⟨x, hx⟩ := x
  simpa only [objEquiv_non_degenerate_iff,
    (objEquiv x).monotone.strictMono_iff_injective] using hx

@[simps coe]
def orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) {m : ℕ} (hm : p + q = m) :
    Fin (n + 1) →o Fin (m + 1) where
  toFun i := ⟨(x.1 i : ℕ) + x.2 i, by omega⟩
  monotone' i j h := by
    dsimp
    simp only [Fin.mk_le_mk]
    have := (objEquiv x).monotone h
    have h₁ : x.1 i ≤ x.1 j := this.1
    have h₂ : x.2 i ≤ x.2 j := this.2
    omega

lemma strictMono_orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate n) {m : ℕ}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x.1 hm) := by
  intro i j hij
  dsimp
  simp only [Fin.mk_lt_mk]
  obtain hij | hij := Prod.lt_iff.1 (strictMono_of_nonDegenerate x hij)
  · have : x.1.1 i < x.1.1 j := hij.1
    have : x.1.2 i ≤ x.1.2 j := hij.2
    omega
  · have : x.1.1 i ≤ x.1.1 j := hij.1
    have : x.1.2 i < x.1.2 j := hij.2
    omega

lemma le_orderHomOfSimplex {n : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate n) {m : ℕ}
    (hm : p + q = m) (i : Fin (n + 1)) : i.1 ≤ orderHomOfSimplex x.1 hm i := by
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => simp
  | succ i hi' =>
      have h : (⟨i, by omega⟩ : Fin (n + 1)) < ⟨i + 1, hi⟩ := by simp
      simpa only [Nat.succ_le_iff] using
        lt_of_le_of_lt (hi' (by omega)) (strictMono_orderHomOfSimplex x hm h)

instance : (Δ[p] ⊗ Δ[q] : SSet.{u}).HasDimensionLT (p + q + 1) where
  degenerate_eq_top n hn := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true,
      mem_degenerate_iff_non_mem_nondegenerate]
    intro hx
    have := Fintype.card_le_of_injective _
      ((strictMono_orderHomOfSimplex ⟨x, hx⟩ rfl).injective)
    simp only [Fintype.card_fin, add_le_add_iff_right] at this
    omega

lemma non_degenerate_iff {n : ℕ} (z : (Δ[p] ⊗ Δ[q] : SSet.{u}) _[n]) (hn : p + q = n) :
    z ∈ (Δ[p] ⊗ Δ[q]).NonDegenerate n ↔ orderHomOfSimplex z hn = .id := by
  constructor
  · intro h
    exact Fin.eq_id_of_strictMono _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn)
  · rw [objEquiv_non_degenerate_iff]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a, ← h b]
    rw [Fin.ext_iff]
    change ((objEquiv z a).1 : ℕ) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]

lemma nonDegenerate_ext {n : ℕ} {z₁ z₂ : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate n}
    (hn : p + q = n) (h : z₁.1.1 = z₂.1.1) :
    z₁ = z₂ := by
  ext
  apply objEquiv.injective
  dsimp
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [non_degenerate_iff _ hn] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using DFunLike.congr_fun (h₁.trans h₂.symm) i

lemma _root_.Fin.prod_zero_zero_lt_iff (i : Fin (p + 1) × Fin (q + 1)) :
    (0, 0) < i ↔ 0 < i.1.1 + i.2.1 := by
  rw [Prod.lt_iff]
  aesop

lemma _root_.Fin.prod_lt_last_last_iff (i : Fin (p + 1) × Fin (q + 1)) :
    i < (Fin.last _, Fin.last _) ↔ i.1.1 + i.2.1 < p + q := by
  simp only [Prod.lt_iff]
  constructor
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    all_goals
      simp [Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val] at h₁ h₂
      omega
  · intro h
    obtain h₁ | h₁ := (Fin.le_last i.1).lt_or_eq
    · exact Or.inl ⟨h₁, Fin.le_last _⟩
    · exact Or.inr ⟨by rw [h₁], by simpa [h₁] using h⟩

lemma _root_.SSet.yonedaEquiv_symm_app_apply {X : SSet.{u}} {n : SimplexCategoryᵒᵖ}
    (x : X.obj n) {m : SimplexCategoryᵒᵖ} (y : (standardSimplex.obj n.unop).obj m) :
    ((X.yonedaEquiv n.unop).symm x).app m y = X.map (standardSimplex.objEquiv _ _ y).op x :=
  rfl

lemma _root_.Fin.prod_exists_intermediate (k₀ k₂ : Fin (p + 1) × Fin (q + 1))
    (h₀₂ : k₀ ≤ k₂)
    (h : k₀.1.1 + k₀.2.1 + 2 ≤ k₂.1.1 + k₂.2.1) :
    ∃ k₁, k₀ < k₁ ∧ k₁ < k₂ := by
  obtain ⟨x₀, y₀⟩ := k₀
  obtain ⟨x₂, y₂⟩ := k₂
  simp only [Prod.le_def] at h₀₂ h
  obtain ⟨hx, hy⟩ := h₀₂
  obtain hx' | rfl := hx.lt_or_eq
  · obtain hy' | rfl := hy.lt_or_eq
    · exact ⟨⟨x₀, y₂⟩, by aesop⟩
    · obtain ⟨x₂', rfl⟩ := x₂.eq_succ_of_ne_zero (fun hx₂ ↦ by
        rw [Fin.ext_iff] at hx₂
        dsimp at hx₂
        omega)
      refine ⟨⟨x₂'.castSucc, y₀⟩, ?_⟩
      rw [Fin.val_succ] at h
      simp [Fin.lt_iff_val_lt_val]
      omega
  · obtain ⟨y₂', rfl⟩ := y₂.eq_succ_of_ne_zero (fun hy₂ ↦ by
      rw [Fin.ext_iff] at hy₂
      dsimp at hy₂
      omega)
    refine ⟨⟨x₀, y₂'.castSucc⟩, ?_⟩
    rw [Fin.val_succ] at h
    simp [Fin.lt_iff_val_lt_val]
    omega

lemma nondegenerate_mem_ofSimplex_aux {d : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate d) (hd : d < p + q) :
    ∃ (y : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate (d + 1)),
      x.1 ∈ (Subcomplex.ofSimplex y.1).obj _ := by
  let S : Finset (Fin (d + 1)) :=
    { i | ⟨i.1, by omega⟩ < orderHomOfSimplex x.1 rfl i }
  by_cases hS : S.Nonempty
  · obtain ⟨i₀, hi₀⟩ : ∃ i₀, i₀ = S.min' hS := ⟨_, rfl⟩
    obtain rfl | ⟨i₀, rfl⟩ := Fin.eq_zero_or_eq_succ i₀
    · have h := Fin.strictMono_insert_zero (objEquiv x.1)
        (strictMono_of_nonDegenerate x) ⟨0, 0⟩ (by
          simpa only [← hi₀, S, Finset.mem_filter, Finset.mem_univ,
            true_and, _root_.Fin.prod_zero_zero_lt_iff]
              using S.min'_mem hS)
      exact ⟨⟨_, (objEquiv_non_degenerate_iff
        (objEquiv.{u}.symm ⟨_, h.monotone⟩)).2 h.injective⟩,
        (standardSimplex.objEquiv _ _).symm
          (SimplexCategory.δ 0), objEquiv.injective rfl⟩
    · obtain ⟨k, hk₁, hk₂⟩ := Fin.prod_exists_intermediate (objEquiv x.1 i₀.castSucc)
        (objEquiv x.1 i₀.succ) ((objEquiv x.1).monotone i₀.castSucc_le_succ) (by
          have h₀ : i₀.castSucc ∉ S := fun h₀ ↦ by
            have := S.min'_le _ h₀
            simp [← hi₀] at this
          have h₁ : i₀.succ ∈ S := by
            simpa only [hi₀] using S.min'_mem hS
          simp [S] at h₀ h₁ ⊢
          omega)
      have h := Fin.strictMono_insert (objEquiv x.1)
        (strictMono_of_nonDegenerate x) i₀ k hk₁ hk₂
      refine ⟨⟨_, (objEquiv_non_degenerate_iff
        (objEquiv.{u}.symm ⟨_, h.monotone⟩)).2 h.injective⟩,
        (standardSimplex.objEquiv _ _).symm
          (SimplexCategory.δ i₀.succ.castSucc), objEquiv.injective ?_⟩
      ext j : 2
      rw [SSet.yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply, objEquiv_map_apply,
        Equiv.apply_symm_apply]
      dsimp [SimplexCategory.δ]
      rw [← Fin.succ_castSucc, Fin.insert_apply_succAbove]
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    have h := Fin.strictMono_insert_last (objEquiv x.1)
      (strictMono_of_nonDegenerate x) ⟨Fin.last _, Fin.last _⟩ (by
        rw [_root_.Fin.prod_lt_last_last_iff]
        refine lt_of_le_of_lt ?_ hd
        simpa [← hS, S] using Finset.not_mem_empty (Fin.last d))
    refine ⟨⟨_, (objEquiv_non_degenerate_iff
      (objEquiv.{u}.symm ⟨_, h.monotone⟩)).2 h.injective⟩,
      (standardSimplex.objEquiv _ _).symm
        (SimplexCategory.δ (Fin.last _)), objEquiv.injective ?_⟩
    ext j : 2
    rw [SSet.yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply, objEquiv_map_apply,
      Equiv.apply_symm_apply]
    dsimp [SimplexCategory.δ]
    rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_last j),
      Fin.insert_last_castSucc]

lemma nondegenerate_mem_ofSimplex {d : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate d) {n : ℕ} (hn : p + q = n) :
    ∃ (y : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate n),
      x.1 ∈ (Subcomplex.ofSimplex y.1).obj _ := by
  subst hn
  have hd := Nat.le_of_lt_succ (dim_lt_of_nondegenerate _ x (p + q + 1))
  obtain ⟨i, hi⟩ := Nat.le.dest hd
  induction i generalizing d with
  | zero =>
      obtain rfl : d = p + q := by omega
      exact ⟨x, Subcomplex.mem_ofSimplex_obj _⟩
  | succ d' hd' =>
      obtain ⟨y, hy⟩ := nondegenerate_mem_ofSimplex_aux x (by omega)
      obtain ⟨z, hz⟩ := hd' y (by omega) (by omega)
      rw [← Subcomplex.ofSimplex_le_iff] at hz
      exact ⟨z, hz _ hy⟩

lemma subcomplex_eq_top_iff (A : (Δ[p] ⊗ Δ[q] : SSet.{u}).Subcomplex)
    {n : ℕ} (hn : p + q = n) :
    A = ⊤ ↔ (Δ[p] ⊗ Δ[q]).NonDegenerate n ⊆ A.obj (op [n]) := by
  constructor
  · rintro rfl
    simp
  · intro h
    apply le_antisymm le_top
    simp only [Subcomplex.le_iff_contains_nonDegenerate, Subtype.forall,
      top_subpresheaf_obj, Set.top_eq_univ, Set.mem_univ, forall_const]
    intro d x hx
    obtain ⟨y, hy⟩ := nondegenerate_mem_ofSimplex ⟨x, hx⟩ hn
    exact (Subcomplex.ofSimplex_le_iff _ _).2 (h y.2) _ hy

instance {k : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate k) :
    Mono ((yonedaEquiv _ _).symm x.1) := by
  obtain ⟨x, hx⟩ := x
  rw [objEquiv_non_degenerate_iff] at hx
  rw [NatTrans.mono_iff_mono_app]
  intro m
  rw [mono_iff_injective]
  intro a b h
  replace h : (objEquiv x).comp (asOrderHom a) = (objEquiv x).comp (asOrderHom b) :=
    objEquiv.symm.injective h
  ext i : 4
  exact hx (DFunLike.congr_fun h i)

noncomputable def isoOfNonDegenerate
    {k : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate k) :
    Δ[k] ≅ Subcomplex.ofSimplex x.1 :=
  standardSimplex.isoOfRepresentableBy
    (Subcomplex.ofSimplexRepresentableBy x.1)

@[reassoc (attr := simp)]
lemma isoOfNonDegenerate_hom_ι {k : ℕ} (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).NonDegenerate k) :
    (isoOfNonDegenerate x).hom ≫ (Subcomplex.ofSimplex x.1).ι =
      (yonedaEquiv _ _).symm x.1 := rfl

namespace nonDegenerateEquiv₁

def toFun (i : Fin (q + 1)) : (Δ[1] ⊗ Δ[q]).NonDegenerate (q + 1) :=
  ⟨⟨standardSimplex.objMk₁ i.succ.castSucc,
    (standardSimplex.objEquiv _ _).symm (SimplexCategory.σ i)⟩, by
      rw [objEquiv_non_degenerate_iff, Fin.orderHom_injective_iff]
      intro j h
      have h₁ := congr_arg Prod.fst h
      have h₂ := congr_arg Prod.snd h
      simp [objEquiv, standardSimplex.objMk₁, SimplexCategory.σ] at h₁ h₂
      by_cases h₃ : j ≤ i
      · have h₂' := congr_arg Fin.val h₂
        rw [Fin.predAbove_of_le_castSucc _ _  h₃] at h₂'
        obtain h₃ | rfl := h₃.lt_or_eq
        · rw [Fin.predAbove_of_le_castSucc] at h₂'; swap
          · rw [Fin.lt_iff_val_lt_val, Fin.val_fin_lt] at h₃
            rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.coe_castSucc]
            omega
          · simp [Fin.castPred, Fin.castLT] at h₂'
        · simp at h₁
      · simp at h₃
        rw [Fin.lt_iff_val_lt_val] at h₃
        rw [Fin.predAbove_of_castSucc_lt] at h₂; swap
        · simpa only [Fin.lt_iff_val_lt_val, Fin.coe_castSucc] using h₃
        have hj : j.castSucc ≠ 0 := fun hj ↦ by
          simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_zero] at hj
          simp [hj] at h₃
        have := i.predAbove_of_castSucc_lt j.succ (by
          rw [Fin.lt_iff_val_lt_val, Fin.coe_castSucc, Fin.val_succ]
          apply h₃.trans (lt_add_one _))
        change j.castSucc.pred hj = i.predAbove j.succ at h₂
        rw [this] at h₂
        replace h₂ := congr_arg Fin.val h₂
        dsimp at h₂
        omega⟩

end nonDegenerateEquiv₁

noncomputable def nonDegenerateEquiv₁ :
    Fin (q + 1) ≃ (Δ[1] ⊗ Δ[q] : SSet.{u}).NonDegenerate (q + 1) :=
  Equiv.ofBijective nonDegenerateEquiv₁.toFun (by
    constructor
    · intro i j h
      simpa using standardSimplex.objMk₁_injective (congr_arg (Prod.fst ∘ Subtype.val) h)
    · intro x
      obtain ⟨i, hi⟩ := standardSimplex.objMk₁_surjective x.1.1
      have hx := (non_degenerate_iff _ (add_comm 1 q)).1 x.2
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by
        rintro rfl
        replace hi : x.1.1 0 = 1 := DFunLike.congr_fun hi.symm 0
        have := DFunLike.congr_fun hx 0
        simp [Fin.ext_iff, hi] at this)
      obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
      · exact ⟨i, nonDegenerate_ext (add_comm _ _) hi⟩
      · replace hi : x.1.1 (Fin.last _) = 0 := by
          rw [hi.symm]
          simp [standardSimplex.objMk₁, Fin.ext_iff]
        have := DFunLike.congr_fun hx (Fin.last _)
        dsimp at this
        simp only [hi, Fin.isValue, Fin.val_zero, zero_add, Fin.ext_iff, Fin.val_last] at this
        omega)

@[simp]
lemma nonDegenerateEquiv₁_fst (i : Fin (q + 1)) :
    (nonDegenerateEquiv₁ i).1.1 =
      standardSimplex.objMk₁ i.succ.castSucc := rfl

@[simp]
lemma nonDegenerateEquiv₁_snd (i : Fin (q + 1)) :
    (nonDegenerateEquiv₁ i).1.2 =
      (standardSimplex.objEquiv _ _).symm (SimplexCategory.σ i) := rfl

end prodStandardSimplex

end SSet
