import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import TopCatModelCategory.SSet.Monoidal

open CategoryTheory Simplicial MonoidalCategory Opposite CartesianMonoidalCategory

universe u

namespace SSet

namespace prodStdSimplex₁

variable {n : ℕ}

noncomputable def nonDegenerateEquiv :
    Fin (n + 1) ≃ (Δ[n] ⊗ Δ[1] : SSet.{u}).nonDegenerate (n + 1) :=
  prodStdSimplex.nonDegenerateEquiv₁.{u}.trans
    (nonDegenerateEquivOfIso (β_ _ _) _)

@[simp]
lemma nonDegenerateEquiv_fst (i : Fin (n + 1)) :
    (nonDegenerateEquiv i).1.1 =
      stdSimplex.objEquiv.symm (SimplexCategory.σ i) := rfl

@[simp]
lemma nonDegenerateEquiv_snd (i : Fin (n + 1)) :
    (nonDegenerateEquiv i).1.2 =
      stdSimplex.objMk₁ i.succ.castSucc := rfl

lemma mem_range_objEquiv_nonDegenerateEquiv₀_iff (i x : Fin (n + 1)) :
    (x, 0) ∈ Set.range (prodStdSimplex.objEquiv (nonDegenerateEquiv i).1) ↔ x ≤ i := by
  constructor
  · rintro ⟨y, hy⟩
    have hy₁ := congr_arg Prod.fst hy
    have hy₂ := congr_arg Prod.snd hy
    dsimp at hy₁ hy₂
    rw [stdSimplex.objMk₁_apply_eq_zero_iff, Fin.succ_castSucc,
      Fin.castSucc_lt_castSucc_iff] at hy₂
    erw [← hy₁, stdSimplex.objEquiv_symm_σ_apply,
      Fin.predAbove_of_lt_succ _ _ hy₂, ← Fin.castSucc_le_castSucc_iff,
      Fin.castSucc_castPred, Fin.le_castSucc_iff]
    exact hy₂
  · intro hx
    refine ⟨x.castSucc, Prod.ext ?_ ?_⟩
    · dsimp
      erw [stdSimplex.objEquiv_symm_σ_apply,
        Fin.predAbove_of_le_castSucc _ _ (by simpa),
        Fin.castPred_castSucc]
    · simpa [stdSimplex.objMk₁_apply_eq_zero_iff]

lemma mem_range_objEquiv_nonDegenerateEquiv₁_iff (i x : Fin (n + 1)) :
    (x, 1) ∈ Set.range (prodStdSimplex.objEquiv (nonDegenerateEquiv i).1) ↔ i ≤ x := by
  constructor
  · rintro ⟨y, hy⟩
    have hy₁ := congr_arg Prod.fst hy
    have hy₂ := congr_arg Prod.snd hy
    dsimp at hy₁ hy₂
    rw [stdSimplex.objMk₁_apply_eq_one_iff, Fin.succ_castSucc, Fin.castSucc_le_castSucc_iff] at hy₂
    erw [← hy₁, stdSimplex.objEquiv_symm_σ_apply, Fin.predAbove_of_succ_le _ _ hy₂,
      ← Fin.succ_le_succ_iff, Fin.succ_pred]
    exact hy₂
  · intro hx
    refine ⟨x.succ, Prod.ext ?_ ?_⟩
    · dsimp
      erw [stdSimplex.objEquiv_symm_σ_apply,
        Fin.predAbove_of_succ_le _ _ (by simpa), Fin.pred_succ]
    · simpa [stdSimplex.objMk₁_apply_eq_one_iff]

noncomputable def filtration (j : Fin (n + 1)) : (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  ⨆ (i : ({i // i ≤ j} : Type)), .ofSimplex (nonDegenerateEquiv i.1).1

lemma ofSimplex_le_filtration {i j : Fin (n + 1)} (hij : i ≤ j) :
    .ofSimplex (nonDegenerateEquiv i).1 ≤ filtration.{u} j :=
  le_iSup (fun (i : {i // i ≤ j}) ↦
    Subcomplex.ofSimplex (nonDegenerateEquiv i.1).1) ⟨i, hij⟩

variable (n) in
lemma filtration_zero :
    filtration.{u} (0 : Fin (n + 1)) = .ofSimplex (nonDegenerateEquiv 0).1 :=
  le_antisymm (by simpa [filtration] using Subcomplex.mem_ofSimplex_obj _)
    (ofSimplex_le_filtration.{u} (by rfl))

variable (n) in
lemma filtration_last :
    filtration.{u} (Fin.last n) = ⊤ := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
  intro x hx
  obtain ⟨i, hi⟩ := nonDegenerateEquiv.surjective ⟨x, hx⟩
  rw [Subtype.ext_iff] at hi
  subst hi
  rw [← Subcomplex.ofSimplex_le_iff]
  exact ofSimplex_le_filtration i.le_last

noncomputable def intersectionNondeg (i j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1] : SSet.{u}).Subcomplex :=
  .ofSimplex (nonDegenerateEquiv i).1 ⊓ .ofSimplex (nonDegenerateEquiv j).1

@[simps coe_fst coe_snd]
def codimOneSimplex (j : Fin (n + 2)) : (Δ[n] ⊗ Δ[1] : SSet.{u}).nonDegenerate n :=
  ⟨⟨stdSimplex.objMk .id, stdSimplex.objMk₁ j⟩, by
    have := stdSimplex.id_nonDegenerate.{u} n
    rw [mem_nonDegenerate_iff_notMem_degenerate] at this ⊢
    intro h
    exact this (degenerate_map h (fst _ _))⟩

lemma δ_castSucc_nonDegenerateEquiv (j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1]).δ j.castSucc (nonDegenerateEquiv j).1 =
      (codimOneSimplex j.castSucc).1 := by
  apply Prod.ext
  · exact stdSimplex.objEquiv.injective SimplexCategory.δ_comp_σ_self
  · dsimp
    rw [stdSimplex.δ_objMk₁_of_lt _ _ (by simp), Fin.pred_succ]

lemma δ_succ_nonDegenerateEquiv (j : Fin (n + 1)) :
    (Δ[n] ⊗ Δ[1]).δ j.succ (nonDegenerateEquiv j).1 =
      (codimOneSimplex j.succ).1 := by
  apply Prod.ext
  · exact stdSimplex.objEquiv.injective SimplexCategory.δ_comp_σ_succ
  · dsimp
    rw [stdSimplex.δ_objMk₁_of_le _ _ (by simp)]
    simp only [Fin.succ_castSucc, Fin.castPred_castSucc]

lemma ofSimplex_codimOneSimplex (j : Fin n) :
    Subcomplex.ofSimplex (codimOneSimplex.{u} j.succ.castSucc).1 =
      intersectionNondeg j.castSucc j.succ := by
  apply le_antisymm
  · dsimp [intersectionNondeg]
    simp only [le_inf_iff, Subcomplex.ofSimplex_le_iff,
      Subcomplex.mem_ofSimplex_obj_iff]
    constructor
    · refine ⟨SimplexCategory.δ j.succ.castSucc, ?_⟩
      rw [← Fin.succ_castSucc, ← δ_succ_nonDegenerateEquiv]
      rfl
    · refine ⟨SimplexCategory.δ j.succ.castSucc, ?_⟩
      rw [Fin.succ_castSucc, ← δ_castSucc_nonDegenerateEquiv]
      rfl
  · rintro ⟨k⟩ s hs
    induction' k using SimplexCategory.rec with k
    obtain ⟨f, rfl⟩ := prodStdSimplex.objEquiv.symm.surjective s
    simp only [prodStdSimplex.mem_ofSimplex_iff, intersectionNondeg,
      Subpresheaf.min_obj, Set.mem_inter_iff, Equiv.apply_symm_apply] at hs ⊢
    rintro ⟨x, y⟩ hxy
    refine ⟨x, Prod.ext rfl ?_⟩
    obtain ⟨x₁, h₁⟩ := hs.1 hxy
    obtain ⟨x₂, h₂⟩ := hs.2 hxy
    have h₁₁ := congr_arg Prod.fst h₁
    have h₁₂ := congr_arg Prod.snd h₁
    have h₂₁ := congr_arg Prod.fst h₂
    have h₂₂ := congr_arg Prod.snd h₂
    simp only [prodStdSimplex.objEquiv_apply_fst, nonDegenerateEquiv_fst,
      prodStdSimplex.objEquiv_apply_snd, nonDegenerateEquiv_snd] at h₁₁ h₁₂ h₂₁ h₂₂
    erw [stdSimplex.objEquiv_symm_σ_apply] at h₁₁ h₂₁
    simp only [prodStdSimplex.objEquiv_apply_snd, codimOneSimplex_coe_snd]
    fin_cases y
    · simp [stdSimplex.objMk₁_apply_eq_zero_iff,
        ← Fin.le_castSucc_iff] at h₁₂ h₂₂ ⊢
      rw [Fin.predAbove_of_le_castSucc _ _ h₁₂] at h₁₁
      simpa [← h₁₁] using h₁₂
    · simp [stdSimplex.objMk₁_apply_eq_one_iff] at h₁₂ h₂₂ ⊢
      rw [Fin.predAbove_of_castSucc_lt _ _ h₂₂] at h₂₁
      rwa [← h₂₁, ← Fin.succ_lt_succ_iff, Fin.succ_pred]

lemma intersectionNondeg_le_intersectionNondeg (i j k : Fin (n + 1))
    (hij : i ≤ j) (hij : j ≤ k) :
    intersectionNondeg.{u} i k ≤ intersectionNondeg.{u} j k := by
  rintro ⟨k⟩ x hx
  induction' k using SimplexCategory.rec with k
  dsimp [intersectionNondeg] at hx ⊢
  simp only [Set.mem_inter_iff, prodStdSimplex.mem_ofSimplex_iff,
    ← Set.subset_inter_iff] at hx ⊢
  apply hx.trans
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_inter_iff] at hxy ⊢
  fin_cases y
  all_goals
  · dsimp at hxy ⊢
    simp only [mem_range_objEquiv_nonDegenerateEquiv₀_iff,
      mem_range_objEquiv_nonDegenerateEquiv₁_iff] at hxy ⊢
    omega

lemma intersectionNondeg_le_intersectionNondeg' (i j k : Fin (n + 1))
    (hij : i ≤ j) (hij : j ≤ k) :
    intersectionNondeg.{u} i k ≤ intersectionNondeg.{u} i j := by
  rintro ⟨k⟩ x hx
  induction' k using SimplexCategory.rec with k
  dsimp [intersectionNondeg] at hx ⊢
  simp only [Set.mem_inter_iff, prodStdSimplex.mem_ofSimplex_iff,
    ← Set.subset_inter_iff] at hx ⊢
  apply hx.trans
  rintro ⟨x, y⟩ hxy
  simp only [Set.mem_inter_iff] at hxy ⊢
  fin_cases y
  all_goals
  · dsimp at hxy ⊢
    simp only [mem_range_objEquiv_nonDegenerateEquiv₀_iff,
      mem_range_objEquiv_nonDegenerateEquiv₁_iff] at hxy ⊢
    omega

namespace filtration

lemma monotone :
    Monotone (filtration.{u} (n := n)) := by
  intro j j' h
  rw [filtration, iSup_le_iff, Subtype.forall]
  intro i hi
  exact ofSimplex_le_filtration (hi.trans h)

lemma sq (j : Fin n) :
    Subcomplex.Sq (Subcomplex.ofSimplex (codimOneSimplex.{u} j.succ.castSucc).1)
      (filtration.{u} j.castSucc) (.ofSimplex (nonDegenerateEquiv j.succ).1)
      (filtration.{u} j.succ) where
  min_eq := by
    rw [ofSimplex_codimOneSimplex]
    apply le_antisymm
    · dsimp [filtration]
      rw [Subcomplex.iSup_inf, iSup_le_iff, Subtype.forall]
      intro i hi
      exact intersectionNondeg_le_intersectionNondeg _ _ _ hi j.castSucc_le_succ
    · dsimp [intersectionNondeg]
      simp only [le_inf_iff, inf_le_right, and_true]
      exact inf_le_left.trans (ofSimplex_le_filtration (by rfl))
  max_eq := by
    apply le_antisymm
    · rw [filtration, sup_le_iff, iSup_le_iff, Subtype.forall]
      constructor
      · intro i hi
        exact ofSimplex_le_filtration (hi.trans (j.castSucc_le_succ))
      · exact ofSimplex_le_filtration (by rfl)
    · rw [filtration, iSup_le_iff, Subtype.forall]
      intro i hi
      obtain hi | rfl := hi.lt_or_eq
      · refine le_trans ?_ le_sup_left
        exact ofSimplex_le_filtration (Fin.le_castSucc_iff.2 hi)
      · exact le_sup_right

noncomputable def ι {i j : Fin (n + 1)} (hi : i ≤ j) :
    Δ[n + 1] ⟶ filtration.{u} j :=
  Subcomplex.lift
    (yonedaEquiv.symm (nonDegenerateEquiv i)) (by
      apply le_antisymm (by simp)
      rw [← Subcomplex.image_le_iff, Subcomplex.image_top]
      simp only [Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]
      exact ofSimplex_le_filtration hi)

@[reassoc (attr := simp)]
lemma ι_ι (i j : Fin (n + 1)) (hi : i ≤ j) :
    ι.{u} hi ≫ (filtration j).ι =
      yonedaEquiv.symm (nonDegenerateEquiv i) := rfl

lemma isPushout (j : Fin n) :
    IsPushout
      (stdSimplex.{u}.δ j.succ.castSucc ≫ ι (by rfl))
      (stdSimplex.δ j.succ.castSucc)
      (Subcomplex.homOfLE (filtration.monotone j.castSucc_le_succ))
      (ι (by rfl)) := by
  fapply (sq.{u} j).isPushout.of_iso'
    (stdSimplex.isoOfRepresentableBy
      (Subcomplex.ofSimplexRepresentableBy _))
    (Iso.refl _)
    (stdSimplex.isoOfRepresentableBy
      (Subcomplex.ofSimplexRepresentableBy _))
    (Iso.refl _)
  · apply Subcomplex.hom_ext
    dsimp
    simp only [Category.assoc, Category.comp_id, ι_ι]
    rw [Subcomplex.homOfLE_ι,
      Subcomplex.isoOfRepresentableBy_ofSimplexRepresentableBy_hom]
    dsimp [CosimplicialObject.δ]
    rw [← yonedaEquiv_symm_map,
      ← δ_succ_nonDegenerateEquiv]
    rfl
  · apply Subcomplex.hom_ext
    dsimp
    simp only [Category.assoc]
    rw [Subcomplex.homOfLE_ι,
      Subcomplex.isoOfRepresentableBy_ofSimplexRepresentableBy_hom,
      Subcomplex.isoOfRepresentableBy_ofSimplexRepresentableBy_hom]
    dsimp [CosimplicialObject.δ]
    rw [← yonedaEquiv_symm_map, Fin.succ_castSucc, ← δ_castSucc_nonDegenerateEquiv]
    rfl
  · simp
  · aesop_cat

variable {X : SSet.{u}} {j : Fin (n + 1)}
  (α : ∀ (i : Fin (n + 1)) (_ : i ≤ j), Δ[n + 1] ⟶ X)
  (hα : ∀ (i : Fin n) (hi : i.succ ≤ j),
    stdSimplex.δ i.succ.castSucc ≫
        α i.castSucc (i.castSucc_le_succ.trans hi) =
      stdSimplex.δ i.succ.castSucc ≫ α i.succ hi)

def exists_desc :
    ∃ (φ : (filtration j : SSet.{u}) ⟶ X),
      ∀ (i : Fin (n + 1)) (hi : i ≤ j), ι hi ≫ φ = α i hi := by
  revert α hα
  induction j using Fin.induction with
  | zero =>
    intro α hα
    refine ⟨(Subcomplex.isoOfEq (filtration_zero.{u} n)).hom ≫
      (stdSimplex.isoOfRepresentableBy
        (Subcomplex.ofSimplexRepresentableBy _)).inv ≫ α 0 (by rfl), ?_⟩
    intro i hi
    obtain rfl : i = 0 := le_antisymm hi bot_le
    trans 𝟙 _ ≫ α 0 (by rfl)
    · rw [← Category.assoc, ← Category.assoc]
      congr 1
      simp [← cancel_mono (stdSimplex.isoOfRepresentableBy
        (Subcomplex.ofSimplexRepresentableBy (nonDegenerateEquiv (0 : Fin (n + 1))).1)).hom]
      rfl
    · simp
  | succ j hj  =>
    intro α hα
    obtain ⟨β, hβ⟩ := hj (fun i hi ↦ α i (hi.trans j.castSucc_le_succ)) (fun i _ ↦ hα i _)
    obtain ⟨φ, hφ₁, hφ₂⟩ := (isPushout j).exists_desc β (α j.succ (by rfl)) (by
      rw [Category.assoc, hβ, hα])
    refine ⟨φ, fun i hi ↦ ?_⟩
    obtain hi | rfl := hi.lt_or_eq
    · rw [← Fin.le_castSucc_iff] at hi
      rw [← hβ i hi, ← hφ₁]
      rfl
    · exact hφ₂

end filtration

noncomputable def ι (i : Fin (n + 1)) : (Δ[n + 1] : SSet.{u}) ⟶ Δ[n] ⊗ Δ[1] :=
  yonedaEquiv.symm (nonDegenerateEquiv i)

@[ext]
lemma hom_ext {X : SSet.{u}} {f g : Δ[n] ⊗ Δ[1] ⟶ X}
    (h : ∀ (i : Fin (n + 1)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext ⟨m⟩ x
  induction' m using SimplexCategory.rec with m
  have hx : x ∈ (⊤ : SSet.Subcomplex _).obj _ := by simp
  simp only [← filtration_last.{u} n, filtration, Subpresheaf.iSup_obj,
    Set.mem_iUnion, Subtype.exists, exists_prop,
    Subcomplex.mem_ofSimplex_obj_iff] at hx
  obtain ⟨i, _, ⟨s, rfl⟩⟩ := hx
  apply congr_fun (NatTrans.congr_app (h i) (op ⦋m⦌))

variable {X : SSet.{u}}
  (α : Fin (n + 1) → (Δ[n + 1] ⟶ X))
  (hα : ∀ (i : Fin n),
    stdSimplex.δ i.succ.castSucc ≫ α i.castSucc =
      stdSimplex.δ i.succ.castSucc ≫ α i.succ)

def exists_desc :
    ∃ (φ : Δ[n] ⊗ Δ[1] ⟶ X),
      ∀ (i : Fin (n + 1)), ι i ≫ φ = α i := by
  obtain ⟨ψ, hψ⟩ := filtration.exists_desc (j := Fin.last n) (fun i hi ↦ α i)
    (fun i _ ↦ hα i)
  exact ⟨(Subcomplex.topIso _).inv ≫ (Subcomplex.isoOfEq (filtration_last n)).inv ≫ ψ,
    fun i ↦ by rw [← hψ i (by exact Fin.le_last i)]; rfl⟩

@[reassoc]
lemma δ_ι_last :
    stdSimplex.δ (Fin.last (n + 1)) ≫ ι (Fin.last n) = ι₀.{u} := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext i : 3
  · simpa [ι, yonedaEquiv_fst, ← yonedaEquiv_symm_map] using
      SimplexCategory.congr_toOrderHom_apply
        (SimplexCategory.δ_comp_σ_succ (i := Fin.last n)) i
  · simp [ι, yonedaEquiv_snd, ← yonedaEquiv_symm_map, stdSimplex.map_op_apply,
      CosimplicialObject.δ, SimplexCategory.δ]
    rw [stdSimplex.objMk₁_of_castSucc_lt _ _ (by simp)]
    rfl

@[reassoc]
lemma δ_ι_zero :
    stdSimplex.δ 0 ≫ ι (0 : Fin (n + 1)) = ι₁.{u} := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext i : 3
  · simpa [ι, yonedaEquiv_fst, ← yonedaEquiv_symm_map] using
      SimplexCategory.congr_toOrderHom_apply
        (SimplexCategory.δ_comp_σ_self (i := 0)) i
  · rfl

@[reassoc]
lemma ι_whiskerRight_δ_of_le (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    ι.{u} j ≫ stdSimplex.δ i ▷ Δ[1] =
      stdSimplex.δ i.castSucc ≫ ι.{u} j.succ := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext k : 3
  · exact SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_le hij).symm k
  · simp [ι, ← yonedaEquiv_symm_map, stdSimplex.map_op_apply, SimplexCategory.δ,
      CosimplicialObject.δ]
    by_cases hk : k ≤ j.castSucc
    · rw [stdSimplex.objMk₁_of_castSucc_lt _ _ (by simpa [← Fin.le_castSucc_iff]),
        stdSimplex.objMk₁_of_castSucc_lt]
      rw [Fin.succ_castSucc, Fin.succ_castSucc, Fin.castSucc_lt_castSucc_iff,
        ← Fin.le_castSucc_iff]
      by_cases hk' : k < i
      · simpa [Fin.succAbove_of_castSucc_lt i.castSucc k (by simpa)]
          using hk.trans (j.castSucc_le_succ)
      · simp only [not_lt] at hk'
        simpa only [Fin.succAbove_of_le_castSucc i.castSucc k (by simpa), ← Fin.succ_castSucc,
          Fin.succ_le_succ_iff]
    · simp only [not_le] at hk
      rw [Fin.succAbove_of_le_castSucc i.castSucc k (by simpa using hij.trans hk.le),
        stdSimplex.objMk₁_of_le_castSucc _ _ (by simpa),
        stdSimplex.objMk₁_of_le_castSucc _ _ (by simpa)]

@[reassoc]
lemma δ_ι_of_lt (i : Fin (n + 3)) (j : Fin (n + 2)) (hij : i < j.castSucc) :
  stdSimplex.δ i ≫ ι.{u} j =
    ι.{u} (j.pred (by simpa using Fin.ne_zero_of_lt hij)) ≫
      stdSimplex.δ (i.castPred (Fin.ne_last_of_lt hij)) ▷ Δ[1] := by
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by simpa using Fin.ne_zero_of_lt hij)
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hij)
  rw [Fin.pred_succ, Fin.castPred_castSucc,
    ι_whiskerRight_δ_of_le _ _ (Fin.le_castSucc_iff.2 hij)]

@[reassoc]
lemma ι_whiskerRight_δ_of_gt (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : j.castSucc < i ) :
    ι.{u} j ≫ stdSimplex.δ i ▷ Δ[1] =
      stdSimplex.δ i.succ ≫ ι.{u} j.castSucc := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext k : 3
  · exact SimplexCategory.congr_toOrderHom_apply (SimplexCategory.δ_comp_σ_of_gt hij).symm k
  · simp [ι, ← yonedaEquiv_symm_map, stdSimplex.map_op_apply, SimplexCategory.δ,
      CosimplicialObject.δ]
    by_cases hk : k < j.succ
    · have : k.castSucc < i.succ := by
        rw [← Fin.castSucc_lt_castSucc_iff] at hk
        rw [← Fin.succ_lt_succ_iff] at hij
        exact hk.trans hij
      rw [stdSimplex.objMk₁_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff] using hk),
        stdSimplex.objMk₁_of_castSucc_lt]
      rwa [Fin.succAbove_of_castSucc_lt _ _ this, Fin.succ_castSucc,
        Fin.castSucc_lt_castSucc_iff, Fin.castSucc_lt_succ_iff, Fin.le_castSucc_iff]
    · simp only [not_lt] at hk
      rw [stdSimplex.objMk₁_of_le_castSucc _ _ (by simpa using hk),
        stdSimplex.objMk₁_of_le_castSucc]
      rw [Fin.succ_castSucc, Fin.castSucc_le_castSucc_iff]
      by_cases hk' : k.castSucc < i.succ
      · simpa [Fin.succAbove_of_castSucc_lt _ _ hk'] using hk
      · simp only [Fin.castSucc_lt_succ_iff, not_le] at hk'
        rw [Fin.succAbove_of_le_castSucc _ _ (by simpa), Fin.succ_le_succ_iff]
        refine hij.le.trans hk'.le

@[reassoc]
lemma δ_ι_of_succ_lt (i : Fin (n + 3)) (j : Fin (n + 2)) (hij : j.succ < i) :
  stdSimplex.δ i ≫ ι.{u} j = ι.{u} (j.castPred (by
      rintro rfl
      simp [Fin.lt_iff_val_lt_val] at hij
      omega)) ≫
      stdSimplex.δ (i.pred (Fin.ne_zero_of_lt hij)) ▷ Δ[1] := by
  rw [ι_whiskerRight_δ_of_gt _ _ (by
    rwa [← Fin.succ_lt_succ_iff, Fin.castSucc_castPred, Fin.succ_pred])]
  simp

@[reassoc]
lemma δ_succ_castSucc_ι_succ (i : Fin n) :
    stdSimplex.δ i.succ.castSucc ≫ prodStdSimplex₁.ι.{u} i.succ =
    stdSimplex.δ i.succ.castSucc ≫ prodStdSimplex₁.ι i.castSucc := by
  apply yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  ext k : 3
  · exact SimplexCategory.congr_toOrderHom_apply
      ((SimplexCategory.δ_comp_σ_self (i := i.succ)).trans
      (SimplexCategory.δ_comp_σ_succ (i := i.castSucc)).symm) k
  · simp [ι, ← yonedaEquiv_symm_map, stdSimplex.map_op_apply, CosimplicialObject.δ,
      SimplexCategory.δ]
    by_cases hk : k < i.succ
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.le_castSucc_iff] using hk)]
      rw [stdSimplex.objMk₁_of_castSucc_lt, stdSimplex.objMk₁_of_castSucc_lt]
      . simpa [Fin.le_castSucc_iff]
      . simpa using hk.le
    · simp only [not_lt] at hk
      rw [Fin.succAbove_of_le_castSucc _ _ (by simpa using hk),
        stdSimplex.objMk₁_of_le_castSucc _ _ (by simpa using hk),
        stdSimplex.objMk₁_of_le_castSucc]
      rw [Fin.succ_castSucc, Fin.castSucc_le_castSucc_iff, Fin.succ_le_succ_iff]
      exact i.castSucc_le_succ.trans hk

end prodStdSimplex₁

end SSet
