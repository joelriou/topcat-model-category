import TopCatModelCategory.SSet.AnodyneExtensionsDefs
import TopCatModelCategory.SSet.ProdSimplex

open HomotopicalAlgebra CategoryTheory Limits SSet.modelCategoryQuillen MonoidalCategory
  Simplicial Opposite

universe u

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C] (W : MorphismProperty C) [W.IsMultiplicative]

lemma map_mem_of_fin {n : ℕ} (F : Fin (n + 1) ⥤ C)
    (hF : ∀ (i : Fin n), W (F.map (homOfLE (i.castSucc_le_succ))))
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    W (F.map f) := by
  let P (k : ℕ) := ∀ (i j : ℕ) (hj : j < n + 1) (hj' : i + k = j),
    W (F.map (homOfLE ((by simpa only [← hj'] using Nat.le_add_right i k) :
      ⟨i, lt_of_le_of_lt ((Nat.le_add_right i k).trans hj'.le) hj⟩ ≤ ⟨j, hj⟩)))
  suffices ∀ k, P k by
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    have h : i ≤ j := leOfHom f
    obtain ⟨k, hk⟩ := Nat.le.dest h
    exact this k i j (by omega) hk
  intro k
  induction k with
  | zero =>
      intro j j' h h'
      obtain rfl : j = j' := by simpa using h'
      simp only [homOfLE_refl, Functor.map_id]
      apply id_mem
  | succ k hk =>
      intro i j hj hj'
      rw [← homOfLE_comp (x := (⟨i, by omega⟩ : Fin (n + 1)))
        (y := ⟨i + k, by omega⟩) (z := ⟨j, by omega⟩) (Nat.le_add_right i k)
          (by simp only [Fin.le_def]; omega), F.map_comp]
      apply comp_mem
      · exact hk i (i + k) (by omega) rfl
      · rw [← add_assoc] at hj'
        subst hj'
        exact hF ⟨i + k, by omega⟩

end MorphismProperty

end CategoryTheory

namespace SSet

namespace anodyneExtensions

lemma δ_mem (i : Fin 2) : anodyneExtensions.{u} (stdSimplex.δ i) := by
  refine (MorphismProperty.arrow_mk_iso_iff _ ?_).2 (anodyneExtensions.horn_ι_mem 0 i.rev)
  exact Arrow.isoMk (horn₁.iso _) (Iso.refl _) (by fin_cases i <;> simp)


namespace subcomplex_unionProd_face_ι_mem

variable {n : ℕ}

noncomputable abbrev simplex (j : Fin (n + 1)) :=
  prodStdSimplex.nonDegenerateEquiv₁ j

noncomputable abbrev ιSimplex (j : Fin (n + 1)) :
    (Δ[n + 1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[n] :=
  SSet.yonedaEquiv.symm (simplex j)

noncomputable def simplexδ (j : Fin (n + 1)) (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}) _⦋n⦌ :=
  (Δ[1] ⊗ Δ[n]).δ i (simplex.{u} j)

lemma simplexδ_mem_ofSimplex (j : Fin (n + 1)) (i : Fin (n + 2)) :
    simplexδ.{u} j i ∈ (Subcomplex.ofSimplex (simplex j).1).obj _ :=
  ⟨_, rfl⟩

lemma simplexδ_snd_mem_boundary_of_gt (j : Fin (n + 2)) (i : Fin (n + 3))
    (hij : i < j.castSucc) :
    (simplexδ j i).2 ∈ (boundary _).obj _ := by
  dsimp [simplexδ, SimplicialObject.δ]
  erw [stdSimplex.map_objEquiv_symm]
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (by rintro rfl; simp at hij)
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (by
    rintro rfl
    exact hij.not_le (j.succ.castSucc.le_last))
  simp only [Fin.castSucc_lt_castSucc_iff] at hij
  rw [SimplexCategory.δ_comp_σ_of_le (by rwa [Fin.le_castSucc_iff])]
  simp only [boundary_eq_iSup, Subpresheaf.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Finset.mem_compl, Finset.mem_singleton]
  exact ⟨i, fun _ ↦ Fin.succAbove_ne _ _⟩

lemma simplexδ_snd_mem_boundary_of_lt (j : Fin (n + 2)) (i : Fin (n + 3))
    (hij : j.succ < i) :
    (simplexδ j i).2 ∈ (boundary _).obj _ := by
  dsimp [simplexδ, SimplicialObject.δ]
  erw [stdSimplex.map_objEquiv_symm]
  obtain ⟨j', rfl⟩ := j.eq_castSucc_of_ne_last (by
    rintro rfl
    exact (Fin.le_last i).not_lt hij)
  obtain ⟨i', rfl⟩ := i.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hij)
  rw [SimplexCategory.δ_comp_σ_of_gt (by simpa using hij)]
  simp only [boundary_eq_iSup, Subpresheaf.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Finset.mem_compl, Finset.mem_singleton]
  exact ⟨i', fun _ ↦ Fin.succAbove_ne _ _⟩

lemma simplexδ_succ_succ_castSucc (j : Fin (n + 1)) :
    simplexδ j.succ j.succ.castSucc = simplexδ j.castSucc j.succ.castSucc := by
  apply Prod.ext
  · ext k : 1
    simp [simplexδ, simplex, SimplicialObject.δ, stdSimplex.map_op_apply,
      stdSimplex.objMk₁, SimplexCategory.δ]
    by_cases h₁ : j.succ ≤ k
    · simp only [j.succ.castSucc.succAbove_of_le_castSucc k (by simpa)]
      rw [if_neg (by simpa), if_neg (by simpa using j.castSucc_le_succ.trans h₁)]
    · simp only [not_le] at h₁
      simp only [j.succ.castSucc.succAbove_of_succ_le k (by simpa)]
      rw [if_pos (by simpa using h₁.le), if_pos (by simpa [Fin.le_castSucc_iff])]
  · ext k : 1
    exact SimplexCategory.congr_toOrderHom_apply
      ((SimplexCategory.δ_comp_σ_self (i := j.succ)).trans
      (SimplexCategory.δ_comp_σ_succ (i := j.castSucc)).symm) k

lemma simplexδ_succ_snd (j : Fin (n + 1)) :
    (simplexδ j j.succ).2 = stdSimplex.objMk .id :=
  stdSimplex.objEquiv.injective SimplexCategory.δ_comp_σ_succ

lemma simplexδ_castSucc_snd (j : Fin (n + 1)) :
    (simplexδ j j.castSucc).2 = stdSimplex.objMk .id :=
  stdSimplex.objEquiv.injective SimplexCategory.δ_comp_σ_self

lemma ιSimplex_app_objEquiv_symm_δ (j : Fin (n + 1)) (i : Fin (n + 2)) :
    (ιSimplex.{u} j).app (op ⦋n⦌)
      (stdSimplex.objEquiv.symm (SimplexCategory.δ i)) =
      simplexδ j i := by
  rfl

instance (j : Fin (n + 1)) : Mono (ιSimplex.{u} j) := by
  rw [stdSimplex.mono_iff]
  exact (prodStdSimplex.nonDegenerate_iff' _).1
    (prodStdSimplex.nonDegenerateEquiv₁.{u} j).2

noncomputable def filtration₁ (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd (stdSimplex.face {1}) (boundary n) ⊔
    (⨆ (j : Fin i.1), Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1)

variable (n) in
lemma filtration₁_zero :
    filtration₁.{u} (0 : Fin (n + 2)) =
      Subcomplex.unionProd (stdSimplex.face {1}) (boundary n) := by
  simp [filtration₁]

lemma filtration₁_succ (i : Fin (n + 1)) :
    filtration₁.{u} i.succ = filtration₁ i.castSucc ⊔
      Subcomplex.ofSimplex (simplex i).1 := by
  dsimp [filtration₁]
  apply le_antisymm
  · simp only [Fin.isValue, sup_le_iff, iSup_le_iff]
    refine ⟨le_sup_left.trans le_sup_left, fun ⟨j, hj⟩ ↦ ?_⟩
    obtain hj | rfl := (Nat.le_of_lt_succ hj).lt_or_eq
    · refine le_trans (le_trans ?_ le_sup_right) le_sup_left
      dsimp
      exact le_iSup (fun (j : Fin i.1) ↦
        Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1) ⟨j, hj⟩
    · exact le_sup_right
  · simp only [Fin.isValue, sup_le_iff, le_sup_left, iSup_le_iff, true_and]
    refine ⟨fun ⟨j, hj⟩ ↦ ?_, ?_⟩
    · refine le_trans ?_ le_sup_right
      exact le_iSup (fun (k : Fin (i.1 + 1)) ↦
        Subcomplex.ofSimplex (simplex ⟨k, by omega⟩).1) ⟨j, by omega⟩
    · refine le_trans ?_ le_sup_right
      exact le_iSup (fun (k : Fin (i.1 + 1)) ↦
        Subcomplex.ofSimplex (simplex ⟨k, by omega⟩).1) ⟨i, by omega⟩

lemma monotone_filtration₁ : Monotone (filtration₁.{u} (n := n)) := by
  rw [Fin.monotone_iff]
  rintro i
  rw [filtration₁_succ]
  exact le_sup_left

variable (n) in
lemma filtration₁_last :
    filtration₁.{u} (Fin.last (n + 1)) = ⊤ := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ (add_comm 1 n)]
  intro x hx
  obtain ⟨i, hi⟩ := prodStdSimplex.nonDegenerateEquiv₁.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp [simplex, hi]
  rw [filtration₁, ← Subcomplex.ofSimplex_le_iff]
  exact (le_iSup (fun (j : Fin (Fin.last (n + 1)).1) ↦
    Subcomplex.ofSimplex (simplex ⟨j, by omega⟩).1) i).trans le_sup_right

lemma le_filtration₁_preimage_ιSimplex (j : Fin (n + 1)) :
    horn.{u} (n + 1) j.succ ≤
    (filtration₁ j.castSucc).preimage (ιSimplex j) := by
  rw [horn_eq_iSup]
  simp only [iSup_le_iff, Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro i hij
  simp only [stdSimplex.face_singleton_compl, filtration₁,
    Subcomplex.ofSimplex_le_iff, Subcomplex.preimage_obj, Set.mem_preimage,
    Subpresheaf.max_obj, Set.mem_union, Subpresheaf.iSup_obj, Set.iSup_eq_iUnion,
    Set.mem_iUnion]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp only [Subcomplex.mem_unionProd_iff, stdSimplex.mem_face_iff,
    Finset.mem_singleton]
  dsimp
  by_cases hj₀ : j = 0
  · subst hj₀
    simp only [Fin.succ_zero_eq_one] at hij
    by_cases hi₀ : i = 0
    · subst hi₀
      exact Or.inl (Or.inl (fun i ↦ rfl))
    · refine Or.inl (Or.inr ?_)
      obtain _ | n := n
      · fin_cases i <;> aesop
      obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero hi₀
      apply simplexδ_snd_mem_boundary_of_lt
      rw [Fin.succ_lt_succ_iff]
      by_contra!
      simp at this
      simp [this] at hij
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj₀; clear hj₀
    obtain _ | n := n
    · fin_cases j
    obtain hij | rfl | hij := lt_trichotomy i j.succ.succ
    · rw [← Fin.le_castSucc_iff] at hij
      obtain hij | rfl :=  hij.lt_or_eq
      · exact Or.inl (Or.inr (simplexδ_snd_mem_boundary_of_gt _ _ hij))
      · exact Or.inr ⟨⟨j, by simp⟩,
          by simpa only [simplexδ_succ_succ_castSucc]
            using simplexδ_mem_ofSimplex j.castSucc j.succ.castSucc⟩
    · simp at hij
    · obtain ⟨i, rfl⟩ := Fin.eq_succ_of_ne_zero (i := i) (by rintro rfl; simp at hij)
      refine Or.inl (Or.inr
        (simplexδ_snd_mem_boundary_of_lt _ _ (by simpa using hij)))

lemma Set.not_mem_setOf {α : Type*} (P : α → Prop) (x : α) :
    x ∉ setOf P ↔ ¬ P x := by simp only [Set.nmem_setOf_iff]

lemma filtration₁_preimage_ιSimplex_le (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) ≤
      horn.{u} (n + 1) j.succ := by
  simp only [stdSimplex.subcomplex_le_horn_iff,
    stdSimplex.face_singleton_compl, ← Subcomplex.image_le_iff,
    Subcomplex.image_ofSimplex, Subcomplex.ofSimplex_le_iff]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp [filtration₁, Subcomplex.unionProd, Set.prod, Set.not_mem_setOf]
  refine ⟨⟨?_, ⟨j, ?_⟩⟩, fun i ↦ ?_⟩
  · simpa only [simplexδ_succ_snd] using non_mem_boundary n
  · simp [simplexδ, SimplicialObject.δ, stdSimplex.map_op_apply,
      stdSimplex.objMk₁, SimplexCategory.δ]
  · rw [prodStdSimplex.mem_ofSimplex_iff, Set.not_subset]
    refine ⟨⟨0, j⟩, ⟨j, ?_⟩, ?_⟩
    · ext : 1
      · simp [simplexδ, SimplicialObject.δ, stdSimplex.objMk₁,
          SimplexCategory.δ]
      · simp [simplexδ_succ_snd]
        rfl
    · obtain ⟨i, hi⟩ := i
      rintro ⟨⟨a, ha₀⟩, ha⟩
      simp [simplex, Prod.ext_iff, stdSimplex.objMk₁] at ha
      obtain ⟨ha₁, ha₂⟩ := ha
      change Fin.predAbove _ _ = _ at ha₂
      rw [Fin.predAbove_of_le_castSucc _ _ (by simp; omega), Fin.ext_iff] at ha₂
      dsimp at ha₂
      omega

lemma filtration₁_preimage_ιSimplex (j : Fin (n + 1)) :
    (filtration₁ j.castSucc).preimage (ιSimplex j) =
      horn.{u} (n + 1) j.succ :=
  le_antisymm (filtration₁_preimage_ιSimplex_le j)
    (le_filtration₁_preimage_ιSimplex j)

lemma filtration₁_to_succ_mem (i : Fin (n + 1)) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} i.castSucc_le_succ)) := by
  have := IsPushout.of_isColimit
    (Subcomplex.isColimitPushoutCoconeOfPullback (ιSimplex i) (filtration₁.{u} i.castSucc)
      (filtration₁.{u} i.succ) (horn.{u} (n + 1) i.succ) ⊤
      (by simpa using (filtration₁_preimage_ιSimplex i).symm)
      (by
        simp only [Subcomplex.image_top,
          filtration₁_succ, Subcomplex.ofSimplex_eq_range]))
  exact MorphismProperty.of_isPushout (P := anodyneExtensions) this
    (anodyneExtensions.{u}.comp_mem _ _
      (horn_ι_mem n i.succ) (of_isIso ((Subcomplex.topIso _).inv)))

lemma filtation₁_map_mem {i j : Fin (n + 2)} (h : i ≤ j) :
    anodyneExtensions (Subcomplex.homOfLE (monotone_filtration₁.{u} h)) :=
  anodyneExtensions.map_mem_of_fin
    ((monotone_filtration₁.{u} (n := n)).functor ⋙ Subcomplex.forget _) filtration₁_to_succ_mem
      (homOfLE h)

variable (n) in
lemma mem₁ :
    anodyneExtensions (Subcomplex.unionProd.{u} (stdSimplex.face {(1 : Fin 2)})
      (boundary n)).ι := by
  change anodyneExtensions
    ((Subcomplex.isoOfEq (filtration₁_zero.{u} n)).inv ≫
          (Subcomplex.homOfLE (monotone_filtration₁.{u} (by simp))) ≫
          (Subcomplex.isoOfEq (filtration₁_last.{u} n)).hom ≫
          (Subcomplex.topIso _).hom)
  refine anodyneExtensions.comp_mem _ _ ?_
    (anodyneExtensions.comp_mem _ _ (filtation₁_map_mem (by simp))
    (anodyneExtensions.comp_mem _ _ ?_ ?_))
  all_goals apply of_isIso

noncomputable def filtration₀ (i : Fin (n + 2)) :
    (Δ[1] ⊗ Δ[n] : SSet.{u}).Subcomplex :=
  Subcomplex.unionProd (stdSimplex.face {0}) (boundary n) ⊔
    (⨆ j, ⨆ (_ : i ≤ j.castSucc), Subcomplex.ofSimplex (simplex j).1)

lemma filtration₀_castSucc (i : Fin (n + 1)) :
    filtration₀.{u} i.castSucc = filtration₀ i.succ ⊔
      Subcomplex.ofSimplex (simplex i).1 := by
  dsimp only [filtration₀]
  simp only [Nat.reduceAdd, Fin.isValue, Fin.castSucc_le_castSucc_iff, Fin.succ_le_castSucc_iff]
  apply le_antisymm
  · simp only [sup_le_iff, iSup_le_iff]
    constructor
    · exact le_trans le_sup_left le_sup_left
    · intro j h
      obtain h | rfl := h.lt_or_eq
      · exact le_trans (le_trans (le_trans (by exact le_trans (by rfl) (le_iSup _ h))
          (le_iSup _ j)) le_sup_right) le_sup_left
      · exact le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    constructor
    · constructor
      · exact le_sup_left
      · intro j h
        exact le_trans (le_trans (by exact le_trans (by rfl) (le_iSup _ h.le))
          (le_iSup _ j)) le_sup_right
    · exact le_trans (le_trans (by exact le_trans (by rfl) (le_iSup _ (by simp)))
        (le_iSup _ i)) le_sup_right

lemma antitone_filtration₀ : Antitone (filtration₀.{u} (n := n)) := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  rw [filtration₀_castSucc]
  apply le_sup_left

variable (n) in
lemma filtration₀_last :
    filtration₀.{u} (Fin.last _ : Fin (n + 2)) =
      Subcomplex.unionProd (stdSimplex.face {0}) (boundary n) := by
  simp [filtration₀]
  intro i hi
  simp only [Fin.ext_iff, Fin.coe_castSucc, Fin.val_last] at hi
  omega

variable (n) in
lemma filtration₀_zero :
    filtration₀.{u} (0 : Fin (n + 2)) = ⊤ := by
  rw [prodStdSimplex.subcomplex_eq_top_iff _ (add_comm 1 n)]
  intro x hx
  obtain ⟨i, hi⟩ := prodStdSimplex.nonDegenerateEquiv₁.surjective ⟨x, hx⟩
  obtain rfl : simplex i = x := by simp [simplex, hi]
  rw [filtration₀, ← Subcomplex.ofSimplex_le_iff]
  exact le_trans (le_trans (by
    exact le_trans (by rfl) (le_iSup _ (by simp))) (le_iSup _ i)) le_sup_right

lemma le_filtration₀_preimage_ιSimplex (j : Fin (n + 1)) :
    horn.{u} (n + 1) j.castSucc ≤
    (filtration₀ j.succ).preimage (ιSimplex j) := by
  rw [horn_eq_iSup]
  simp only [iSup_le_iff, Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff]
  intro i hij
  simp only [stdSimplex.face_singleton_compl, filtration₀,
    Subcomplex.ofSimplex_le_iff, Subcomplex.preimage_obj, Set.mem_preimage,
    Subpresheaf.max_obj, Set.mem_union, Set.iSup_eq_iUnion,
    Set.mem_iUnion, Subcomplex.iSup_obj]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp only [Subcomplex.mem_unionProd_iff, stdSimplex.mem_face_iff,
    Finset.mem_singleton]
  obtain ⟨j, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · obtain _ | n := n
    · fin_cases j
    obtain hij | rfl | hij := lt_trichotomy i j.castSucc.castSucc
    · refine Or.inl (Or.inr (simplexδ_snd_mem_boundary_of_gt _ _ hij))
    · simp at hij
    · rw [Fin.castSucc_lt_iff_succ_le] at hij
      obtain hij | rfl := hij.lt_or_eq
      · exact Or.inl (Or.inr (simplexδ_snd_mem_boundary_of_lt _ _ hij))
      · refine Or.inr ⟨j.succ, by simp, ?_⟩
        convert simplexδ_mem_ofSimplex j.succ j.succ.castSucc using 1
        exact (simplexδ_succ_succ_castSucc j).symm
  · obtain ⟨i, rfl⟩ | rfl := i.eq_castSucc_or_eq_last
    · simp only [Fin.castSucc_inj] at hij
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hij
      obtain _ | n := n
      · fin_cases i
      exact Or.inl (Or.inr (simplexδ_snd_mem_boundary_of_gt _ _ (Fin.castSucc_lt_last i)))
    · refine Or.inl (Or.inl (fun i ↦ ?_))
      dsimp [simplexδ, SimplicialObject.δ]
      rw [stdSimplex.map_op_apply, stdSimplex.objMk₁_apply_eq_zero_iff,
        Fin.castSucc_lt_castSucc_iff]
      dsimp
      rw [Fin.lt_last_iff_ne_last]
      apply Fin.succAbove_ne

lemma filtration₀_preimage_ιSimplex_le (j : Fin (n + 1)) :
    (filtration₀ j.succ).preimage (ιSimplex j) ≤
      horn.{u} (n + 1) j.castSucc := by
  simp only [stdSimplex.subcomplex_le_horn_iff,
    stdSimplex.face_singleton_compl, ← Subcomplex.image_le_iff,
    Subcomplex.image_ofSimplex, Subcomplex.ofSimplex_le_iff]
  rw [ιSimplex_app_objEquiv_symm_δ]
  simp [filtration₀, Subcomplex.unionProd, Set.prod, Set.not_mem_setOf]
  refine ⟨⟨?_, ⟨j, ?_⟩⟩, fun i hi ↦ ?_⟩
  · simpa only [simplexδ_castSucc_snd] using non_mem_boundary n
  · simp [simplexδ, SimplicialObject.δ, stdSimplex.map_op_apply,
      stdSimplex.objMk₁, SimplexCategory.δ]
  · rw [prodStdSimplex.mem_ofSimplex_iff, Set.not_subset]
    refine ⟨⟨1, j⟩, ⟨j, ?_⟩, ?_⟩
    · ext : 1
      · simp [simplexδ, SimplicialObject.δ, stdSimplex.objMk₁,
          SimplexCategory.δ]
      · simp [simplexδ_castSucc_snd]
        rfl
    · rintro ⟨⟨a, ha₀⟩, ha⟩
      simp [simplex, Prod.ext_iff, stdSimplex.objMk₁] at ha
      obtain ⟨ha₁, ha₂⟩ := ha
      change Fin.predAbove _ _ = _ at ha₂
      rw [Fin.predAbove_of_succ_le _ _ ha₁] at ha₂
      obtain ⟨a, rfl⟩ := a.exists_eq_succ_of_ne_zero (by
        rintro rfl
        rw [Fin.zero_eta, Fin.le_zero_iff, Fin.ext_iff] at ha₁
        simp at ha₁)
      simp at ha₂
      subst ha₂
      simp only [Fin.lt_iff_val_lt_val] at hi
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Nat.succ_eq_add_one,
        add_le_add_iff_right] at ha₁
      omega

lemma filtration₀_preimage_ιSimplex (j : Fin (n + 1)) :
    (filtration₀ j.succ).preimage (ιSimplex j) =
      horn.{u} (n + 1) j.castSucc :=
  le_antisymm (filtration₀_preimage_ιSimplex_le j)
    (le_filtration₀_preimage_ιSimplex j)

lemma filtration₀_from_succ_mem (i : Fin (n + 1)) :
    anodyneExtensions (Subcomplex.homOfLE (antitone_filtration₀.{u} i.castSucc_le_succ)) := by
  have := IsPushout.of_isColimit
    (Subcomplex.isColimitPushoutCoconeOfPullback (ιSimplex i) (filtration₀.{u} i.succ)
      (filtration₀.{u} i.castSucc) (horn.{u} (n + 1) i.castSucc) ⊤
      (by simpa using (filtration₀_preimage_ιSimplex i).symm) (by
      rw [filtration₀_castSucc, Subcomplex.image_top, Subcomplex.ofSimplex_eq_range]))
      --(by simpa using (filtration₁_preimage_ιSimplex i).symm)
      --(by
      --  simp only [Subcomplex.image_top,
      --    filtration₁_succ, Subcomplex.ofSimplex_eq_range]))
  exact MorphismProperty.of_isPushout (P := anodyneExtensions) this
    (anodyneExtensions.{u}.comp_mem _ _
      (horn_ι_mem n i.castSucc) (of_isIso ((Subcomplex.topIso _).inv)))

lemma filtration₀_map_mem {i j : Fin (n + 2)} (h : i ≤ j) :
    anodyneExtensions (Subcomplex.homOfLE (antitone_filtration₀.{u} h)) := by
  let F : Fin (n + 2) ⥤ SSet.{u}ᵒᵖ :=
    { obj i := op (filtration₀ i : SSet)
      map f := (Subcomplex.homOfLE (antitone_filtration₀ (leOfHom f))).op
      map_id _ := rfl
      map_comp _ _ := by rw [← op_comp, Subcomplex.homOfLE_comp] }
  exact anodyneExtensions.op.map_mem_of_fin F filtration₀_from_succ_mem (homOfLE h)

variable (n) in
lemma mem₀ :
    anodyneExtensions (Subcomplex.unionProd.{u} (stdSimplex.face {(0 : Fin 2)})
      (boundary n)).ι := by
  change anodyneExtensions ((Subcomplex.isoOfEq (filtration₀_last.{u} n)).inv ≫
    (Subcomplex.homOfLE (antitone_filtration₀.{u} (by simp))) ≫
    (Subcomplex.isoOfEq (filtration₀_zero.{u} n)).hom ≫
    (Subcomplex.topIso _).hom)
  refine anodyneExtensions.comp_mem _ _ ?_
    (anodyneExtensions.comp_mem _ _ (filtration₀_map_mem (by simp))
    (anodyneExtensions.comp_mem _ _ ?_ ?_))
  all_goals apply of_isIso

end subcomplex_unionProd_face_ι_mem

open subcomplex_unionProd_face_ι_mem in
lemma subcomplex_unionProd_face_boundary_ι_mem (n : ℕ) (i : Fin 2) :
    anodyneExtensions (Subcomplex.unionProd.{u} (stdSimplex.face {i})
      (boundary n)).ι := by
  fin_cases i
  · exact mem₀ n
  · exact mem₁ n

section

variable {n : ℕ} (k : Fin (n + 1))

open ChosenFiniteProducts

namespace retractArrowHornCastSuccι

lemma preimage_ι_comp_ι₁_eq_top :
    (Λ[n + 1, k.castSucc].unionProd Λ[1, 0]).preimage (Λ[n + 1, k.castSucc].ι ≫ ι₁) = ⊤ := by
  apply le_antisymm (by simp)
  rintro d ⟨x, hx⟩ _
  simp [Subcomplex.mem_unionProd_iff]
  tauto

def ρ : Fin (n + 2) × Fin 2 → Fin (n + 2)
  | ⟨x, 0⟩ => min x k.castSucc
  | ⟨x, 1⟩ => x

lemma ρ_zero_le (x : Fin (n + 2)) : ρ k ⟨x, 0⟩ ≤ k.castSucc := by simp [ρ]

lemma ρ_mem_union (x : Fin (n + 2) × Fin 2) :
    ρ k x ∈ ({x.1} ∪ {k.castSucc} : Set _) := by
  obtain ⟨x₁, x₂⟩ := x
  fin_cases x₂ <;> simp [ρ]; omega

lemma monotone_ρ : Monotone (ρ k) := by
  rw [monotone_prod_iff]
  constructor
  · intro x
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    simp [ρ]
  · intro i
    fin_cases i
    · intro x y h
      simp only [ρ, Fin.coe_eq_castSucc, le_inf_iff, inf_le_iff, inf_le_right, and_true,
        le_refl, or_true]
      tauto
    · intro x y h
      exact h

def r : Δ[n + 1] ⊗ Δ[1] ⟶ Δ[n + 1] :=
  prodStdSimplex.homEquiv.symm ⟨ρ k, monotone_ρ k⟩

lemma range_union_singleton_le
    {d : ℕ} (x : (Δ[n + 1] ⊗ Δ[1] : SSet.{u}) _⦋d⦌) :
    Set.range (stdSimplex.asOrderHom
      ((r k).app (op ⦋d⦌) x)) ∪ {k.castSucc} ⊆
        Set.range (stdSimplex.asOrderHom x.1) ∪ {k.castSucc} := by
  obtain ⟨x₁, x₂⟩ := x
  rintro _ (⟨i, rfl⟩ | _)
  · apply (_ : (_ : Set _) ≤ _) (ρ_mem_union _ ⟨_, _⟩)
    rintro _ (rfl | rfl) <;> aesop
  · aesop

@[reassoc (attr := simp)]
lemma ι₁_r : ι₁ ≫ r k = 𝟙 _ :=
  yonedaEquiv.injective rfl

variable (n) in
@[reassoc (attr := simp)]
lemma ι₀_r_zero : ι₀ ≫ r (0 : Fin (n + 1)) = const (stdSimplex.obj₀Equiv.symm 0) :=
  yonedaEquiv.injective (by
    ext i : 1
    change ρ (0 : Fin (n + 1)) ⟨i, 0⟩ = 0
    simp [ρ])

lemma preimage_ι_comp_r_eq_top :
    Λ[n + 1, k.castSucc].preimage ((Λ[n + 1, k.castSucc].unionProd Λ[1, 0]).ι ≫ r k) = ⊤ := by
  rw [Subcomplex.preimage_ι_comp_eq_top_iff]
  dsimp [Subcomplex.unionProd]
  rw [sup_le_iff]
  constructor
  · rw [← Subcomplex.image_le_iff]
    rintro ⟨d⟩ _ ⟨⟨y₁, y₂⟩, ⟨_, hy₂⟩, rfl⟩
    induction' d using SimplexCategory.rec with d
    replace hy₂ := horn₁.eq_objMk_const _ _ hy₂
    apply face_le_horn (Fin.last _) _ (fun h ↦ by
      simp only [Fin.ext_iff, Fin.val_last, Fin.coe_castSucc] at h
      omega)
    simp only [stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
    intro i
    have : (r k).app _ ⟨y₁, y₂⟩ i ≤ k.castSucc := by subst hy₂; apply ρ_zero_le
    intro h
    simp only [h, Fin.last_le_iff, Fin.ext_iff, Fin.coe_castSucc, Fin.val_last] at this
    omega
  · rw [← Subcomplex.image_le_iff]
    rintro ⟨d⟩ _ ⟨⟨y₁, y₂⟩, ⟨hy₁, _⟩, rfl⟩
    induction' d using SimplexCategory.rec with d
    rw [horn, Set.mem_setOf_eq] at hy₁ ⊢
    intro h
    apply hy₁ (subset_antisymm (by simp) ?_)
    rw [← h]
    apply range_union_singleton_le

end retractArrowHornCastSuccι

open retractArrowHornCastSuccι in
noncomputable def retractArrowHornCastSuccι :
    RetractArrow Λ[n + 1, k.castSucc].ι
      ((Λ[n + 1, k.castSucc].unionProd (horn.{u} 1 0)).ι) where
  i := Arrow.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ ι₁)
    (preimage_ι_comp_ι₁_eq_top k)) ι₁ rfl
  r := Arrow.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ r k)
    (preimage_ι_comp_r_eq_top k)) (r k) rfl
  retract := by
    ext : 1
    · simp [← cancel_mono (Subcomplex.ι _)]
    · simp

namespace retractArrowHornSuccι

lemma preimage_ι_comp_ι₀_eq_top :
    (Λ[n + 1, k.succ].unionProd Λ[1, 1]).preimage (Λ[n + 1, k.succ].ι ≫ ι₀) = ⊤ := by
  apply le_antisymm (by simp)
  rintro d ⟨x, hx⟩ _
  simp [Subcomplex.mem_unionProd_iff]
  tauto

def ρ : Fin (n + 2) × Fin 2 → Fin (n + 2)
  | ⟨x, 0⟩ => x
  | ⟨x, 1⟩ => max x k.succ

lemma le_ρ_one (x : Fin (n + 2)) : k.succ ≤ ρ k ⟨x, 1⟩ := by simp [ρ]

lemma ρ_mem_union (x : Fin (n + 2) × Fin 2) :
    ρ k x ∈ ({x.1} ∪ {k.succ} : Set _) := by
  obtain ⟨x₁, x₂⟩ := x
  fin_cases x₂ <;> simp [ρ]; omega

lemma monotone_ρ : Monotone (ρ k) := by
  rw [monotone_prod_iff]
  constructor
  · intro x
    rw [Fin.monotone_iff_le_succ]
    intro i
    fin_cases i
    simp [ρ]
  · intro i
    fin_cases i
    · intro x y h
      exact h
    · intro x y h
      simp only [ρ, le_sup_iff, sup_le_iff, le_refl, and_true]
      omega

def r : Δ[n + 1] ⊗ Δ[1] ⟶ Δ[n + 1] :=
  prodStdSimplex.homEquiv.symm ⟨ρ k, monotone_ρ k⟩

lemma range_union_singleton_le
    {d : ℕ} (x : (Δ[n + 1] ⊗ Δ[1] : SSet.{u}) _⦋d⦌) :
    Set.range (stdSimplex.asOrderHom
      ((r k).app (op ⦋d⦌) x)) ∪ {k.succ} ⊆
        Set.range (stdSimplex.asOrderHom x.1) ∪ {k.succ} := by
  obtain ⟨x₁, x₂⟩ := x
  rintro _ (⟨i, rfl⟩ | _)
  · apply (_ : (_ : Set _) ≤ _) (ρ_mem_union _ ⟨_, _⟩)
    rintro _ (rfl | rfl) <;> aesop
  · aesop

@[reassoc (attr := simp)]
lemma ι₀_r : ι₀ ≫ r k = 𝟙 _ :=
  yonedaEquiv.injective rfl

lemma preimage_ι_comp_r_eq_top :
    Λ[n + 1, k.succ].preimage ((Λ[n + 1, k.succ].unionProd Λ[1, 1]).ι ≫ r k) = ⊤ := by
  rw [Subcomplex.preimage_ι_comp_eq_top_iff]
  dsimp [Subcomplex.unionProd]
  rw [sup_le_iff]
  constructor
  · rw [← Subcomplex.image_le_iff]
    rintro ⟨d⟩ _ ⟨⟨y₁, y₂⟩, ⟨_, hy₂⟩, rfl⟩
    induction' d using SimplexCategory.rec with d
    replace hy₂ := horn₁.eq_objMk_const _ _ hy₂
    apply face_le_horn 0 _ (fun h ↦ by
      rw [Fin.ext_iff] at h
      simp at h)
    simp only [stdSimplex.mem_face_iff, Finset.mem_compl, Finset.mem_singleton]
    intro i
    have : k.succ ≤ (r k).app _ ⟨y₁, y₂⟩ i := by subst hy₂; apply le_ρ_one
    intro h
    rw [h, Fin.le_zero_iff, Fin.ext_iff] at this
    simp at this
  · rw [← Subcomplex.image_le_iff]
    rintro ⟨d⟩ _ ⟨⟨y₁, y₂⟩, ⟨hy₁, _⟩, rfl⟩
    induction' d using SimplexCategory.rec with d
    rw [horn, Set.mem_setOf_eq] at hy₁ ⊢
    intro h
    apply hy₁ (subset_antisymm (by simp) ?_)
    rw [← h]
    apply range_union_singleton_le

end retractArrowHornSuccι

open retractArrowHornSuccι in
noncomputable def retractArrowHornSuccι :
    RetractArrow Λ[n + 1, k.succ].ι
      ((Λ[n + 1, k.succ].unionProd (horn.{u} 1 1)).ι) where
  i := Arrow.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ ι₀)
    (preimage_ι_comp_ι₀_eq_top k)) ι₀ rfl
  r := Arrow.homMk (Subcomplex.lift (Subcomplex.ι _ ≫ r k)
    (preimage_ι_comp_r_eq_top k)) (r k) rfl
  retract := by
    ext : 1
    · simp [← cancel_mono (Subcomplex.ι _)]
    · simp

end

end anodyneExtensions

lemma modelCategoryQuillen.J_le_hornOneUnionProdInclusions :
    modelCategoryQuillen.J.{u} ≤ hornOneUnionProdInclusions.retracts := by
  rintro _ _ _ h
  simp only [J, MorphismProperty.iSup_iff] at h
  obtain ⟨n, ⟨k⟩⟩ := h
  obtain ⟨k, rfl⟩ | rfl := k.eq_castSucc_or_eq_last
  · exact ⟨_, _, _, anodyneExtensions.retractArrowHornCastSuccι k,
      mem_hornOneUnionProdInclusions _ _⟩
  · exact ⟨_, _, _, anodyneExtensions.retractArrowHornSuccι (Fin.last _),
      mem_hornOneUnionProdInclusions _ _⟩

end SSet
