module

public import TopCatModelCategory.SSet.NonDegenerateProdSimplex
public import TopCatModelCategory.SSet.Monoidal

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory

lemma Fin.range₁ {α : Type*} (f : Fin 1 → α) :
    Set.range f = {f 0} := Set.range_unique

lemma Fin.range_eq_insert {α : Type*} (f : Fin (n + 1) → α) :
    Set.range f =
      Insert.insert (f 0) (Set.range (fun (i : Fin n) ↦ f i.succ)) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, rfl⟩
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ <;> aesop
  · aesop

lemma Fin.range₂ {α : Type*} (f : Fin 2 → α) :
    Set.range f = {f 0, f 1} := by
  simp [Fin.range_eq_insert]

lemma Fin.range₃ {α : Type*} (f : Fin 3 → α) :
    Set.range f = {f 0, f 1, f 2} := by
  simp [Fin.range_eq_insert]

namespace SSet

namespace square

open CartesianMonoidalCategory

noncomputable def ιTriangle₀ : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  yonedaEquiv.symm (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 0).1

noncomputable def ιTriangle₁ : (Δ[2] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  yonedaEquiv.symm (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 1).1

noncomputable def diagonal : Δ[1] ⟶ Δ[1] ⊗ Δ[1] := lift (𝟙 _) (𝟙 _)

@[reassoc (attr := simp)]
lemma diagonal_fst : diagonal.{u} ≫ fst _ _ = 𝟙 _ := by simp [diagonal]

@[reassoc (attr := simp)]
lemma diagonal_snd : diagonal.{u} ≫ snd _ _ = 𝟙 _ := by simp [diagonal]

@[reassoc (attr := simp)]
lemma δ₀_diagonal :
    stdSimplex.δ 0 ≫ diagonal =
      const (prodStdSimplex.obj₀Equiv.symm ⟨1, 1⟩) := by
  apply yonedaEquiv.injective
  apply Prod.ext <;> exact stdSimplex.obj₀Equiv.injective (by rfl)

@[reassoc (attr := simp)]
lemma δ₁_diagonal :
    stdSimplex.δ 1 ≫ diagonal =
      const (prodStdSimplex.obj₀Equiv.symm ⟨0, 0⟩) := by
  apply yonedaEquiv.injective
  apply Prod.ext <;> exact stdSimplex.obj₀Equiv.injective (by rfl)

@[reassoc (attr := simp)]
lemma δ₀_ιTriangle₀ :
    stdSimplex.δ 0 ≫ square.ιTriangle₀ = ι₁ ≫ (β_ _ _).hom := by
  dsimp [ιTriangle₀]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₁_ιTriangle₀ :
    stdSimplex.δ 1 ≫ square.ιTriangle₀ = diagonal := by
  dsimp [ιTriangle₀]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₂_ιTriangle₀ : stdSimplex.δ 2 ≫ square.ιTriangle₀ = ι₀ := by
  dsimp [ιTriangle₀]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₀_ιTriangle₁ : stdSimplex.δ 0 ≫ square.ιTriangle₁ = ι₁ := by
  dsimp [ιTriangle₁]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₁_ιTriangle₁ :
    stdSimplex.δ 1 ≫ square.ιTriangle₁ = diagonal := by
  dsimp [ιTriangle₁]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc (attr := simp)]
lemma δ₂_ιTriangle₁ :
    stdSimplex.δ 2 ≫ square.ιTriangle₁ = ι₀ ≫ (β_ _ _).hom := by
  dsimp [ιTriangle₁]
  rw [stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  apply prodStdSimplex.objEquiv.injective
  rw [Equiv.apply_symm_apply]
  ext x : 3 <;> fin_cases x <;> rfl

@[reassoc]
lemma δ₁_whiskerRight :
    stdSimplex.{u}.δ (1 : Fin 2) ▷ Δ[1] =
      snd _ _ ≫ stdSimplex.δ 2 ≫ ιTriangle₁ := by
  rw [← cancel_epi (stdSimplex.leftUnitor _).inv]
  apply yonedaEquiv.injective
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

@[reassoc]
lemma δ₀_whiskerRight :
    stdSimplex.{u}.δ (0 : Fin 2) ▷ Δ[1] =
      snd _ _ ≫ stdSimplex.δ 0 ≫ ιTriangle₀ := by
  rw [← cancel_epi (stdSimplex.leftUnitor _).inv]
  apply yonedaEquiv.injective
  apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

noncomputable abbrev diagonalSimplex : (Δ[1] ⊗ Δ[1] : SSet.{u}).nonDegenerate 1 :=
  ⟨yonedaEquiv diagonal, by
    rw [prodStdSimplex.nonDegenerate_iff']
    intro x y h
    simpa using congr_arg Prod.fst h⟩

lemma range_objEquiv_nonDegenerateEquiv₁_zero :
    Set.range (prodStdSimplex.objEquiv
      (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 0).1) =
        {(0,0), (1, 0), (1, 1)} :=
  Fin.range₃ _

lemma range_objEquiv_nonDegenerateEquiv₁_one :
    Set.range (prodStdSimplex.objEquiv
      (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 1).1) =
        {(0,0), (0, 1), (1, 1)} :=
  Fin.range₃ _

lemma range_objEquiv_diagonalSimplex :
    Set.range (prodStdSimplex.objEquiv diagonalSimplex.1) = {(0, 0), (1, 1)} := by
  rw [Fin.range₂]
  rfl

lemma range_objEquiv_diagonalSimplex_eq_inter :
    Set.range (prodStdSimplex.objEquiv diagonalSimplex.1) =
    Set.range (prodStdSimplex.objEquiv
      (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 0).1) ∩
    Set.range (prodStdSimplex.objEquiv
      (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 1).1) := by
  rw [range_objEquiv_nonDegenerateEquiv₁_zero,
    range_objEquiv_nonDegenerateEquiv₁_one,
    range_objEquiv_diagonalSimplex]
  ext x
  fin_cases x <;> simp

open Subcomplex

lemma sq : Sq (ofSimplex.{u} (yonedaEquiv diagonal))
    (ofSimplex (prodStdSimplex.nonDegenerateEquiv₁ 0).1)
    (ofSimplex (prodStdSimplex.nonDegenerateEquiv₁ 1).1)
    (⊤ : (Δ[1] ⊗ Δ[1]).Subcomplex) where
  max_eq := by
    rw [prodStdSimplex.subcomplex_eq_top_iff _ rfl]
    intro x hx
    obtain ⟨i, hi⟩ := prodStdSimplex.nonDegenerateEquiv₁.surjective ⟨x, hx⟩
    rw [Subtype.ext_iff] at hi
    dsimp at hi
    subst hi
    rw [Subpresheaf.max_obj, Set.mem_union]
    fin_cases i
    · exact Or.inl (mem_ofSimplex_obj _)
    · exact Or.inr (mem_ofSimplex_obj _)
  min_eq := by
    ext ⟨k⟩ x
    induction k using SimplexCategory.rec with | _ k
    obtain ⟨x, rfl⟩ := prodStdSimplex.objEquiv.symm.surjective x
    dsimp
    simp only [Set.mem_inter_iff, prodStdSimplex.mem_ofSimplex_iff,
      Equiv.apply_symm_apply]
    rw [range_objEquiv_diagonalSimplex_eq_inter, Set.subset_inter_iff]

lemma isPushout :
    IsPushout (stdSimplex.{u}.δ 1)
      (stdSimplex.δ 1) square.ιTriangle₀
      square.ιTriangle₁ := by
  fapply sq.{u}.isPushout.of_iso'
    (prodStdSimplex.isoOfNonDegenerate.{u} diagonalSimplex)
    (prodStdSimplex.isoOfNonDegenerate.{u}
        (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 0))
    (prodStdSimplex.isoOfNonDegenerate.{u}
        (prodStdSimplex.nonDegenerateEquiv₁ (q := 1) 1))
    (topIso (Δ[1] ⊗ Δ[1])).symm
  all_goals try apply Subcomplex.hom_ext _ rfl
  all_goals
    apply Subcomplex.hom_ext
    dsimp
    rw [Category.assoc, Category.assoc, homOfLE_ι,
      prodStdSimplex.isoOfNonDegenerate_hom_ι,
      prodStdSimplex.isoOfNonDegenerate_hom_ι,
      ← yonedaEquiv_symm_δ]
    congr 1
    apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

end square

end SSet
