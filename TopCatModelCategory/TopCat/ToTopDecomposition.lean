import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.TopCat.CosimpInterior
import TopCatModelCategory.TopCat.CosimpIso
import TopCatModelCategory.TopCat.RelativeT1CellComplex
import TopCatModelCategory.CellComplex

open Simplicial CategoryTheory HomotopicalAlgebra Limits

namespace stdSimplex

def interior (X : Type*) [Fintype X]: Set (stdSimplex ℝ X) :=
  setOf (fun x ↦ ∀ i, 0 < x i)

def toTopMap_mem_interior {n m : SimplexCategory} (f : n ⟶ m) [hf : Epi f]
    (x : stdSimplex ℝ (Fin (n.len + 1)))
    (hx : x ∈ interior (Fin (n.len + 1)))  :
    stdSimplex.map f x ∈ interior _ := by
  rw [SimplexCategory.epi_iff_surjective] at hf
  intro i
  obtain ⟨j, hj⟩ := hf i
  exact lt_of_lt_of_le (hx j) (by
    simp [FunOnFinite.linearMap_apply_apply]
    apply Finset.single_le_sum (a := j)
    · simp
    · simpa)

lemma range_toTop_map_face_singleton_compl {n : ℕ} (i : Fin (n + 2)) :
    Set.range (SSet.toTop.{u}.map (SSet.stdSimplex.face {i}ᶜ).ι) =
      Set.range (SSet.toTop.map (SSet.stdSimplex.δ i)) := by
  rw [← SSet.stdSimplex.faceSingletonComplIso_hom_ι, Functor.map_comp]
  dsimp
  ext x
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := ((SSet.toTop ⋙ forget _).mapIso
      (SSet.stdSimplex.faceSingletonComplIso i)).toEquiv.surjective x
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩

open SimplexCategory NNReal in
lemma toTopHomeo_apply_eq_zero_iff {n : ℕ} (x : (|Δ[n]| : Type u)) (i : Fin (n + 1)) :
    (⦋n⦌.toTopHomeo x) i = 0 ↔
      x ∈ Set.range (ConcreteCategory.hom (SSet.toTop.map (SSet.stdSimplex.face {i}ᶜ).ι)) := by
  obtain _ | n := n
  · refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · fin_cases i
      simp at hx
    · have : SSet.stdSimplex.face.{u} {i}ᶜ = ⊥ := by
        fin_cases i
        ext ⟨n⟩ x
        induction n using SimplexCategory.rec with | _ n
        rw [SSet.stdSimplex.mem_face_iff]
        simpa using ⟨0, by subsingleton⟩
      rw [this] at hx
      simp at hx
  · rw [range_toTop_map_face_singleton_compl]
    obtain ⟨x, rfl⟩ := ⦋n + 1⦌.toTopHomeo.symm.surjective x
    simp only [Homeomorph.apply_symm_apply, Set.mem_range]
    sorry
    /-trans ∃ (y : ⦋n⦌.toTopObj), toTopMap (δ i) y = x
    · constructor
      · intro hx
        let y (j : Fin (n + 1)) : ℝ≥0 := x (Fin.succAbove i j)
        refine ⟨⟨y, ?_⟩, ?_⟩
        · simp [toTopObj, y]
          trans ∑ (j ∈ {i}ᶜ), x j
          · exact Finset.sum_of_injOn i.succAbove (by simp) (by simp)
              (by simp; tauto) (by simp)
          · have := x.2
            simp only [toTopObj, Set.mem_setOf_eq] at this
            rw [← this]
            convert Finset.sum_compl_add_sum (s := {i}) (f := x)
            simpa
        · ext j : 2
          dsimp [ToType] at j ⊢
          by_cases hj : j < i
          · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
            dsimp [y]
            rw [Finset.sum_eq_single (a := j), Fin.succAbove_of_castSucc_lt i j hj]
            · simp
              intro b hb hb'
              exact (hb' (Fin.succAbove_right_injective
                (hb.trans (Fin.succAbove_of_castSucc_lt i j hj).symm))).elim
            · simp
              intro h
              change Fin.succAbove _ _ ≠ _ at h
              rw [Fin.succAbove_of_castSucc_lt _ _ hj] at h
              tauto
          · simp only [not_lt] at hj
            obtain hj | hj := hj.lt_or_eq
            · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hj)
              simp [y]
              rw [Finset.sum_eq_single (a := j), Fin.succAbove_of_lt_succ _ _ hj]
              · simp
                intro b hb hb'
                exact (hb' (Fin.succAbove_right_injective
                  (hb.trans (Fin.succAbove_of_lt_succ i j hj).symm))).elim
              · simp
                intro h
                change Fin.succAbove _ _ ≠ _ at h
                rw [Fin.succAbove_of_lt_succ _ _ hj] at h
                tauto
            · subst hj
              simp [y]
              rw [hx, Finset.sum_eq_zero]
              simp
              intro x hx
              exact (Fin.succAbove_ne _ _ hx).elim
      · rintro ⟨x, rfl⟩
        simp only [toTopMap, len_mk, Finset.sum_eq_zero_iff, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rintro j hj
        exact (Fin.succAbove_ne _ _ hj).elim
    · constructor
      · rintro ⟨y, rfl⟩
        exact ⟨⦋n⦌.toTopHomeo.symm y,
          (toTopHomeo_symm_naturality_apply _ _).symm⟩
      · rintro ⟨y, hy⟩
        obtain ⟨y, rfl⟩ := ⦋n⦌.toTopHomeo.symm.surjective y
        refine ⟨y, ?_⟩
        apply ⦋n + 1⦌.toTopHomeo.symm.injective
        rw [← hy]
        exact toTopHomeo_symm_naturality_apply _ _-/

lemma toTopHomeo_mem_interior_iff {n : ℕ} (x : |Δ[n]|) :
    ⦋n⦌.toTopHomeo x ∈ interior _ ↔ x ∈ (Set.range (SSet.toTop.map ∂Δ[n].ι))ᶜ := by
  dsimp [interior]
  rw [← not_iff_not]
  sorry
  --simp only [Set.mem_compl_iff, not_not, not_forall, not_lt, nonpos_iff_eq_zero]
  --rw [SSet.boundary_eq_iSup]
  --simp only [SSet.Subcomplex.range_toTop_map_iSup_ι, Set.mem_iUnion, toTopHomeo_apply_eq_zero_iff ]
  --rfl

open TopCat in
lemma toTopMap_apply_injective_of_epi_of_mem_interior
    {n m : SimplexCategory} {f g : n ⟶ m} [Epi f] [Epi g]
    {x : stdSimplex ℝ (Fin (n.len + 1))} (h : stdSimplex.map f x = stdSimplex.map g x)
    (hx : x ∈ interior _) :
    f = g := by
  /-refine cosimp.injective_map_interior_of_epi unitInterval f g
    ((cosimp.toTopIso.app _).hom x) (Fin.strictMono_iff_lt_succ.2 (by
      intro i
      rw [Subtype.mk_lt_mk]
      dsimp [cosimp.toTopIso, cosimp.objUnitIntervalHomeomorph]
      simp only [cosimp.objOfToTopObj_succ, NNReal.val_eq_coe,
        lt_add_iff_pos_right, NNReal.coe_pos]
      apply hx i)) ?_
  have h₁ := ConcreteCategory.congr_hom (cosimp.toTopIso.hom.naturality f) x
  have h₂ := congr_arg (cosimp.toTopIso.hom.app m) h
  have h₃ := ConcreteCategory.congr_hom (cosimp.toTopIso.hom.naturality g) x
  exact h₁.symm.trans (h₂.trans h₃)-/
  sorry

end stdSimplex

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y)

noncomputable def toTopObjToTop {n : ℕ} (x : X _⦋n⦌)
    (p : _root_.stdSimplex ℝ (Fin (n + 1))) : |X| :=
  toTop.map (yonedaEquiv.symm x) (⦋n⦌.toTopHomeo.symm p)

lemma toTopObjToTop_naturality {n : ℕ} (x : X _⦋n⦌) (p : _root_.stdSimplex ℝ (Fin (n + 1))) :
    toTop.map f (toTopObjToTop x p) = toTopObjToTop (f.app _ x) p := by
  dsimp [toTopObjToTop]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, yonedaEquiv_symm_comp]

lemma toTopObjToTop_naturality' {n m : ℕ} (x : X _⦋n⦌) (p : _root_.stdSimplex ℝ (Fin (m + 1)))
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    toTopObjToTop x (_root_.stdSimplex.map f p) = toTopObjToTop (X.map f.op x) p := by
  dsimp only [toTopObjToTop]
  obtain ⟨p, rfl⟩ := (SimplexCategory.toTopHomeo ⦋m⦌).surjective p
  have := congr_fun (SimplexCategory.toTopHomeo_naturality f) p
  dsimp at this ⊢
  rw [Homeomorph.symm_apply_apply, ← this, Homeomorph.symm_apply_apply,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    stdSimplex.map_comp_yonedaEquiv_symm]

noncomputable def sigmaToTop : (Σ (s : X.N), stdSimplex.interior (Fin (s.dim + 1))) → |X| :=
  fun ⟨s, p⟩ ↦ toTopObjToTop s.simplex p

open RelativeCellComplex in
lemma sigmaToTop_bijective : Function.Bijective X.sigmaToTop := by
  let hX := X.relativeCellComplex.map (SSet.toTop)
  let e₁ : (Σ (s : X.N), (stdSimplex.interior (Fin (s.dim + 1)))) ≃
    (Σ (c : hX.Cells), ((Set.range (ConcreteCategory.hom
      (toTop.{u}.map ∂Δ[c.j].ι)))ᶜ : Set _)) :=
    { toFun := fun ⟨s, x, hx⟩ ↦
        ⟨(mapCellsEquiv _ _).symm
          ((relativeCellComplexCellsEquiv X).symm s), ⟨⦋s.dim⦌.toTopHomeo.symm x, by
            obtain ⟨y, rfl⟩ := (SimplexCategory.toTopHomeo.{u} ⦋s.dim⦌).surjective x
            erw [stdSimplex.toTopHomeo_mem_interior_iff] at hx
            rwa [Homeomorph.symm_apply_apply]⟩⟩
      invFun := fun ⟨s, y, hy⟩ ↦
        ⟨relativeCellComplexCellsEquiv X (mapCellsEquiv _ _ s), ⟨⦋s.j⦌.toTopHomeo y, by
            dsimp
            sorry
            --rwa [stdSimplex.toTopHomeo_mem_interior_iff]
            ⟩⟩
      left_inv := by
        rintro ⟨s, x, hx⟩
        sorry
        --aesop
      right_inv := by
        rintro ⟨s, y, hy⟩
        aesop }
  let e₂ := TopCat.RelativeT₁CellComplex.sigmaEquiv hX
    (fun _ _ ↦ boundary.t₁Inclusions_toTop_map_ι _)
  let e : (Σ (s : X.N), stdSimplex.interior (Fin (s.dim + 1))) ≃ |X| :=
    (e₁.trans e₂).trans (Equiv.subtypeUnivEquiv (by simp))
  convert e.bijective
  ext ⟨s, x, hx⟩
  dsimp [e, e₁, e₂, mapCellsEquiv, relativeCellComplexCellsEquiv, sigmaToTop, Cells.ι,
    relativeCellComplex]
  dsimp [hX, map, AttachCells.map, AttachCells.cell, toTopObjToTop]
  rw [← TopCat.comp_app, ← TopCat.comp_app, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 3
  exact (X.relativeCellComplexι_eq ((relativeCellComplexCellsEquiv X).symm s)).symm

lemma sigmaToTop_naturality (s : X.N) (p : stdSimplex.interior (Fin (s.dim + 1)))
    (t : Y.N) (g : ⦋s.dim⦌ ⟶ ⦋t.dim⦌) [Epi g] (hg : f.app _ s.simplex = Y.map g.op t.simplex) :
    toTop.map f (sigmaToTop ⟨s, p⟩) =
      sigmaToTop ⟨t, ⟨stdSimplex.map g p.1,
      stdSimplex.toTopMap_mem_interior g p.1 p.2⟩⟩ := by
  dsimp [sigmaToTop]
  obtain ⟨p, _⟩ := p
  dsimp
  sorry
  --rw [toTopObjToTop_naturality, hg, toTopObjToTop_naturality']

@[simps! apply]
noncomputable def sigmaEquivToTop : (Σ (s : X.N), stdSimplex.interior (Fin (s.dim + 1))) ≃ |X| :=
  Equiv.ofBijective _ sigmaToTop_bijective

@[simp]
lemma sigmaEquivToTop_symm_apply (x : (Σ (s : X.N), stdSimplex.interior (Fin (s.dim + 1)))) :
    sigmaEquivToTop.symm (X.sigmaToTop x) = x :=
  sigmaEquivToTop.symm_apply_apply x

lemma sigmaToTop_mem_interiorCell (x : (Σ (s : X.N), stdSimplex.interior (Fin (s.dim +1)))) :
    sigmaToTop x ∈ TopCat.RelativeT₁CellComplex.interiorCell
    ((X.relativeCellComplex.mapCellsEquiv toTop).symm
      (X.relativeCellComplexCellsEquiv.symm x.1)) := by
  obtain ⟨s, x⟩ := x
  refine ⟨⦋s.dim⦌.toTopHomeo.symm x.1, ?_, by aesop⟩
  · dsimp
    simp only [← stdSimplex.toTopHomeo_mem_interior_iff]
    erw [Homeomorph.apply_symm_apply]
    exact x.2

end SSet
