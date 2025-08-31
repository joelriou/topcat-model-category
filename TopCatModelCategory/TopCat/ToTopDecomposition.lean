import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.CosimpInterior
import TopCatModelCategory.TopCat.CosimpIso

open Simplicial CategoryTheory

namespace stdSimplex

def interior (n : SimplexCategory) : Set (n.toTopObj) :=
  setOf (fun x ↦ ∀ i, 0 < x i)

def toTopMap_mem_interior {n m : SimplexCategory} (x : n.toTopObj)
    (hx : x ∈ interior n) (f : n ⟶ m) [hf : Epi f] :
      SimplexCategory.toTopMap f x ∈ interior m := by
  rw [SimplexCategory.epi_iff_surjective] at hf
  intro i
  obtain ⟨j, hj⟩ := hf i
  dsimp
  exact lt_of_lt_of_le (hx j) (Finset.single_le_sum (a := j) (by simp) (by simpa))

open TopCat in
lemma toTopMap_apply_injective_of_epi_of_mem_interior
    {n m : SimplexCategory} {f g : n ⟶ m} [Epi f] [Epi g]
    {x : n.toTopObj} (h : SimplexCategory.toTopMap f x = SimplexCategory.toTopMap g x)
    (hx : x ∈ interior n) :
    f = g := by
  refine cosimp.injective_map_interior_of_epi unitInterval f g
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
  exact h₁.symm.trans (h₂.trans h₃)

end stdSimplex

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y)

noncomputable def toTopObjToTop {n : ℕ} (x : X _⦋n⦌) (p : ⦋n⦌.toTopObj) : |X| :=
  toTop.map (yonedaEquiv.symm x) (⦋n⦌.toTopHomeo.symm p)

lemma toTopObjToTop_naturality {n : ℕ} (x : X _⦋n⦌) (p : ⦋n⦌.toTopObj) :
    toTop.map f (toTopObjToTop x p) = toTopObjToTop (f.app _ x) p := by
  dsimp [toTopObjToTop]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, yonedaEquiv_symm_comp]

lemma toTopObjToTop_naturality' {n m : ℕ} (x : X _⦋n⦌) (p : ⦋m⦌.toTopObj)
    (f : ⦋m⦌ ⟶ ⦋n⦌) :
    toTopObjToTop x (SimplexCategory.toTopMap f p) = toTopObjToTop (X.map f.op x) p := by
  dsimp only [toTopObjToTop]
  obtain ⟨p, rfl⟩ := (SimplexCategory.toTopHomeo _).surjective p
  have := congr_fun (SimplexCategory.toTopHomeo_naturality f) p
  dsimp at this ⊢
  rw [Homeomorph.symm_apply_apply, ← this, Homeomorph.symm_apply_apply,
    ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    stdSimplex.map_comp_yonedaEquiv_symm]

noncomputable def sigmaToTop : (Σ (s : X.N), stdSimplex.interior ⦋s.dim⦌) → |X| :=
  fun ⟨s, p⟩ ↦ toTopObjToTop s.simplex p

lemma sigmaToTop_bijective : Function.Bijective X.sigmaToTop := sorry

lemma sigmaToTop_naturality (s : X.N) (p : stdSimplex.interior ⦋s.dim⦌)
    (t : Y.N) (g : ⦋s.dim⦌ ⟶ ⦋t.dim⦌) [Epi g] (hg : f.app _ s.simplex = Y.map g.op t.simplex) :
    toTop.map f (sigmaToTop ⟨s, p⟩) =
      sigmaToTop ⟨t, ⟨SimplexCategory.toTopMap g p,
        stdSimplex.toTopMap_mem_interior p.1 p.2 g⟩⟩ := by
  dsimp [sigmaToTop]
  obtain ⟨p, _⟩ := p
  dsimp
  rw [toTopObjToTop_naturality, hg, toTopObjToTop_naturality']

@[simps! apply]
noncomputable def sigmaEquivToTop : (Σ (s : X.N), stdSimplex.interior ⦋s.dim⦌) ≃ |X| :=
  Equiv.ofBijective _ sigmaToTop_bijective

end SSet
