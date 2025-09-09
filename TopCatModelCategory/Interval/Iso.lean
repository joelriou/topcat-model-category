import TopCatModelCategory.Interval.Cosimplicial
import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.Elements
import Mathlib.Data.NNReal.Basic

namespace CategoryTheory

namespace Interval

variable {n : SimplexCategory} (s : SimplexCategory.toTopObj n)

def objOfToTopObj (i : Fin (n.len + 2)) : ℝ :=
  (Finset.univ.filter (fun (j : Fin _) ↦ j.castSucc < i)).sum (fun j ↦ s.1 j)

@[simp]
lemma objOfToTopObj_zero : objOfToTopObj s 0 = 0 := by simp [objOfToTopObj]

@[simp]
lemma objOfToTopObj_last : objOfToTopObj s (Fin.last _) = 1 := by
  obtain ⟨s, hs⟩ := s
  simp only [SimplexCategory.toTopObj, Set.mem_setOf_eq] at hs
  rw [Subtype.ext_iff] at hs
  simp only [NNReal.val_eq_coe, NNReal.coe_sum, NNReal.coe_one] at hs
  rw [← hs, objOfToTopObj]
  aesop

@[simp]
lemma objOfToTopObj_succ (i : Fin (n.len + 1)) :
    objOfToTopObj s i.succ = objOfToTopObj s i.castSucc + (s.1 i).1 := by
  simp only [objOfToTopObj, Fin.castSucc_lt_succ_iff,
    Fin.castSucc_lt_castSucc_iff, NNReal.val_eq_coe]
  rw [Finset.sum_eq_add_sum_diff_singleton (i := i) (by simp), add_comm]
  congr
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  omega

lemma monotone_objOfToTopObj : Monotone (objOfToTopObj s) := by
  simp [Fin.monotone_iff]

lemma objOfToTopObj_mem_unitInterval (i : Fin (n.len + 2)) :
    objOfToTopObj s i ∈ unitInterval := by
  simp only [Set.mem_Icc]
  constructor
  · rw [← objOfToTopObj_zero s]
    exact monotone_objOfToTopObj _ (Fin.zero_le _)
  · rw [← objOfToTopObj_last s]
    exact monotone_objOfToTopObj _ (Fin.le_last _)

def toTopObjToIntervalHom {n : SimplexCategory} (s : n.toTopObj) :
    IntervalHom (Fin (n.len + 2)) unitInterval where
  orderHom := ⟨fun i ↦ ⟨_, objOfToTopObj_mem_unitInterval s i⟩, monotone_objOfToTopObj s⟩
  map_bot' := by ext; apply objOfToTopObj_zero
  map_top' := by ext; apply objOfToTopObj_last

@[simp]
lemma toTopObjToIntervalHom_apply {n : SimplexCategory} (s : n.toTopObj)
    (i : Fin (n.len + 2)) :
    (toTopObjToIntervalHom s i).1 = objOfToTopObj s i := rfl

lemma toTopObjToIntervalHom_bijective (n : SimplexCategory) :
    Function.Bijective (toTopObjToIntervalHom (n := n)) := by
  constructor
  · intro s t h
    simp [IntervalHom.ext_iff', Subtype.ext_iff] at h
    ext i
    simpa only [← h, objOfToTopObj_succ s i, add_right_inj] using objOfToTopObj_succ t i
  · intro f
    let s (i : Fin (n.len + 1)) : ℝ := (f i.succ).1 - (f i.castSucc).1
    have hs₀ (i) : 0 ≤ s i := sub_nonneg_of_le (f.1.monotone i.castSucc_le_succ)
    have hs₁ (i : Fin (n.len + 2)) :
        (Finset.univ.filter (fun (j : Fin _) ↦ j.castSucc < i)).sum (fun j ↦ s j) = f i := by
      induction i using Fin.induction with
      | zero => simp [show f 0 = 0 from f.map_bot']
      | succ l hi =>
        rw [Finset.sum_eq_add_sum_diff_singleton (i := l) (by simp), ← eq_sub_iff_add_eq']
        convert hi using 2
        · ext j
          simp only [Fin.castSucc_lt_succ_iff, Finset.mem_sdiff, Finset.mem_filter,
            Finset.mem_univ, true_and, Finset.mem_singleton, Fin.castSucc_lt_castSucc_iff]
          omega
        · simp [s]
    refine ⟨⟨(fun i ↦ ⟨s i, hs₀ i⟩), ?_⟩, by ext; apply hs₁⟩
    have := hs₁ (Fin.last _)
    simp only [show f (Fin.last _) = ⊤ from f.map_top'] at this
    simp only [SimplexCategory.toTopObj, Set.mem_setOf_eq]
    rw [Subtype.ext_iff]
    simp only [NNReal.val_eq_coe, NNReal.coe_sum, NNReal.coe_mk, Finset.sum_sub_distrib,
      NNReal.coe_one, s]
    convert this using 1
    aesop

noncomputable def toTopObjEquiv {n : SimplexCategory} :
    n.toTopObj ≃ IntervalHom (Fin (n.len + 2)) unitInterval :=
  Equiv.ofBijective _ (toTopObjToIntervalHom_bijective n)

@[simp]
lemma toTopObjEquiv_apply {n : SimplexCategory} (s : n.toTopObj) (i : Fin (n.len + 2)) :
    (toTopObjEquiv s i).1 = objOfToTopObj s i := rfl

@[simp]
lemma toTopObjEquiv_naturality {n m : SimplexCategory} (f : n ⟶ m)
    (x : n.toTopObj) :
    toTopObjEquiv (SimplexCategory.toTopMap f x) =
      (toTopObjEquiv x).comp f.toIntervalHom := by
  ext i
  dsimp [toTopObjEquiv, toTopObjToIntervalHom, objOfToTopObj]
  simp only [NNReal.coe_sum]
  rw [← Finset.sum_disjiUnion]; swap
  · intro a ha b hb h i hia hib x hx
    have h₁ := hia hx
    have h₂ := hib hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact (h (by rw [← h₁, h₂])).elim
  congr
  ext j
  simp
  exact (SimplexCategory.II.castSucc_lt_map_apply f i j).symm

noncomputable def isoToTop₀CompForget :
    SimplexCategory.toTop₀ ⋙ forget _ ≅ toCosimplicialObject (.of unitInterval) :=
  NatIso.ofComponents (fun n ↦
    Equiv.toIso (toTopObjEquiv.trans
      (toCosimplicialObjectObjEquiv (X := .of unitInterval)).symm)) (fun {n m} f ↦ by
      ext
      exact toCosimplicialObjectObjEquiv.injective (toTopObjEquiv_naturality _ _))

open Functor in
noncomputable def isoToTopCompForget :
    SimplexCategory.toTop.{u} ⋙ forget _ ≅ toCosimplicialObject (.of (ULift.{u} unitInterval)) :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (Iso.refl _) ≪≫ (associator _ _ _).symm ≪≫
    (isoWhiskerRight isoToTop₀CompForget (CategoryTheory.uliftFunctor.{u, 0})) ≪≫
      (toCosimplicialObjectUliftFunctorObj.{u, 0} (.of unitInterval)).symm

instance : IsCofiltered (SimplexCategory.toTop₀ ⋙ forget _).Elements :=
  IsCofiltered.of_equivalence (Elements.equivalenceOfIso isoToTop₀CompForget.symm)

instance : IsCofiltered (SimplexCategory.toTop.{u} ⋙ forget _).Elements :=
  IsCofiltered.of_equivalence (Elements.equivalenceOfIso isoToTopCompForget.symm)

end Interval

end CategoryTheory
