import TopCatModelCategory.SSet.PiZero
import TopCatModelCategory.TopCat.Adj

universe u

open Simplicial CategoryTheory Limits Opposite NNReal

@[simp]
lemma NNReal.sum_coe {α : Type*} [Fintype α] (f : α → ℝ≥0) :
    (Finset.univ.sum f).1 = Finset.univ.sum (fun i ↦ (f i).1) := by
  let coeℝ : ℝ≥0 →+ ℝ := AddMonoidHom.mk' (fun (x : ℝ≥0) ↦ x.1) (by aesop)
  apply map_sum coeℝ

namespace SSet

instance (n : SimplexCategory) : PathConnectedSpace (SimplexCategory.toTopObj n) := by
  induction' n using SimplexCategory.rec with n
  refine ⟨⟨SimplexCategory.toTopMap (⦋0⦌.const ⦋n⦌ 0) default⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ ↦
    ⟨⟨fun t ↦ ⟨fun i ↦ ⟨(1 - t) * (x i).1 + t * (y i).1, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩⟩
  · apply add_nonneg
    · exact mul_nonneg (by simpa only [sub_nonneg] using t.2.2) (x i).2
    · exact mul_nonneg t.2.1 (y i).2
  · ext
    simp only [SimplexCategory.toTopObj, Set.mem_setOf_eq] at hx hy
    rw [Subtype.ext_iff, NNReal.sum_coe] at hx hy
    dsimp at hx hy
    refine (NNReal.sum_coe _).trans ?_
    dsimp
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy]
    ring
  · continuity
  · aesop
  · aesop

instance (n : ℕ) : PathConnectedSpace |Δ[n]| :=
  ⦋n⦌.toTopHomeo.symm.surjective.pathConnectedSpace (by continuity)

lemma π₀.eq_of_path {X : TopCat.{0}} {x y : X} (p : _root_.Path x y) :
    π₀.mk (TopCat.toSSetObj₀Equiv.symm x) =
      π₀.mk (TopCat.toSSetObj₀Equiv.symm y) := by
  let e := stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{0}
  refine π₀.sound
    (TopCat.toSSetObjEquiv.symm (p.comp (ContinuousMap.comp ⟨_, continuous_uliftDown⟩
    ⟨_, stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{0}.continuous_toFun⟩))) ?_ ?_
  · apply TopCat.toSSetObj₀Equiv.injective
    dsimp
    rw [TopCat.toSSetObj₀Equiv_toSSet_obj_δ_one]
    change p (e (e.symm 0)).1 = _
    aesop
  · apply TopCat.toSSetObj₀Equiv.injective
    dsimp
    rw [TopCat.toSSetObj₀Equiv_toSSet_obj_δ_zero]
    change p (e (e.symm 1)).1 = _
    aesop

variable (X : SSet.{0})

lemma surjective_mapπ₀_sSetTopAdj_unit_app :
    Function.Surjective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  intro x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective x
  obtain ⟨⟨⟨n⟩, s⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget _)
    (X.isColimitCoconeFromElementsOp)) x
  induction' n using SimplexCategory.rec with n
  dsimp at x
  refine ⟨π₀.mk (X.map (⦋0⦌.const ⦋n⦌ 0).op s), ?_⟩
  dsimp [-TopCat.toSSetObj₀Equiv_symm_apply]
  let x₀ := (toTop.map (stdSimplex.map (⦋0⦌.const ⦋n⦌ 0)) default)
  refine Eq.trans ?_ (congr_arg (mapπ₀ (TopCat.toSSet.map (toTop.map (yonedaEquiv.symm s))))
    (π₀.eq_of_path (PathConnectedSpace.somePath x₀ x)))
  simp only [TopCat.toSSetObj₀Equiv_symm_apply, mapπ₀_mk]
  congr
  have := congr_fun (congr_app (sSetTopAdj.unit.naturality (yonedaEquiv.symm s)) (op ⦋0⦌))
    (stdSimplex.obj₀Equiv.symm 0)
  dsimp at this
  convert this
  apply TopCat.toSSetObj₀Equiv.injective
  dsimp [TopCat.toSSetObj₀Equiv, x₀]
  let f : ⦋0⦌ ⟶ ⦋n⦌ := SimplexCategory.const _ _ 0
  have : toTop.map (stdSimplex.map f) =
    TopCat.ofHom ((TopCat.toSSetObjEquiv
      (((sSetTopAdj.unit.app Δ[n]).app (op ⦋0⦌)) (yonedaEquiv (stdSimplex.map f)))).comp
      (toContinuousMap ⦋0⦌.toTopHomeo)) := by
    ext x₀
    have h₁ : (stdSimplex.{0}.map f).app (op ⦋0⦌) (yonedaEquiv (𝟙 Δ[0])) =
      yonedaEquiv (stdSimplex.map f) := rfl
    have h₂ := congr_fun (congr_app (sSetTopAdj.unit.naturality (stdSimplex.map f)) (op ⦋0⦌))
      (yonedaEquiv (𝟙 _))
    dsimp at h₂ ⊢
    rw [← h₁, h₂]
    apply congr_arg (toTop.map (stdSimplex.map f))
    apply Subsingleton.elim
  rw [this, Subsingleton.elim default (⦋0⦌.toTopHomeo default)]
  rfl

lemma bijective_mapπ₀_sSetTopAdj_unit_app :
    Function.Bijective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  sorry

end SSet
