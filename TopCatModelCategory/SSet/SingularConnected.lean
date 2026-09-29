module

public import TopCatModelCategory.SSet.ConnectedComponents
public import TopCatModelCategory.SSet.PiZero
public import TopCatModelCategory.TopCat.Adj
public import TopCatModelCategory.TopCat.CoyonedaPreservesCoproducts

@[expose] public section

universe u

open Simplicial CategoryTheory Limits Opposite NNReal

namespace CategoryTheory

namespace ObjectProperty

variable {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (τ : F ⟶ G)

def isIsoNatTransApp : ObjectProperty C :=
  fun X ↦ IsIso (τ.app X)

instance closedUnderCoproducts_isIsoNatTransApp (J : Type*) [Category J]
    [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G] :
    IsClosedUnderColimitsOfShape (isIsoNatTransApp τ) J := by
  -- the proof needs a small fix
  suffices ∀ (F : J ⥤ C) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ x, isIsoNatTransApp τ (F.obj x)), isIsoNatTransApp τ c.pt from ⟨by
      rintro F ⟨h⟩
      exact this _ _ h.isColimit h.prop_diag_obj⟩
  intro K c hc hK
  have (j : J) : IsIso (τ.app (K.obj j)) := by simpa [isIsoNatTransApp] using hK j
  let e (j : J) : F.obj (K.obj j) ≅ G.obj (K.obj j) := asIso (τ.app (K.obj j))
  obtain ⟨φ, hφ⟩ : ∃ (φ : G.obj c.pt ⟶ F.obj c.pt),
      ∀ (j : J), G.map (c.ι.app j) ≫ φ = (e j).inv ≫ F.map (c.ι.app j) :=
    ⟨(isColimitOfPreserves G hc).desc (Cocone.mk _
      { app j := (e j).inv ≫ F.map (c.ι.app j)
        naturality j₁ j₂ f := by
          dsimp [e]
          rw [Category.comp_id, IsIso.eq_inv_comp, NatIso.naturality_2'_assoc, ← c.w f,
            Functor.map_comp] }),
      (isColimitOfPreserves G hc).fac _⟩
  exact ⟨φ, (isColimitOfPreserves F hc).hom_ext (fun j ↦ by simp [hφ, e]),
    (isColimitOfPreserves G hc).hom_ext (fun j ↦ by simp [reassoc_of% hφ, e])⟩

end ObjectProperty

end CategoryTheory

@[simp]
lemma NNReal.sum_coe {α : Type*} [Fintype α] (f : α → ℝ≥0) :
    (Finset.univ.sum f).1 = Finset.univ.sum (fun i ↦ (f i).1) := by
  let coeℝ : ℝ≥0 →+ ℝ := AddMonoidHom.mk' (fun (x : ℝ≥0) ↦ x.1) (by aesop)
  apply map_sum coeℝ

namespace SSet

instance (n : ℕ) : PathConnectedSpace |Δ[n]| :=
  ⦋n⦌.toTopHomeo.symm.surjective.pathConnectedSpace (by continuity)

lemma π₀.eq_of_path {X : TopCat.{u}} {x y : X} (p : _root_.Path x y) :
    π₀.mk (TopCat.toSSetObj₀Equiv.symm x) =
      π₀.mk (TopCat.toSSetObj₀Equiv.symm y) := by
  let e := stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}
  refine π₀.sound
    ((TopCat.toSSetObjEquiv _ _).symm (p.comp (ContinuousMap.comp ⟨_, continuous_uliftDown⟩
    ⟨_, stdSimplex.simplexCategoryToTopObjHomeoUnitInterval.{u}.continuous_toFun⟩))) ?_ ?_
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

variable (X : SSet.{u})

lemma surjective_mapπ₀_sSetTopAdj_unit_app :
    Function.Surjective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  intro x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨x, rfl⟩ := TopCat.toSSetObj₀Equiv.symm.surjective x
  obtain ⟨⟨⟨n⟩, s⟩, x, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget _)
    (X.isColimitCoconeFromElementsOp)) x
  induction n using SimplexCategory.rec with | _ n
  dsimp at x
  refine ⟨π₀.mk (X.map (⦋0⦌.const ⦋n⦌ 0).op s), ?_⟩
  dsimp [-TopCat.toSSetObj₀Equiv_symm_apply]
  let x₀ := (toTop.map (SSet.stdSimplex.map (⦋0⦌.const ⦋n⦌ 0)) (by exact default))
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
  have : toTop.{u}.map (SSet.stdSimplex.map f) =
    TopCat.ofHom ((TopCat.toSSetObjEquiv _ _
      (((sSetTopAdj.unit.app Δ[n]).app (op ⦋0⦌)) (yonedaEquiv (SSet.stdSimplex.map f)))).comp
      (toContinuousMap ⦋0⦌.toTopHomeo)) := by
    ext x₀
    have h₁ : (stdSimplex.{u}.map f).app (op ⦋0⦌) (yonedaEquiv (𝟙 Δ[0])) =
      yonedaEquiv (SSet.stdSimplex.map f) := rfl
    have h₂ := congr_fun (congr_app (sSetTopAdj.unit.naturality (SSet.stdSimplex.map f)) (op ⦋0⦌))
      (yonedaEquiv (𝟙 _))
    dsimp at h₂ ⊢
    rw [← h₁, h₂]
    apply congr_arg (toTop.map (SSet.stdSimplex.map f))
    apply Subsingleton.elim
  rfl

def isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp : ObjectProperty SSet.{u} :=
  fun X ↦ IsIso ((Functor.whiskerRight sSetTopAdj.{u}.unit π₀Functor).app X)

lemma isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp_of_connected (X : SSet.{u})
    (hX : Subsingleton (π₀ X)) :
    isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp X := by
  simp only [isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp, Functor.comp_obj, Functor.id_obj,
    π₀Functor_obj, Functor.whiskerRight_app, isIso_iff_bijective]
  exact ⟨Function.injective_of_subsingleton (α := π₀ X) _,
      surjective_mapπ₀_sSetTopAdj_unit_app X⟩

lemma isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp_eq_top :
    isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp.{u} = ⊤ := by
  change ObjectProperty.isIsoNatTransApp _ = ⊤
  ext X
  simp only [Pi.top_apply, «Prop».top_eq_true, iff_true]
  apply ObjectProperty.prop_of_isColimit _ (π₀.isColimitCofan X)
  rintro ⟨c⟩
  apply isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp_of_connected
  dsimp
  infer_instance

lemma bijective_mapπ₀_sSetTopAdj_unit_app :
    Function.Bijective (mapπ₀ (sSetTopAdj.unit.app X)) := by
  simp only [← isIso_iff_bijective]
  exact isIsoWhiskerRightSSetTopAdjUnitπ₀FunctorApp_eq_top.ge _ (by simp)

end SSet
