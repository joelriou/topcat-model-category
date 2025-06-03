import TopCatModelCategory.SSet.HomotopySequence
import TopCatModelCategory.SSet.Fibrations
import Mathlib.CategoryTheory.Adjunction.Unique

universe u

open CategoryTheory Monoidal Simplicial MonoidalCategory MonoidalClosed
  SSet.modelCategoryQuillen HomotopicalAlgebra Opposite
  ChosenFiniteProducts

namespace SSet

variable (X : SSet.{u}) (x : X _⦋0⦌)

namespace stdSimplex

noncomputable def ihom₀ : ihom Δ[0] ≅ 𝟭 SSet.{u} :=
  Adjunction.rightAdjointUniq (ihom.adjunction Δ[0])
    (Adjunction.id.ofNatIsoLeft
      (NatIso.ofComponents (fun X ↦ (leftUnitor X).symm) ))

lemma ihom₀_inv_app : ihom₀.inv.app X =
  curry (leftUnitor X).hom := rfl

end stdSimplex

noncomputable def pathEv₀ : (ihom Δ[1]).obj X ⟶ X :=
  (pre (stdSimplex.δ (0 : Fin 2))).app X ≫
    stdSimplex.ihom₀.hom.app _

instance [IsFibrant X] (i : Fin 2) :
    Fibration ((pre (stdSimplex.δ i)).app X) := by
  sorry

instance [IsFibrant X] : Fibration (X.pathEv₀) := by
  dsimp [pathEv₀]
  infer_instance

protected noncomputable def path₀ :
    Subcomplex ((ihom Δ[1]).obj X) :=
  Subcomplex.fiber X.pathEv₀ x

noncomputable def path₀Ev₁ : (X.path₀ x : SSet) ⟶ X :=
  Subcomplex.ι _ ≫
    (pre (stdSimplex.δ (1 : Fin 2))).app X ≫
      (stdSimplex.ihom₀.app X).hom

instance [IsFibrant X] : Fibration (X.path₀Ev₁ x) := by
  sorry

noncomputable def path₀Const : (X.path₀ x : SSet) _⦋0⦌ :=
  ⟨ihom₀Equiv.symm (const x), by
    have : curry (snd Δ[1] X) ≫ (pre (stdSimplex.δ (0 : Fin 2))).app X =
        curry (stdSimplex.leftUnitor X).hom := by
      apply uncurry_injective
      rw [uncurry_curry]
      rw [uncurry_natural_left]
      sorry
    simp only [SSet.path₀, pathEv₀, Subcomplex.mem_fiber_obj_zero_iff]
    apply ((stdSimplex.ihom₀.app X).app (op ⦋0⦌)).toEquiv.symm.injective
    dsimp
    rw [← FunctorToTypes.comp, Iso.hom_inv_id_app,
      NatTrans.id_app, types_id_apply,
      stdSimplex.ihom₀_inv_app, ← this, comp_app,
      types_comp_apply]
    apply congr_arg
    apply ihom₀Equiv.injective
    rw [Equiv.apply_symm_apply]
    rfl⟩

@[simp]
lemma path₀Ev₁_app_path₀Const :
    (X.path₀Ev₁ x).app (op ⦋0⦌) (X.path₀Const x) = x := by
  sorry

def loop : Subcomplex (X.path₀ x) :=
  Subcomplex.fiber (X.path₀Ev₁ x) x

@[reassoc (attr := simp)]
lemma loop_ι_path₀Ev₁ : (X.loop x).ι ≫ X.path₀Ev₁ x = const x := by
  simp [loop]

noncomputable def loop.basePoint : (X.loop x : SSet) _⦋0⦌ :=
  Subcomplex.fiber.basePoint _ (path₀Ev₁_app_path₀Const X x)

end SSet
