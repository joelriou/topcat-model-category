import TopCatModelCategory.SSet.HomotopySequence
import Mathlib.CategoryTheory.Adjunction.Unique

universe u

open CategoryTheory Monoidal Simplicial MonoidalCategory MonoidalClosed
  SSet.modelCategoryQuillen HomotopicalAlgebra

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

protected noncomputable def path₀ :
    Subcomplex ((ihom Δ[1]).obj X) :=
  Subcomplex.fiber X.pathEv₀ x

noncomputable def path₀Ev₁ : (X.path₀ x : SSet) ⟶ X :=
  Subcomplex.ι _ ≫
    (pre (stdSimplex.δ (1 : Fin 2))).app X ≫
      (stdSimplex.ihom₀.app X).hom

def loop : Subcomplex (X.path₀ x) :=
  Subcomplex.fiber (X.path₀Ev₁ x) x

@[reassoc (attr := simp)]
lemma loop_ι_path₀Ev₁ : (X.loop x).ι ≫ X.path₀Ev₁ x = const x := by
  simp [loop]

end SSet
