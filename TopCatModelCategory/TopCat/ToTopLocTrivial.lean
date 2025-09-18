import TopCatModelCategory.SSet.MinimalFibrationsLemmas
import TopCatModelCategory.TrivialBundleOver
import TopCatModelCategory.TopCat.SerreFibrationBundle
import TopCatModelCategory.ModelCategoryTopCat

universe u

open Simplicial CategoryTheory MorphismProperty HomotopicalAlgebra
  TopCat.modelCategory Limits

namespace SSet

variable {E B : SSet.{u}} {p : E ⟶ B} {F : SSet.{u}}
  (τ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ)

namespace MinimalFibrationLocTrivial

section

noncomputable abbrev pull (_ : ∀ ⦃n : ℕ⦄ (σ : Δ[n] ⟶ B), TrivialBundleWithFiberOver F p σ) :=
    Over.pullback ((toDeltaGenerated.map p))

variable (A : Over (toDeltaGenerated.obj B))

noncomputable def pullObj : DeltaGenerated'.{u} := ((pull τ).obj A).left

noncomputable def ι : pullObj τ A ⟶ toDeltaGenerated.obj E := ((pull τ).obj A).hom

noncomputable def π : pullObj τ A ⟶ A.left := pullback.fst _ _

lemma isPullback : IsPullback (ι τ A) (π τ A) (toDeltaGenerated.map p) A.hom :=
  (IsPullback.of_hasPullback _ _).flip

def IsTrivial : Prop := trivialBundlesWithFiber (toDeltaGenerated.obj F) (π τ A)

def IsLocTrivial : Prop :=
  (trivialBundlesWithFiber (toDeltaGenerated.obj F)).locally
    GeneratedByTopCat.grothendieckTopology (π τ A)

section

variable {Z : DeltaGenerated'.{u}} {t : Z ⟶ toDeltaGenerated.obj E}
    {l : Z ⟶ A.left} (sq : IsPullback t l (toDeltaGenerated.map p) A.hom)

include sq

noncomputable def objIso : pullObj τ A ≅ Z :=
  (IsPullback.exists_iso_of_isos (isPullback τ A) sq (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)).choose

@[reassoc (attr := simp)]
lemma objIso_hom_comp_eq_π : (objIso τ A sq).hom ≫ l = π τ A := by
  simpa using ((IsPullback.exists_iso_of_isos (isPullback τ A) sq (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) (by simp)).choose_spec.2).symm

end

end

lemma isLocTrivial {Z : SSet.{u}} [IsFinite Z] (a : Z ⟶ B) :
    IsLocTrivial τ (Over.mk (toDeltaGenerated.map a)) := by
  sorry

end MinimalFibrationLocTrivial

variable (p) in
open MinimalFibrationLocTrivial MorphismProperty in
include τ in
lemma fibration_toTop_map_of_trivialBundle_over_simplices [IsFinite B] :
    Fibration (toTop.map p) := by
  let e : Arrow.mk (π τ (Over.mk (toDeltaGenerated.map (𝟙 B)))) ≅ Arrow.mk (toDeltaGenerated.map p) := by
    have : IsPullback (𝟙 (toDeltaGenerated.obj E)) (toDeltaGenerated.map p)
        (toDeltaGenerated.map p) (toDeltaGenerated.map (𝟙 B)) := by
      simpa using IsPullback.id_horiz (toDeltaGenerated.map p)
    exact Arrow.isoMk (objIso τ _ this) (Iso.refl _)
  exact DeltaGenerated'.fibration_toTopCat_map_of_locally_trivialBundle
    ((arrow_mk_iso_iff _ e).1
      (locally_monotone (trivialBundlesWithFiber_le_trivialBundles _) _ _ (isLocTrivial τ (𝟙 B))))

end SSet
