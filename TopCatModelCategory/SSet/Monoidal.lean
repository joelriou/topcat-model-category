import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Closed.Monoidal
import TopCatModelCategory.MonoidalClosed
import TopCatModelCategory.SSet.Basic
import TopCatModelCategory.SSet.StandardSimplex

universe u

open CategoryTheory MonoidalCategory Simplicial Opposite Limits
  ChosenFiniteProducts

namespace SSet

section

variable {X : SSet.{u}}

noncomputable def ι₀ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 0))

@[reassoc (attr := simp)]
lemma ι₀_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₀ ≫ f ▷ _ = f ≫ ι₀ := rfl

@[reassoc (attr := simp)]
lemma ι₀_fst (X : SSet.{u}) : ι₀ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₀_snd (X : SSet.{u}) : ι₀ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 0)) := rfl

@[simp]
lemma ι₀_app_fst {X : SSet.{u}} {m} (x : X.obj m) : (ι₀.app _ x).1 = x := rfl

noncomputable def ι₁ {X : SSet.{u}} : X ⟶ X ⊗ Δ[1] :=
  lift (𝟙 X) (const (stdSimplex.obj₀Equiv.{u}.symm 1))

@[reassoc (attr := simp)]
lemma ι₁_fst (X : SSet.{u}) : ι₁ ≫ fst X _ = 𝟙 X := rfl

@[reassoc (attr := simp)]
lemma ι₁_snd (X : SSet.{u}) : ι₁ ≫ snd X _ = (const (stdSimplex.obj₀Equiv.{u}.symm 1)) := rfl

@[reassoc (attr := simp)]
lemma ι₁_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    ι₁ ≫ f ▷ _ = f ≫ ι₁ := rfl

@[simp]
lemma ι₁_app_fst {X : SSet.{u}} {m} (x : X.obj m) : (ι₁.app _ x).1 = x := rfl

end

namespace stdSimplex

variable (X) {Y : SSet.{u}}

def isTerminalObj₀ : IsTerminal (Δ[0] : SSet.{u}) :=
  IsTerminal.ofUniqueHom (fun _ ↦ SSet.const (obj₀Equiv.symm 0)) (fun _ _ ↦ by ext; simp)

noncomputable def leftUnitor : Δ[0] ⊗ X ≅ X where
  hom := snd _ _
  inv := lift (isTerminalObj₀.from _) (𝟙 X)

@[reassoc (attr := simp)]
lemma leftUnitor_inv_snd : (leftUnitor X).inv ≫ snd _ _ = 𝟙 _ := rfl

@[reassoc (attr := simp)]
lemma snd_leftUnitor_inv : snd _ _ ≫ (leftUnitor X).inv = 𝟙 _ := by
  rw [← cancel_epi (leftUnitor X).inv,
    leftUnitor_inv_snd_assoc, Category.comp_id]

variable {X} in
@[reassoc (attr := simp)]
lemma leftUnitor_inv_naturality (f : X ⟶ Y) :
    (leftUnitor X).inv ≫ _ ◁ f = f ≫ (leftUnitor Y).inv := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma leftUnitor_hom_naturality (f : X ⟶ Y) :
    _ ◁ f  ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_map_δ_zero :
    (stdSimplex.leftUnitor X).inv ≫ stdSimplex.δ 0 ▷ X =
      ι₁ ≫ (β_ _ _).hom := rfl

@[reassoc (attr := simp)]
lemma leftUnitor_inv_map_δ_one :
    (stdSimplex.leftUnitor X).inv ≫ stdSimplex.δ 1 ▷ X =
      ι₀ ≫ (β_ _ _).hom := rfl

@[reassoc]
lemma _root_.SSet.ι₀_stdSimplex_zero :
    ι₀ = stdSimplex.δ 1 ≫ (stdSimplex.leftUnitor Δ[1]).inv := by
  ext : 1
  all_goals exact yonedaEquiv.injective (by ext i; fin_cases i; rfl)

@[reassoc]
lemma _root_.SSet.ι₁_stdSimplex_zero :
    ι₁ = stdSimplex.δ 0 ≫ (stdSimplex.leftUnitor Δ[1]).inv := by
  ext : 1
  all_goals exact yonedaEquiv.injective (by ext i; fin_cases i; rfl)

@[simps -isSimp]
noncomputable def rightUnitor : X ⊗ Δ[0] ≅ X where
  hom := fst _ _
  inv := lift (𝟙 X) (isTerminalObj₀.from _)

@[reassoc (attr := simp)]
lemma rightUnitor_inv_fst : (rightUnitor X).inv ≫ fst _ _ = 𝟙 _ := rfl

@[reassoc (attr := simp)]
lemma fst_rightUnitor_inv : fst _ _ ≫ (rightUnitor X).inv = 𝟙 _ := by
  rw [← cancel_epi (rightUnitor X).inv,
    rightUnitor_inv_fst_assoc, Category.comp_id]

variable {X} in
@[reassoc (attr := simp)]
lemma rightUnitor_inv_naturality (f : X ⟶ Y) :
    (rightUnitor X).inv ≫ f ▷ _ = f ≫ (rightUnitor Y).inv := rfl

variable {X} in
@[reassoc (attr := simp)]
lemma rightUnitor_hom_naturality (f : X ⟶ Y) :
    f ▷ _ ≫  (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_zero :
    (stdSimplex.rightUnitor X).inv ≫ X ◁ stdSimplex.δ 0 =
      ι₁ := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_inv_map_δ_one :
    (stdSimplex.rightUnitor X).inv ≫ X ◁ stdSimplex.δ 1 =
      ι₀ := rfl

@[reassoc (attr := simp)]
lemma rightUnitor_hom_ι₀ :
    (stdSimplex.rightUnitor X).hom ≫ ι₀ = X ◁ stdSimplex.δ 1 := by
  rw [← rightUnitor_inv_map_δ_one, Iso.hom_inv_id_assoc]

@[reassoc (attr := simp)]
lemma rightUnitor_hom_ι₁ :
    (stdSimplex.rightUnitor X).hom ≫ ι₁ = X ◁ stdSimplex.δ 0 := by
  rw [← rightUnitor_inv_map_δ_zero, Iso.hom_inv_id_assoc]

end stdSimplex

instance : MonoidalClosed (SSet.{u}) :=
  inferInstanceAs (MonoidalClosed (SimplexCategoryᵒᵖ ⥤ Type u))

variable {X Y : SSet.{u}}

noncomputable def ihom₀Equiv : ((ihom X).obj Y) _⦋0⦌ ≃ (X ⟶ Y) :=
  yonedaEquiv.symm.trans
    (((ihom.adjunction X).homEquiv Δ[0] Y).symm.trans
      (Iso.homFromEquiv (stdSimplex.rightUnitor X)))

lemma ihom₀Equiv_symm_comp {Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ihom₀Equiv.symm (f ≫ g) =
      ((MonoidalClosed.pre f).app Z).app (op ⦋0⦌) (ihom₀Equiv.symm g) := rfl

lemma ihom₀Equiv_symm_comp' {Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ihom₀Equiv.symm (f ≫ g) =
      ((ihom X).map g).app (op ⦋0⦌) (ihom₀Equiv.symm f) := rfl

lemma yonedaEquiv_fst {n : ℕ} (f : Δ[n] ⟶ X ⊗ Y) :
    (yonedaEquiv f).1 = yonedaEquiv (f ≫ fst _ _) := rfl

lemma yonedaEquiv_snd {n : ℕ} (f : Δ[n] ⟶ X ⊗ Y) :
    (yonedaEquiv f).2 = yonedaEquiv (f ≫ snd _ _) := rfl

end SSet
