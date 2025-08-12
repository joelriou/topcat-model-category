import TopCatModelCategory.SSet.Monoidal
import TopCatModelCategory.SSet.Homotopy
import Mathlib.CategoryTheory.Retract

universe u

open CategoryTheory Category MonoidalCategory Simplicial
  CartesianMonoidalCategory

namespace SSet

variable (X Y : SSet.{u})

structure DeformationRetract extends Retract X Y where
  h : Y ⊗ Δ[1] ⟶ Y
  hi : toRetract.i ▷ _ ≫ h = fst _ _ ≫ toRetract.i := by aesop_cat
  h₀ : ι₀ ≫ h = r ≫ i := by aesop_cat
  h₁ : ι₁ ≫ h = 𝟙 Y := by aesop_cat

namespace DeformationRetract

attribute [reassoc (attr := simp)] hi h₁ h₀

variable {X Y} (d : DeformationRetract X Y)

@[reassoc (attr := simp)]
lemma i_ι₀ : d.i ≫ ι₀ ≫ d.h = d.i := by
  simpa only [ι₀_comp_assoc, lift_fst_assoc, id_comp] using ι₀ ≫= d.hi

@[simps]
def homotopy : Homotopy (d.r ≫ d.i) (𝟙 Y) where
  h := d.h

end DeformationRetract

variable {X Y} {B : SSet.{u}} (p : X ⟶ B) (q : Y ⟶ B)

structure FiberwiseDeformationRetract extends DeformationRetract X Y where
  wr : r ≫ p = q
  wh : h ≫ q = fst _ _ ≫ q

namespace FiberwiseDeformationRetract

variable {p q} (d : FiberwiseDeformationRetract p q)

attribute [reassoc (attr := simp)] wr wh

@[reassoc (attr := simp)]
lemma wi : d.i ≫ q = p := by
  simp only [← d.wr, d.retract_assoc]

@[simps]
def retractArrow : RetractArrow p q where
  i := Arrow.homMk d.i (𝟙 B)
  r := Arrow.homMk d.r (𝟙 B)

end FiberwiseDeformationRetract

namespace Subcomplex

variable (A : X.Subcomplex)

structure DeformationRetract extends SSet.DeformationRetract A X where
  i_eq_ι : i = A.ι

structure FiberwiseDeformationRetract (p : X ⟶ B)
    extends SSet.FiberwiseDeformationRetract (A.ι ≫ p) p where
  i_eq_ι : i = A.ι

end Subcomplex

end SSet
