import TopCatModelCategory.SSet.HomotopySequence

open CategoryTheory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen Limits

namespace SSet

structure FibrationSequence where
  F : SSet.{u}
  E : SSet.{u}
  B : SSet.{u}
  i : F ⟶ E
  p : E ⟶ B
  hp : Fibration p
  f : F _⦋0⦌
  e : E _⦋0⦌
  b : B _⦋0⦌
  he : i.app _ f = e
  hb : p.app _ e = b
  isPullback : IsPullback i (stdSimplex.objZeroIsTerminal.from F)
      p (yonedaEquiv.symm b)

variable (seq : FibrationSequence.{u})

namespace FibrationSequence

attribute [instance] hp
attribute [simp] he hb

noncomputable def isoFiber : seq.F ≅ Subcomplex.fiber seq.p seq.b :=
  IsLimit.conePointUniqueUpToIso seq.isPullback.isLimit
    (Subcomplex.fiber_isPullback seq.p seq.b).isLimit

@[reassoc (attr := simp)]
lemma isoFiber_hom_ι : seq.isoFiber.hom ≫ Subcomplex.ι _ = seq.i :=
  IsLimit.conePointUniqueUpToIso_hom_comp seq.isPullback.isLimit
    (Subcomplex.fiber_isPullback seq.p seq.b).isLimit .left

@[simp]
lemma coe_isoFiber_hom_app {n : SimplexCategoryᵒᵖ} (x : seq.F.obj n) :
    (seq.isoFiber.hom.app _ x).1 = seq.i.app _ x :=
  congr_fun (congr_app seq.isoFiber_hom_ι n) x

@[reassoc (attr := simp)]
lemma isoFiber_inv_i : seq.isoFiber.inv ≫ seq.i = Subcomplex.ι _ :=
  IsLimit.conePointUniqueUpToIso_inv_comp seq.isPullback.isLimit
    (Subcomplex.fiber_isPullback seq.p seq.b).isLimit .left

@[simp]
lemma isoFiber_hom_app_f :
    seq.isoFiber.hom.app _ seq.f =
      KanComplex.HomotopySequence.basePoint seq.p seq.hb := by
  aesop

instance : IsFibrant seq.F := isFibrant_of_iso seq.isoFiber.symm

end FibrationSequence

end SSet
