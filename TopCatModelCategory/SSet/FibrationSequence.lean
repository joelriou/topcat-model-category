import TopCatModelCategory.SSet.HomotopySequence
import TopCatModelCategory.SSet.Fibrations

open CategoryTheory Simplicial HomotopicalAlgebra
  SSet.modelCategoryQuillen Limits Opposite

namespace SSet

structure FibrationSequence where
  F : SSet.{u}
  E : SSet.{u}
  B : SSet.{u}
  i : F ⟶ E
  p : E ⟶ B
  hp : Fibration p := by infer_instance
  f : F _⦋0⦌
  e : E _⦋0⦌
  b : B _⦋0⦌
  hf : i.app _ f = e
  he : p.app _ e = b
  isPullback : IsPullback i (stdSimplex.objZeroIsTerminal.from F)
      p (yonedaEquiv.symm b)

namespace FibrationSequence

attribute [instance] hp
attribute [simp] hf he

section

@[simps]
def ofFibration {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    {e : E _⦋0⦌} {b : B _⦋0⦌}
    (he : p.app _ e = b) : FibrationSequence where
  p := p
  isPullback := Subcomplex.fiber_isPullback p b
  f := KanComplex.HomotopySequence.basePoint p he
  hf := rfl
  he := he

variable (seq : FibrationSequence.{u})

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
      KanComplex.HomotopySequence.basePoint seq.p seq.he := by
  aesop

@[simp]
lemma isoFiber_inv_app_f :
    seq.isoFiber.inv.app _ (KanComplex.HomotopySequence.basePoint seq.p seq.he) =
      seq.f := by
  rw [← isoFiber_hom_app_f]
  exact congr_fun (seq.isoFiber.hom_inv_id_app _) _

instance : IsFibrant seq.F := isFibrant_of_iso seq.isoFiber.symm

end

@[ext]
structure Hom (seq₁ seq₂ : FibrationSequence.{u}) where
  mor₁ : seq₁.F ⟶ seq₂.F
  mor₂ : seq₁.E ⟶ seq₂.E
  mor₃ : seq₁.B ⟶ seq₂.B
  comm_i : seq₁.i ≫ mor₂ = mor₁ ≫ seq₂.i := by aesop_cat
  comm_p : seq₁.p ≫ mor₃ = mor₂ ≫ seq₂.p := by aesop_cat
  mor₁_app_f : mor₁.app _ seq₁.f = seq₂.f := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm_i Hom.comm_p
attribute [simp] Hom.mor₁_app_f

instance : Category FibrationSequence.{u} where
  Hom := Hom
  id seq :=
    { mor₁ := 𝟙 _
      mor₂ := 𝟙 _
      mor₃ := 𝟙 _ }
  comp f g :=
    { mor₁ := f.mor₁ ≫ g.mor₁
      mor₂ := f.mor₂ ≫ g.mor₂
      mor₃ := f.mor₃ ≫ g.mor₃ }

@[simp] lemma id_mor₁ (seq : FibrationSequence) : Hom.mor₁ (𝟙 seq) = 𝟙 _ := rfl
@[simp] lemma id_mor₂ (seq : FibrationSequence) : Hom.mor₂ (𝟙 seq) = 𝟙 _ := rfl
@[simp] lemma id_mor₃ (seq : FibrationSequence) : Hom.mor₃ (𝟙 seq) = 𝟙 _ := rfl

section

variable {seq₁ seq₂ seq₃ : FibrationSequence.{u}} (f : seq₁ ⟶ seq₂) (g : seq₂ ⟶ seq₃)

@[reassoc, simp] lemma comp_mor₁ : (f ≫ g).mor₁ = f.mor₁ ≫ g.mor₁ := rfl
@[reassoc, simp] lemma comp_mor₂ : (f ≫ g).mor₂ = f.mor₂ ≫ g.mor₂ := rfl
@[reassoc, simp] lemma comp_mor₃ : (f ≫ g).mor₃ = f.mor₃ ≫ g.mor₃ := rfl

end

section

open KanComplex

variable (seq : FibrationSequence.{u}) [IsFibrant seq.B]

instance : IsFibrant seq.E := by
  rw [isFibrant_iff,
    Subsingleton.elim (terminal.from seq.E) (seq.p ≫ terminal.from seq.B)]
  infer_instance

noncomputable def δ (n : ℕ) : π (n + 1) seq.B seq.b → π n seq.F seq.f :=
  (mapπ seq.isoFiber.inv n
    (HomotopySequence.basePoint seq.p seq.he) seq.f (by simp)).comp
      (HomotopySequence.δ' seq.p seq.he n 0)

end

end FibrationSequence

end SSet
