import TopCatModelCategory.SSet.HomotopySequence
import TopCatModelCategory.SSet.Fibrations
import TopCatModelCategory.SSet.Loop

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
  hf : i.app _ f = e := by aesop_cat
  he : p.app _ e = b := by aesop_cat
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
  f := Subcomplex.fiber.basePoint p he
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
      Subcomplex.fiber.basePoint seq.p seq.he := by
  aesop

@[simp]
lemma isoFiber_inv_app_f :
    seq.isoFiber.inv.app _ (Subcomplex.fiber.basePoint seq.p seq.he) =
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

namespace Hom

@[simp]
lemma mor₂_app_e {seq seq' : FibrationSequence}
    (φ : seq ⟶ seq') : φ.mor₂.app _ seq.e = seq'.e := by
  simp only [← seq.hf, ← seq'.hf, ← φ.mor₁_app_f, ← FunctorToTypes.comp, φ.comm_i]

@[simp]
lemma mor₃_app_b {seq seq' : FibrationSequence}
    (φ : seq ⟶ seq') : φ.mor₃.app _ seq.b = seq'.b := by
  simp only [← seq.he, ← seq'.he, ← mor₂_app_e φ, ← FunctorToTypes.comp, φ.comm_p]

end Hom

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

open HomotopySequence

noncomputable def δ (n : ℕ) : π (n + 1) seq.B seq.b → π n seq.F seq.f :=
  (mapπ seq.isoFiber.inv n
    (Subcomplex.fiber.basePoint seq.p seq.he) seq.f (by simp)).comp
      (HomotopySequence.δ' seq.p seq.he n 0)

lemma exact₂ {n : ℕ} (x₂ : π n seq.E seq.e)
    (hx₂ : mapπ seq.p n seq.e seq.b seq.he x₂ = 1) :
    ∃ (x₁ : π n seq.F seq.f), mapπ seq.i n seq.f seq.e seq.hf x₁ = x₂ := by
  obtain ⟨y₁, rfl⟩ := exists_of_map₂_eq_one hx₂
  refine ⟨mapπ seq.isoFiber.inv n (Subcomplex.fiber.basePoint seq.p seq.he) seq.f (by simp) y₁, ?_⟩
  simp only [mapπ_mapπ, isoFiber_inv_i]
  rfl

lemma exact₁ {n : ℕ} (x₁ : π n seq.F seq.f)
    (hx₁ : mapπ seq.i n seq.f seq.e seq.hf x₁ = 1) :
    ∃ (x₃ : π (n + 1) seq.B seq.b),
      seq.δ n x₃ = x₁ := by
  obtain ⟨x₃, hx₃⟩ := exists_of_map₁_eq_one
    (x := mapπ seq.isoFiber.hom n seq.f (Subcomplex.fiber.basePoint seq.p seq.he) (by simp) x₁)
      (by simpa only [map₁, mapπ_mapπ, isoFiber_hom_ι]) 0
  refine ⟨x₃, ?_⟩
  dsimp [δ]
  simp only [hx₃, mapπ_mapπ, Iso.hom_inv_id, mapπ_id]

lemma exact₃ {n : ℕ} (x₃ : π (n + 1) seq.B seq.b)
    (hx₃ : seq.δ n x₃ = 1) :
    ∃ (x₂ : π (n + 1) seq.E seq.e),
      mapπ seq.p (n + 1) seq.e seq.b seq.he x₂ = x₃ := by
  apply exists_of_δ'_eq_one (x := x₃) (i := 0)
  apply (mapπEquivOfIso seq.isoFiber n seq.f
    (Subcomplex.fiber.basePoint seq.p seq.he) (by simp)).symm.injective
  simpa

end

open KanComplex

variable {seq seq' : FibrationSequence.{u}}
  (φ : seq ⟶ seq')

@[reassoc (attr := simp)]
lemma isoFiber_hom_mapFiber :
    seq.isoFiber.hom ≫
      Subcomplex.mapFiber seq.p seq'.p φ.mor₂ φ.mor₃ (by simp) seq.b seq'.b (by simp) =
    φ.mor₁ ≫ seq'.isoFiber.hom := by
  aesop

@[reassoc (attr := simp)]
lemma mapFiber_isoFiber_inv :
    Subcomplex.mapFiber seq.p seq'.p φ.mor₂ φ.mor₃ (by simp) seq.b seq'.b (by simp) ≫
      seq'.isoFiber.inv = seq.isoFiber.inv ≫ φ.mor₁ := by
  rw [← cancel_mono (seq'.isoFiber.hom), Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← isoFiber_hom_mapFiber,
    Iso.inv_hom_id_assoc]

variable [IsFibrant seq.B] [IsFibrant seq'.B]
noncomputable def δ_naturality_apply {n : ℕ} (x : π (n + 1) seq.B seq.b) :
    seq'.δ n (mapπ φ.mor₃ (n + 1) seq.b seq'.b (by simp) x) =
    mapπ φ.mor₁ n seq.f seq'.f (by simp) (seq.δ n x) := by
  simp [δ, HomotopySequence.δ'_naturality seq.he seq'.he n 0 x _ _ φ.comm_p.symm (by simp),
    mapπ_mapπ]

noncomputable def δ_naturality (n : ℕ) :
    (seq'.δ n).comp (mapπ φ.mor₃ (n + 1) seq.b seq'.b (by simp)) =
      (mapπ φ.mor₁ n seq.f seq'.f (by simp)).comp (seq.δ n) := by
  ext x
  apply δ_naturality_apply


@[simps]
protected def fiber {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) (b : B _⦋0⦌)
    (he : p.app _ e = b) : FibrationSequence where
  f := Subcomplex.fiber.basePoint p he
  e := e
  isPullback := Subcomplex.fiber_isPullback p b

section

variable (X : SSet) [IsFibrant X] (x : X _⦋0⦌)

@[simps]
noncomputable def loop : FibrationSequence where
  F := X.loop x
  E := X.path₀ x
  B := X
  f := X.loopBasePoint x
  e := X.path₀BasePoint x
  b := x
  i := X.loopι x
  p := X.path₀π x
  isPullback := X.isPullback_loop  x

end

end FibrationSequence

end SSet
