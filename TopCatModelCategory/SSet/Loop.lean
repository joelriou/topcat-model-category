module

public import TopCatModelCategory.SSet.Contractible
public import TopCatModelCategory.SSet.HomotopySequence
public import TopCatModelCategory.SSet.Fibrations
public import TopCatModelCategory.SSet.KanComplexWHomotopy
public import TopCatModelCategory.SSet.FundamentalGroupoidPiOne
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section

universe u

open CategoryTheory Monoidal Simplicial MonoidalCategory MonoidalClosed
  SSet.modelCategoryQuillen HomotopicalAlgebra Opposite
  CartesianMonoidalCategory Limits

namespace SSet

namespace stdSimplex

-- by E. Riehl
instance {α : Type*} (β : Type*) [PartialOrder α] [PartialOrder β] [DecidableEq (α → β)] :
    DecidableEq (α →o β) := fun a b =>
  decidable_of_iff (a.toFun = b.toFun) OrderHom.ext_iff.symm

-- by E. Riehl
instance {n m : ℕ} : DecidableEq (⦋n⦌ ⟶ ⦋m⦌) := fun a b =>
  decidable_of_iff (a.toOrderHom = b.toOrderHom) SimplexCategory.Hom.ext_iff.symm

instance {n d : ℕ} : DecidableEq (Δ[n] _⦋d⦌) := fun a b ↦
  decidable_of_iff (objEquiv a = objEquiv b) (by simp)

instance {X : SSet} (d : ℕ) [DecidableEq (X _⦋d⦌)] : DecidableEq (Δ[d] ⟶ X) := fun a b ↦
  decidable_of_iff (yonedaEquiv a = yonedaEquiv b) (by simp)

instance {n m : ℕ} : DecidableEq (Δ[n] ⟶ Δ[m]) := inferInstance

lemma δ_one :
    stdSimplex.δ (1 : Fin 2) = yonedaEquiv.symm (const _ 0 _) := by
  decide

lemma δ_zero :
    stdSimplex.δ (0 : Fin 2) = yonedaEquiv.symm (const _ 1 _) := by
  decide

end stdSimplex

variable (X : SSet.{u})

instance (A : SSet.{u}) (a : A _⦋0⦌) [IsFibrant X] :
    Fibration ((A.ihomEv a).app X) := by
  have : IsSplitMono (yonedaEquiv.symm a) :=
    ⟨⟨{ retraction := stdSimplex.isTerminalObj₀.from _ }⟩⟩
  dsimp [ihomEv]
  infer_instance

abbrev path := (ihom Δ[1]).obj X

noncomputable def pathEv₀ : X.path ⟶ X := (Δ[1].ihomEv (stdSimplex.obj₀Equiv.symm 0)).app X

noncomputable def pathEv₁ : X.path ⟶ X := (Δ[1].ihomEv (stdSimplex.obj₀Equiv.symm 1)).app X

instance [IsFibrant X] : Fibration X.pathEv₀ := by dsimp [pathEv₀]; infer_instance

instance [IsFibrant X] : Fibration X.pathEv₁ := by dsimp [pathEv₁]; infer_instance

noncomputable def pathEv₀₁ : X.path ⟶ X ⊗ X := lift X.pathEv₀ X.pathEv₁

@[simp] lemma pathEv₀₁_fst : X.pathEv₀₁ ≫ fst _ _ = X.pathEv₀ := rfl
@[simp] lemma pathEv₀₁_snd : X.pathEv₀₁ ≫ snd _ _ = X.pathEv₁ := rfl

namespace boundary₁

noncomputable def ihomObjIso : (ihom (∂Δ[1] : SSet.{u})).obj X ≅ X ⊗ X where
  hom := lift ((MonoidalClosed.pre ι₀).app X ≫ stdSimplex.ihom₀.hom.app X)
      ((MonoidalClosed.pre ι₁).app X ≫ stdSimplex.ihom₀.hom.app X)
  inv := curry ((boundary₁.isColimitRightTensor (X ⊗ X)).desc
      (BinaryCofan.mk (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _)))
  hom_inv_id := by
    apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    apply hom_ext_rightTensor
    · rw [← whisker_exchange_assoc, whiskerRight_ι₀_isColimitRightTensor_desc]
      rfl
    · rw [← whisker_exchange_assoc, whiskerRight_ι₁_isColimitRightTensor_desc]
      rfl
  inv_hom_id := by
    ext : 1
    · simp only [comp_lift, lift_fst, Category.id_comp, curry_pre_app_assoc,
        whiskerRight_ι₀_isColimitRightTensor_desc]
      dsimp
      rw [← cancel_mono (stdSimplex.ihom₀.inv.app X), Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id]
      rfl
    · simp only [comp_lift, lift_snd, Category.id_comp, curry_pre_app_assoc,
        whiskerRight_ι₁_isColimitRightTensor_desc]
      dsimp
      rw [← cancel_mono (stdSimplex.ihom₀.inv.app X), Category.assoc, Iso.hom_inv_id_app,
        Category.comp_id]
      rfl

@[reassoc (attr := simp)]
lemma ihomObjIso_hom_fst :
    (ihomObjIso.{u} X).hom ≫ fst _ _ =
      ((MonoidalClosed.pre ι₀).app X ≫ stdSimplex.ihom₀.hom.app X) := rfl

@[reassoc (attr := simp)]
lemma ihomObjIso_hom_snd :
    (ihomObjIso.{u} X).hom ≫ snd _ _ =
      ((MonoidalClosed.pre ι₁).app X ≫ stdSimplex.ihom₀.hom.app X) := rfl

end boundary₁

lemma pre_boundary_ι_app_comp_boundary₁_ihomObjIso :
    (MonoidalClosed.pre ∂Δ[1].ι).app X ≫ (boundary₁.ihomObjIso X).hom = X.pathEv₀₁ := by
  ext : 1
  · dsimp [pathEv₀]
    rw [Category.assoc, boundary₁.ihomObjIso_hom_fst, ← NatTrans.comp_app_assoc,
      ← MonoidalClosed.pre_map, boundary₁.ι₀_ι, stdSimplex.δ_one]
    rfl
  · rw [Category.assoc, boundary₁.ihomObjIso_hom_snd, ← NatTrans.comp_app_assoc,
      ← MonoidalClosed.pre_map, boundary₁.ι₁_ι, stdSimplex.δ_zero]
    rfl

noncomputable def arrowMkPathEv₀₁Iso :
    Arrow.mk X.pathEv₀₁ ≅ Arrow.mk ((MonoidalClosed.pre ∂Δ[1].ι).app X) :=
  Iso.symm (Arrow.isoMk (Iso.refl _) (boundary₁.ihomObjIso X) (by
    simp [pre_boundary_ι_app_comp_boundary₁_ihomObjIso]))

instance [IsFibrant X] : Fibration X.pathEv₀₁ := by
  rw [HomotopicalAlgebra.fibration_iff]
  refine (MorphismProperty.arrow_mk_iso_iff _ X.arrowMkPathEv₀₁Iso).2 ?_
  rw [← HomotopicalAlgebra.fibration_iff]
  infer_instance

noncomputable def pathConst : X ⟶ X.path := curry (snd _ _)

variable (x : X _⦋0⦌)

noncomputable def constPath : X.path _⦋0⦌ := X.pathConst.app _ x

lemma constPath_eq : X.constPath x = ihom₀Equiv.symm (const x) :=
  ihom₀Equiv.injective (by aesop)

@[simp] lemma pathEv₀_app_constPath : X.pathEv₀.app _ (X.constPath x) = x := by
  simp [pathEv₀, constPath_eq, ihomEv_app_app_ihom₀Equiv_symm]

@[simp] lemma pathEv₁_app_constPath : X.pathEv₁.app _ (X.constPath x) = x := by
  simp [pathEv₁, constPath_eq, ihomEv_app_app_ihom₀Equiv_symm]

noncomputable abbrev path₀ : Subcomplex X.path := Subcomplex.fiber X.pathEv₀ x

@[reassoc (attr := simp)]
lemma path₀_ι_pathEv₀ : (X.path₀ x).ι ≫ X.pathEv₀ = const x := by
  simp [path₀]

@[reassoc (attr := simp)]
lemma const_whiskerRight_comp_uncurry_path₀_ι (Z : SSet.{u}) :
    const (X := Z) (stdSimplex.const 1 0 (op ⦋0⦌)) ▷ (X.path₀ x).toSSet ≫
      uncurry (X.path₀ x).ι = const x := by
  wlog hZ : Z = Δ[0]
  · let p : Z ⟶ Δ[0] := stdSimplex.isTerminalObj₀.from Z
    rw [← comp_const p, comp_whiskerRight, Category.assoc, this _ _ _ rfl, comp_const]
  subst hZ
  have := X.path₀_ι_pathEv₀ x
  rw [← cancel_mono (stdSimplex.ihom₀.inv.app _)] at this
  dsimp [pathEv₀, ihomEv] at this
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
    const_comp, yonedaEquiv_symm_zero] at this
  rw [whiskerRight_comp_uncurry, this]
  rfl

def loop : Subcomplex X.path := X.path₀ x ⊓ Subcomplex.fiber X.pathEv₁ x

lemma loop_le_path₀ : X.loop x ≤ X.path₀ x := inf_le_left

lemma constPath_mem_path₀ : X.constPath x ∈ (X.path₀ x).obj _ := by
  simp [Subcomplex.mem_fiber_obj_zero_iff]

lemma constPath_mem_loop : X.constPath x ∈ (X.loop x).obj _ := by
  simp [loop, Subcomplex.mem_fiber_obj_zero_iff]

@[simps]
noncomputable def path₀BasePoint : (X.path₀ x : SSet) _⦋0⦌ :=
  ⟨_, constPath_mem_path₀ _ _⟩

@[simps]
noncomputable def loopBasePoint : (X.loop x : SSet) _⦋0⦌ :=
  ⟨_, constPath_mem_loop _ _⟩

noncomputable abbrev loopι : (X.loop x : SSet) ⟶ X.path₀ x :=
  Subcomplex.homOfLE (X.loop_le_path₀ x)

noncomputable def path₀π : (X.path₀ x : SSet) ⟶ X := Subcomplex.ι _ ≫ X.pathEv₁

@[simp]
lemma loopι_app_loopBasePoint : (X.loopι x).app _ (X.loopBasePoint x) = X.path₀BasePoint x := rfl

@[simp]
lemma path₀π_app_basePoint : (X.path₀π x).app _ (X.path₀BasePoint x) = x := by
  simp [path₀π]

@[reassoc (attr := simp)]
lemma loopι_path₀π : X.loopι x ≫ X.path₀π x = const x := by
  ext n ⟨f, hf⟩
  simp only [loop, Subpresheaf.min_obj, Set.mem_inter_iff,
    Subcomplex.mem_fiber_obj_iff X.pathEv₁] at hf
  tauto

lemma isPullback_path₀ :
    IsPullback (X.path₀ x).ι (X.path₀π x) X.pathEv₀₁
      (lift (const x) (𝟙 _)) := by
  let S := Subcomplex.preimage (Subcomplex.ofSimplex x) (fst X X)
  have S_ι_fst : S.ι ≫ fst _ _ = const x := by
    ext n ⟨⟨y₁, y₂⟩, hy⟩
    dsimp [S] at hy
    rw [Set.mem_preimage, Subcomplex.mem_ofSimplex₀_obj_iff] at hy
    aesop
  have hS : S.preimage X.pathEv₀₁ = X.path₀ x := by aesop
  let e : (S : SSet) ≅ X :=
    { hom := S.ι ≫ snd _ _
      inv := S.lift (lift (const x) (𝟙 X)) (by
        apply le_antisymm (by simp)
        rw [← Subcomplex.image_le_iff, Subcomplex.image_top, ← Subcomplex.image_le_iff,
          ← Subcomplex.range_comp, lift_fst, Subcomplex.le_ofSimplex_iff,
          Subcomplex.range_const_ι]) }
  exact (Subcomplex.preimage_isPullback S X.pathEv₀₁).of_iso
      (Subcomplex.isoOfEq hS) (Iso.refl _) e (Iso.refl _) rfl rfl (by simp)
      (by ext : 1 <;> aesop)

instance [IsFibrant X] : Fibration (X.path₀π x) := by
  rw [HomotopicalAlgebra.fibration_iff]
  exact MorphismProperty.of_isPullback (X.isPullback_path₀ x) (by
    rw [← HomotopicalAlgebra.fibration_iff]
    infer_instance)

lemma loop_eq_fiber : X.loop x = Subcomplex.fiber X.pathEv₀₁ ⟨x, x⟩ := by
  ext ⟨n⟩ y
  simp [loop, Subcomplex.mem_fiber_obj_iff, pathEv₀₁]
  rw [Prod.ext_iff]
  dsimp
  rfl

lemma isPullback_loop' :
    IsPullback (X.loop x).ι (stdSimplex.objZeroIsTerminal.from _)
      (X.pathEv₀₁) (yonedaEquiv.symm ⟨x, x⟩) := by
  rw [loop_eq_fiber]
  convert Subcomplex.fiber_isPullback X.pathEv₀₁ (x, x)

lemma isPullback_loop :
    IsPullback (X.loopι x) (stdSimplex.objZeroIsTerminal.from _)
      (X.path₀π x) (yonedaEquiv.symm x) := by
  rw [← IsPullback.paste_horiz_iff (X.isPullback_path₀ x)]
  · convert X.isPullback_loop' x
    aesop
  · simp

instance [IsFibrant X] : IsFibrant (X.loop x : SSet) := by
  rw [isFibrant_iff_of_isTerminal (stdSimplex.objZeroIsTerminal.from _)
    stdSimplex.objZeroIsTerminal, HomotopicalAlgebra.fibration_iff]
  exact MorphismProperty.of_isPullback (X.isPullback_loop x) (by
    rw [← HomotopicalAlgebra.fibration_iff]
    infer_instance)

namespace stdSimplex

@[simps]
def hDelta₁OrderHom : Fin 2 × Fin 2 →o Fin 2 :=
  ⟨fun ⟨x, y⟩ ↦ match x, y with
    | 0, 0 => 0
    | 0, 1 => 0
    | 1, 0 => 0
    | 1, 1 => 1, by
    rw [monotone_prod_iff]
    constructor
    all_goals
    · intro i j k _
      fin_cases i <;> fin_cases j <;> fin_cases k <;> aesop⟩

def hDelta₁ : Δ[1] ⊗ Δ[1] ⟶ Δ[1] :=
  prodStdSimplex.homEquiv.symm hDelta₁OrderHom

@[reassoc (attr := simp)]
lemma whiskerLeft_δ_zero_comp_hDelta₁ :
    _ ◁ stdSimplex.δ 0 ≫ hDelta₁ = (stdSimplex.rightUnitor _).hom := by
  rw [← cancel_epi (stdSimplex.rightUnitor _).inv, Iso.inv_hom_id]
  apply yonedaEquiv.injective
  ext i
  fin_cases i <;> rfl

@[reassoc (attr := simp)]
lemma whiskerLeft_δ_one_comp_hDelta₁ :
    _ ◁ stdSimplex.δ 1 ≫ hDelta₁ = SSet.const (stdSimplex.obj₀Equiv.symm 0) := by
  rw [← cancel_epi (stdSimplex.rightUnitor _).inv]
  apply yonedaEquiv.injective
  ext i
  fin_cases i <;> rfl

@[reassoc (attr := simp)]
lemma const_zero_whiskerRight_comp_hDelta₁ :
    SSet.const (X := X) (stdSimplex.const 1 0 (op ⦋0⦌)) ▷ Δ[1] ≫ stdSimplex.hDelta₁ =
    SSet.const (stdSimplex.const 1 0 (op ⦋0⦌)) := by
  wlog hX : X = Δ[0]
  · exact isTerminalObj₀.from X ▷ Δ[1] ≫= this _ rfl
  subst hX
  rw [← cancel_epi (stdSimplex.leftUnitor _).inv]
  apply yonedaEquiv.injective
  ext i
  fin_cases i <;> rfl

end stdSimplex

noncomputable def pathHomotopy :
    Homotopy (X.pathEv₀ ≫ X.pathConst) (𝟙 X.path) where
  h := (β_ _ _).hom ≫ curry ((α_ _ _ _).inv ≫ uncurry
    ((MonoidalClosed.pre stdSimplex.hDelta₁).app X))
  h₀ := by
    rw [MonoidalClosed.uncurry_pre, Subcomplex.RelativeMorphism.botEquiv_symm_apply_map,
      ← cancel_epi (stdSimplex.rightUnitor _).hom, stdSimplex.rightUnitor_hom_ι₀_assoc,
      BraidedCategory.braiding_naturality_right_assoc,
      ← curry_natural_left, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, stdSimplex.whiskerLeft_δ_one_comp_hDelta₁,
      ← curry_natural_left]
    dsimp only [pathConst]
    rw [← curry_natural_left]
    rfl
  h₁ := by
    rw [MonoidalClosed.uncurry_pre, Subcomplex.RelativeMorphism.botEquiv_symm_apply_map,
      ← cancel_epi (stdSimplex.rightUnitor _).hom, stdSimplex.rightUnitor_hom_ι₁_assoc,
      BraidedCategory.braiding_naturality_right_assoc, Category.comp_id,
      ← curry_natural_left, associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, stdSimplex.whiskerLeft_δ_zero_comp_hDelta₁]
    apply uncurry_injective
    rfl

@[reassoc (attr := simp)]
lemma path₀_ι_whiskerLeft_pathHomotopy_h_pathEv₀ :
    (X.path₀ x).ι ▷ Δ[1] ≫ X.pathHomotopy.h ≫ X.pathEv₀ = const x := by
  dsimp only [pathHomotopy, pathEv₀, ihomEv, NatTrans.comp_app]
  rw [Category.assoc, MonoidalClosed.uncurry_pre,
    BraidedCategory.braiding_naturality_left_assoc,
    ← cancel_epi (β_ _ _).inv, Iso.inv_hom_id_assoc, comp_const,
    curry_pre_app_assoc, ← curry_natural_left_assoc,
    whiskerRight_tensor_assoc, Iso.hom_inv_id_assoc,
    ← comp_whiskerRight_assoc, stdSimplex.obj₀Equiv_symm_apply,
    yonedaEquiv_symm_zero, stdSimplex.const_zero_whiskerRight_comp_hDelta₁,
    associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    ← uncurry_id_eq_ev, ← uncurry_natural_left, Category.comp_id,
    const_whiskerRight_comp_uncurry_path₀_ι, comp_const]
  rfl

noncomputable def contractiblePath₀ : Contractible (X.path₀ x) where
  pt := X.path₀BasePoint x
  h := { h := Subcomplex.lift ((X.path₀ x).ι ▷ _ ≫ X.pathHomotopy.h) (by simp) }

instance : IsContractible (X.path₀ x) := ⟨X.contractiblePath₀ x⟩

end SSet
