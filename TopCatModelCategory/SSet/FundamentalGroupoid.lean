import TopCatModelCategory.CommSq
import TopCatModelCategory.IsFibrant
import TopCatModelCategory.SSet.Square
import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.HomotopyBasic
import TopCatModelCategory.SSet.AnodyneExtensionsDefs
import TopCatModelCategory.SSet.Monoidal

universe u

open HomotopicalAlgebra CategoryTheory Category Simplicial Limits MonoidalCategory
  ChosenFiniteProducts SSet.modelCategoryQuillen

namespace SSet

variable {X : SSet.{u}}

namespace boundary₁

lemma sq : Subcomplex.Sq ⊥ (stdSimplex.face {0}) (stdSimplex.face {1})
    (boundary.{u} 1) where
  max_eq := by
    rw [boundary_eq_iSup]
    ext
    rw [Subpresheaf.max_obj, Set.mem_union, Subpresheaf.iSup_obj,
      Set.mem_iUnion]
    constructor
    · rintro (h₀ | h₁)
      · exact ⟨1, h₀⟩
      · exact ⟨0, h₁⟩
    · rintro ⟨i, h⟩
      fin_cases i
      · exact Or.inr h
      · exact Or.inl h
  min_eq := by
    ext ⟨m⟩ x
    induction' m using SimplexCategory.rec with m
    aesop

noncomputable def ι₀ : Δ[0] ⟶ (boundary 1 : SSet.{u}) :=
  (stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} ({1}ᶜ : Finset (Fin 2)) 0
    (Fin.orderIsoSingleton 0))).hom ≫
    Subcomplex.homOfLE (face_le_boundary (1 : Fin 2))

noncomputable def ι₁ : Δ[0] ⟶ (boundary 1 : SSet.{u}) :=
  (stdSimplex.isoOfRepresentableBy
    (stdSimplex.faceRepresentableBy.{u} ({0}ᶜ : Finset (Fin 2)) 0
    (Fin.orderIsoSingleton 1))).hom ≫
    Subcomplex.homOfLE (face_le_boundary (0 : Fin 2))

@[reassoc (attr := simp)]
lemma ι₀_ι : ι₀.{u} ≫ (boundary 1).ι = stdSimplex.δ 1 := by
  apply yonedaEquiv.injective
  ext i
  fin_cases i
  rfl

@[reassoc (attr := simp)]
lemma ι₁_ι : ι₁.{u} ≫ (boundary 1).ι = stdSimplex.δ 0 := by
  apply yonedaEquiv.injective
  ext i
  fin_cases i
  rfl

lemma ι₀_eq_ι_one : ι₀.{u} = boundary.ι 1 := by
  rw [← cancel_mono (Subcomplex.ι _)]
  apply yonedaEquiv.injective
  ext i
  fin_cases i
  rfl

lemma ι₁_eq_ι_zero : ι₁.{u} = boundary.ι 0 := by
  rw [← cancel_mono (Subcomplex.ι _)]
  apply yonedaEquiv.injective
  ext i
  fin_cases i
  rfl

lemma isPushout : IsPushout (initial.to _) (initial.to _) ι₀.{u} ι₁.{u} :=
  sq.{u}.isPushout.of_iso' (initialIsoIsInitial (Subcomplex.isInitialBot _))
    (stdSimplex.isoOfRepresentableBy
      (stdSimplex.faceRepresentableBy.{u} ({1}ᶜ : Finset (Fin 2)) 0
      (Fin.orderIsoSingleton 0)))
    (stdSimplex.isoOfRepresentableBy
      (stdSimplex.faceRepresentableBy.{u} ({0}ᶜ : Finset (Fin 2)) 0
      (Fin.orderIsoSingleton 1))) (Iso.refl _)
    (initialIsInitial.hom_ext _ _) (initialIsInitial.hom_ext _ _)
    (by simp [ι₀]) (by simp [ι₁])

noncomputable def isColimit : IsColimit (BinaryCofan.mk ι₀.{u} ι₁) :=
  isPushout.{u}.isColimitBinaryCofan initialIsInitial

@[ext]
lemma hom_ext {f g : (boundary 1 : SSet) ⟶ X}
    (h₀ : ι₀ ≫ f = ι₀ ≫ g) (h₁ : ι₁ ≫ f = ι₁ ≫ g) : f = g := by
  apply BinaryCofan.IsColimit.hom_ext isColimit <;> assumption

noncomputable def desc (x₀ x₁ : X _⦋0⦌) : (boundary 1 : SSet) ⟶ X :=
  (BinaryCofan.IsColimit.desc' isColimit (yonedaEquiv.symm x₀)
    (yonedaEquiv.symm x₁)).1

@[reassoc (attr := simp)]
lemma ι₀_desc (x₀ x₁ : X _⦋0⦌) : ι₀ ≫ desc x₀ x₁ = yonedaEquiv.symm x₀ :=
  (BinaryCofan.IsColimit.desc' isColimit _ _).2.1

@[reassoc (attr := simp)]
lemma ι₁_desc (x₀ x₁ : X _⦋0⦌) : ι₁ ≫ desc x₀ x₁ = yonedaEquiv.symm x₁ :=
  (BinaryCofan.IsColimit.desc' isColimit _ _).2.2

noncomputable def isColimitRightTensor (X : SSet.{u}) :
    IsColimit (BinaryCofan.mk (ι₀ ▷ X) (ι₁ ▷ X)) :=
  mapIsColimitOfPreservesOfIsColimit (tensorRight X) _ _ isColimit

@[reassoc (attr := simp)]
lemma whiskerRight_ι₀_isColimitRightTensor_desc
    {X : SSet.{u}} (c : BinaryCofan (Δ[0] ⊗ X) (Δ[0] ⊗ X)) :
    ι₀ ▷ X ≫ (isColimitRightTensor X).desc c = c.inl :=
  (isColimitRightTensor X).fac c (.mk .left)

@[reassoc (attr := simp)]
lemma whiskerRight_ι₁_isColimitRightTensor_desc
    {X : SSet.{u}} (c : BinaryCofan (Δ[0] ⊗ X) (Δ[0] ⊗ X)) :
    ι₁ ▷ X ≫ (isColimitRightTensor X).desc c = c.inr :=
  (isColimitRightTensor X).fac c (.mk .right)

noncomputable def isColimitLeftTensor (X : SSet.{u}) :
    IsColimit (BinaryCofan.mk (X ◁ ι₀) (X ◁ ι₁)) :=
  mapIsColimitOfPreservesOfIsColimit (tensorLeft X) _ _ isColimit

lemma hom_ext_rightTensor {X Y : SSet.{u}} {f g : (boundary 1 : SSet) ⊗ X ⟶ Y}
    (h₀ : ι₀ ▷ X ≫ f = ι₀ ▷ X ≫ g) (h₁ : ι₁ ▷ X ≫ f = ι₁ ▷ X ≫ g) :
    f = g := by
  apply BinaryCofan.IsColimit.hom_ext (isColimitRightTensor X) <;> assumption

lemma hom_ext_leftTensor {X Y : SSet.{u}} {f g : X ⊗ (boundary 1 : SSet) ⟶ Y}
    (h₀ : X ◁ ι₀ ≫ f = X ◁ ι₀ ≫ g) (h₁ : X ◁ ι₁ ≫ f = X ◁ ι₁≫ g) :
    f = g := by
  apply BinaryCofan.IsColimit.hom_ext (isColimitLeftTensor X) <;> assumption

end boundary₁

namespace KanComplex

variable (X)

structure FundamentalGroupoid where
  pt : X _⦋0⦌

namespace FundamentalGroupoid

variable {X}

@[simps apply]
def objEquiv : FundamentalGroupoid X ≃ X _⦋0⦌ where
  toFun x := x.pt
  invFun x := { pt := x}
  left_inv _ := rfl
  right_inv _ := rfl

@[simps! pt]
def map {Y : SSet.{u}} (f : X ⟶ Y) (x : FundamentalGroupoid X) :
    FundamentalGroupoid Y :=
  objEquiv.symm (f.app _ (objEquiv x))

def Hom (x₀ x₁ : FundamentalGroupoid X) :=
  Subcomplex.RelativeMorphism.HomotopyClass.{u} _ _
    (boundary₁.desc x₀.pt x₁.pt ≫ (Subcomplex.topIso X).inv)

abbrev Edge (x₀ x₁ : FundamentalGroupoid X) :=
  Subcomplex.RelativeMorphism.{u} _ _
    (boundary₁.desc x₀.pt x₁.pt ≫ (Subcomplex.topIso X).inv)

@[ext]
lemma Edge.ext {x₀ x₁ : FundamentalGroupoid X} {p q : Edge x₀ x₁}
    (h : p.map = q.map) :
    p = q :=
  Subcomplex.RelativeMorphism.ext h

@[simps]
def Edge.mk {x₀ x₁ : FundamentalGroupoid X} (f : Δ[1] ⟶ X)
    (h₀ : stdSimplex.δ 1 ≫ f = const x₀.pt := by simp)
    (h₁ : stdSimplex.δ 0 ≫ f = const x₁.pt := by simp) :
    Edge x₀ x₁ where
  map := f
  comm := by
    apply boundary₁.hom_ext
    · dsimp
      rw [assoc, boundary₁.ι₀_desc_assoc, yonedaEquiv_symm_zero, const_comp,
        boundary₁.ι₀_ι_assoc, h₀, FunctorToTypes.comp,
        Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe]
    · dsimp
      rw [assoc, boundary₁.ι₁_desc_assoc, yonedaEquiv_symm_zero, const_comp,
        boundary₁.ι₁_ι_assoc, h₁, FunctorToTypes.comp,
        Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe]

def Edge.ofEq {x₀ x₁ : FundamentalGroupoid X} (h : x₀ = x₁) :
    Edge x₀ x₁ :=
  Edge.mk (const x₀.pt) rfl (by rw [h]; rfl)

@[reassoc]
lemma Edge.comm₀ {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    stdSimplex.δ 1 ≫ p.map = const x₀.pt := by
  have := boundary₁.ι₀ ≫= p.comm
  rw [assoc, boundary₁.ι₀_ι_assoc, boundary₁.ι₀_desc_assoc,
    yonedaEquiv_symm_zero, const_comp, FunctorToTypes.comp, Subpresheaf.ι_app,
    Subcomplex.topIso_inv_app_coe] at this
  exact this

lemma Edge.comm₀' {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    p.map.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = x₀.pt := by
  convert congr_arg yonedaEquiv p.comm₀ using 1
  · dsimp [CosimplicialObject.δ]
    rw [yonedaEquiv_map_comp, stdSimplex.map_yonedaEquiv]
    apply congr_arg
    ext i
    fin_cases i
    rfl
  · simp

@[reassoc]
lemma Edge.comm₀'' {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    (stdSimplex.face {(0 : Fin 2)}).ι ≫ p.map = const x₀.pt := by
  rw [← cancel_epi (stdSimplex.faceSingletonIso (0 : Fin 2)).hom, comp_const]
  rw [stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ_assoc]
  exact p.comm₀

@[reassoc]
lemma Edge.comm₁ {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    stdSimplex.δ 0 ≫ p.map = const x₁.pt := by
  have := boundary₁.ι₁ ≫= p.comm
  rw [assoc, boundary₁.ι₁_ι_assoc, boundary₁.ι₁_desc_assoc,
    yonedaEquiv_symm_zero, const_comp, FunctorToTypes.comp, Subpresheaf.ι_app,
    Subcomplex.topIso_inv_app_coe] at this
  exact this

lemma Edge.comm₁' {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    p.map.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = x₁.pt := by
  convert congr_arg yonedaEquiv p.comm₁ using 1
  · dsimp [CosimplicialObject.δ]
    rw [yonedaEquiv_map_comp, stdSimplex.map_yonedaEquiv]
    apply congr_arg
    ext i
    fin_cases i
    rfl
  · simp

@[reassoc]
lemma Edge.comm₁'' {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    (stdSimplex.face {(1 : Fin 2)}).ι ≫ p.map = const x₁.pt := by
  rw [← cancel_epi (stdSimplex.faceSingletonIso (1 : Fin 2)).hom, comp_const]
  rw [stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ_assoc]
  exact p.comm₁

@[simps! map]
def Edge.id (x : FundamentalGroupoid X) : Edge x x :=
  Edge.mk (const x.pt)

@[simp]
lemma Edge.ofEq_refl (x : FundamentalGroupoid X) :
    Edge.ofEq (rfl : x = x) = Edge.id x := rfl

namespace Edge

section

variable {x₀ x₁ : FundamentalGroupoid X}

@[simps! map]
def pushforward (p : Edge x₀ x₁) {Y : SSet.{u}} (f : X ⟶ Y) :
    Edge (x₀.map f) (x₁.map f) :=
  Edge.mk (p.map ≫ f) (by simp [p.comm₀_assoc])
    (by simp [p.comm₁_assoc])

@[simp]
lemma id_pushforward (x : FundamentalGroupoid X) {Y : SSet.{u}} (f : X ⟶ Y) :
    (Edge.id x).pushforward f = Edge.id (map f x) := by
  aesop

@[simp]
lemma pushforward_id (p : Edge x₀ x₁) :
    p.pushforward (𝟙 X) = p := by
  aesop

@[simp]
lemma pushforward_comp (p : Edge x₀ x₁) {Y Z : SSet.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    p.pushforward (f ≫ g) = (p.pushforward f).pushforward g := by
  aesop

variable (p q : Edge x₀ x₁)

nonrec abbrev Homotopy := p.Homotopy q

namespace Homotopy

variable {p q} (h : p.Homotopy q)

@[reassoc (attr := simp)]
lemma comm₀ : ι₀ ≫ (β_ _ _).hom ≫ h.h = const x₀.pt := by
  have := boundary₁.ι₀ ▷ Δ[1] ≫= h.rel
  rw [assoc, whiskerRight_fst_assoc, boundary₁.ι₀_desc_assoc,
    yonedaEquiv_symm_zero, const_comp, comp_const, FunctorToTypes.comp, Subpresheaf.ι_app,
    Subcomplex.topIso_inv_app_coe, ← comp_whiskerRight_assoc, boundary₁.ι₀_ι,
    ← cancel_epi (stdSimplex.leftUnitor _).inv,
    stdSimplex.leftUnitor_inv_map_δ_one_assoc, comp_const] at this
  exact this

@[reassoc (attr := simp)]
lemma comm₁ : ι₁ ≫ (β_ _ _).hom ≫ h.h = const x₁.pt := by
  have := boundary₁.ι₁ ▷ Δ[1] ≫= h.rel
  rw [assoc, whiskerRight_fst_assoc, boundary₁.ι₁_desc_assoc,
    yonedaEquiv_symm_zero, const_comp, comp_const, FunctorToTypes.comp, Subpresheaf.ι_app,
    Subcomplex.topIso_inv_app_coe, ← comp_whiskerRight_assoc, boundary₁.ι₁_ι,
    ← cancel_epi (stdSimplex.leftUnitor _).inv,
    stdSimplex.leftUnitor_inv_map_δ_zero_assoc, comp_const] at this
  exact this

@[simps]
noncomputable def map {Y : SSet.{u}} (f : X ⟶ Y) :
    (p.pushforward f).Homotopy (q.pushforward f) where
  h := h.h ≫ f
  rel := by
    rw [h.rel_assoc]
    congr 1
    apply boundary₁.hom_ext
    · dsimp
      rw [assoc, assoc, boundary₁.ι₀_desc_assoc,
        boundary₁.ι₀_desc_assoc]
      apply yonedaEquiv.injective
      simp
    · dsimp
      rw [assoc, assoc, boundary₁.ι₁_desc_assoc,
        boundary₁.ι₁_desc_assoc]
      apply yonedaEquiv.injective
      simp

end Homotopy

end

variable {x₀ x₁ x₂ x₃ : FundamentalGroupoid X}

structure CompStruct (p₀₁ : Edge x₀ x₁) (p₁₂ : Edge x₁ x₂) (p₀₂ : Edge x₀ x₂) where
  map : Δ[2] ⟶ X
  h₀₁ : stdSimplex.δ 2 ≫ map = p₀₁.map := by aesop_cat
  h₁₂ : stdSimplex.δ 0 ≫ map = p₁₂.map := by aesop_cat
  h₀₂ : stdSimplex.δ 1 ≫ map = p₀₂.map := by aesop_cat

namespace CompStruct

attribute [reassoc (attr := simp)] h₀₁ h₁₂ h₀₂

@[simps]
def pushforward {p₀₁ : Edge x₀ x₁} {p₁₂ : Edge x₁ x₂} {p₀₂ : Edge x₀ x₂}
    (h : CompStruct p₀₁ p₁₂ p₀₂)
    {Y : SSet.{u}} (f : X ⟶ Y) :
    CompStruct (p₀₁.pushforward f) (p₁₂.pushforward f) (p₀₂.pushforward f) where
  map := h.map ≫ f

def idComp (p : Edge x₀ x₁) : CompStruct (Edge.id x₀) p p where
  map := stdSimplex.σ 0 ≫ p.map
  h₀₁ := by
    have := stdSimplex.{u}.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by simp)
    dsimp at this
    rw [reassoc_of% this, p.comm₀, comp_const, id_map]
  h₁₂ := stdSimplex.{u}.δ_comp_σ_self_assoc (n := 1) (i := 0) _
  h₀₂ := stdSimplex.{u}.δ_comp_σ_succ_assoc (n := 1) (i := 0) _

def compId (p : Edge x₀ x₁) : CompStruct p (Edge.id x₁) p where
  map := stdSimplex.σ 1 ≫ p.map
  h₀₁ := stdSimplex.δ_comp_σ_succ_assoc (n := 1) (i := 1) _
  h₁₂ := by
    have := stdSimplex.{u}.δ_comp_σ_of_le (n := 0) (i := 0) (j := 0) (by simp)
    dsimp at this
    rw [reassoc_of% this, p.comm₁, comp_const, id_map]
  h₀₂ := stdSimplex.δ_comp_σ_self_assoc (n := 1) (i := 1) _

variable [IsFibrant X]

lemma left_inverse (p : Edge x₀ x₁) :
    ∃ (q : Edge x₁ x₀), Nonempty (CompStruct q p (Edge.id x₁)) := by
  obtain ⟨α, h₀₂, h₁₂⟩ := horn₂₂.isPushout.exists_desc (const x₁.pt) p.map
    (by rw [p.comm₁, comp_const])
  obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
    (anodyneExtensions.horn_ι_mem 1 2)
  have h₀₂' := horn₂₂.ι₀₂ ≫= hβ
  rw [horn.ι_ι_assoc, h₀₂] at h₀₂'
  have h₁₂' := horn₂₂.ι₁₂ ≫= hβ
  rw [horn.ι_ι_assoc, h₁₂] at h₁₂'
  refine ⟨Edge.mk (stdSimplex.δ 2 ≫ β) ?_ ?_,
    ⟨{ map := β, h₀₁ := rfl, h₁₂ := h₁₂', h₀₂ := h₀₂' }⟩⟩
  · have := stdSimplex.{u}.δ_comp_δ_self (n := 0) (i := 1)
    dsimp at this
    rw [← reassoc_of% this, h₀₂', comp_const]
  · have := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 0) (j := 1) (by simp)
    dsimp at this
    rw [reassoc_of% this, h₁₂', p.comm₀]

lemma right_inverse (p : Edge x₀ x₁) :
    ∃ (q : Edge x₁ x₀), Nonempty (CompStruct p q (Edge.id x₀)) := by
  obtain ⟨α, h₀₁, h₁₂⟩ := horn₂₀.isPushout.exists_desc p.map (const x₀.pt)
    (by rw [p.comm₀, comp_const])
  obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
    (anodyneExtensions.horn_ι_mem 1 0)
  have h₀₁' := horn₂₀.ι₀₁ ≫= hβ
  rw [horn.ι_ι_assoc, h₀₁] at h₀₁'
  have h₀₂' := horn₂₀.ι₀₂ ≫= hβ
  rw [horn.ι_ι_assoc, h₁₂] at h₀₂'
  refine ⟨Edge.mk (stdSimplex.δ 0 ≫ β) ?_ ?_,
    ⟨{ map := β, h₀₁ := h₀₁', h₁₂ := rfl, h₀₂ := h₀₂' }⟩⟩
  · have := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 0) (j := 1) (by simp)
    dsimp at this
    rw [← reassoc_of% this, h₀₁', p.comm₁]
  · have := stdSimplex.{u}.δ_comp_δ_self (n := 0) (i := 0)
    dsimp at this
    rw [reassoc_of% this, h₀₂', comp_const]

noncomputable def assoc {f₀₁ : Edge x₀ x₁} {f₁₂ : Edge x₁ x₂} {f₂₃ : Edge x₂ x₃}
    {f₀₂ : Edge x₀ x₂} {f₁₃ : Edge x₁ x₃} {f₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct f₀₁ f₁₂ f₀₂)
    (h₁₃ : CompStruct f₁₂ f₂₃ f₁₃)
    (h : CompStruct f₀₁ f₁₃ f₀₃) :
    CompStruct f₀₂ f₂₃ f₀₃ := by
  apply Nonempty.some
  obtain ⟨α, hα₁, hα₂, hα₃⟩ :=
    horn₃₁.exists_desc h₁₃.map h.map h₀₂.map (by simp) (by simp) (by simp)
  obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
    (anodyneExtensions.horn_ι_mem 2 1)
  exact ⟨{
    map := stdSimplex.δ 1 ≫ β
    h₀₁ := by
      have := stdSimplex.{u}.δ_comp_δ (n := 1) (i := 1) (j := 2) (by simp)
      dsimp at this
      rw [← h₀₂.h₀₂, ← hα₃, ← hβ, horn.ι_ι_assoc, reassoc_of% this]
    h₁₂ := by
      have := stdSimplex.{u}.δ_comp_δ_self (n := 1) (i := 0)
      dsimp at this
      rw [← h₁₃.h₁₂, ← hα₁, ← hβ, horn.ι_ι_assoc, reassoc_of% this]
    h₀₂ :=  by
      have := stdSimplex.{u}.δ_comp_δ_self (n := 1) (i := 1)
      dsimp at this
      rw [← h.h₀₂, ← hα₂, ← hβ, horn.ι_ι_assoc, reassoc_of% this] }⟩

noncomputable def assoc' {f₀₁ : Edge x₀ x₁} {f₁₂ : Edge x₁ x₂} {f₂₃ : Edge x₂ x₃}
    {f₀₂ : Edge x₀ x₂} {f₁₃ : Edge x₁ x₃} {f₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct f₀₁ f₁₂ f₀₂)
    (h₁₃ : CompStruct f₁₂ f₂₃ f₁₃)
    (h : CompStruct f₀₂ f₂₃ f₀₃) :
    CompStruct f₀₁ f₁₃ f₀₃ := by
  apply Nonempty.some
  obtain ⟨α, hα₁, hα₂, hα₃⟩ :=
    horn₃₂.exists_desc h₁₃.map h.map h₀₂.map (by simp) (by simp) (by simp)
  obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
    (anodyneExtensions.horn_ι_mem 2 2)
  exact ⟨{
    map := stdSimplex.δ 2 ≫ β
    h₀₁ := by
      have := stdSimplex.{u}.δ_comp_δ (n := 1) (i := 2) (j := 2) (by simp)
      dsimp at this
      rw [← h₀₂.h₀₁, ← hα₃, ← hβ, horn.ι_ι_assoc, reassoc_of% this]
    h₁₂ := by
      have := stdSimplex.{u}.δ_comp_δ (n := 1) (i := 0) (j := 1) (by simp)
      dsimp at this
      rw [← h₁₃.h₀₂, ← hα₁, ← hβ, horn.ι_ι_assoc, reassoc_of% this]
    h₀₂ :=  by
      have := stdSimplex.{u}.δ_comp_δ_self (n := 1) (i := 1)
      dsimp at this
      rw [← h.h₀₂, ← hα₂, ← hβ, horn.ι_ι_assoc, reassoc_of% this] }⟩

end CompStruct

lemma exists_compStruct [IsFibrant X] (p₀₁ : Edge x₀ x₁) (p₁₂ : Edge x₁ x₂) :
    ∃ (p₀₂ : Edge x₀ x₂), Nonempty (CompStruct p₀₁ p₁₂ p₀₂) := by
  obtain ⟨α, h₀₁, h₁₂⟩ := horn₂₁.isPushout.exists_desc p₀₁.map p₁₂.map (by
    have h₀ := boundary₁.ι₁ ≫= p₀₁.comm
    have h₁ := boundary₁.ι₀ ≫= p₁₂.comm
    rw [assoc, boundary₁.ι₁_ι_assoc,
      boundary₁.ι₁_desc_assoc] at h₀
    rw [assoc, boundary₁.ι₀_ι_assoc,
      boundary₁.ι₀_desc_assoc] at h₁
    rw [h₀, h₁])
  obtain ⟨β, hβ⟩ := anodyneExtensions.exists_lift_of_isFibrant α
    (anodyneExtensions.horn_ι_mem 1 1)
  have h₀₁' := horn₂₁.ι₀₁ ≫= hβ
  rw [horn.ι_ι_assoc, h₀₁] at h₀₁'
  have h₁₂' := horn₂₁.ι₁₂ ≫= hβ
  rw [horn.ι_ι_assoc, h₁₂] at h₁₂'
  refine ⟨Edge.mk (stdSimplex.δ 1 ≫ β) ?_ ?_,
    ⟨{ map := β, h₀₁ := h₀₁', h₁₂ := h₁₂', h₀₂ := rfl }⟩⟩
  · have := stdSimplex.{u}.δ_comp_δ_self (n := 0) (i := 1)
    dsimp at this
    rw [reassoc_of% this, h₀₁', p₀₁.comm₀]
  · have := stdSimplex.{u}.δ_comp_δ (n := 0) (i := 0) (j := 0) (by simp)
    dsimp at this
    rw [reassoc_of% this, h₁₂', p₁₂.comm₁]

def HomotopyL (p q : Edge x₀ x₁) := CompStruct p (Edge.id x₁) q
def HomotopyR (p q : Edge x₀ x₁) := CompStruct (Edge.id x₀) p q

section

variable (p q r : Edge x₀ x₁)

def HomotopyL.refl : HomotopyL p p := CompStruct.compId p
def HomotopyR.refl : HomotopyR p p := CompStruct.idComp p

variable {p q r} [IsFibrant X]

noncomputable def HomotopyL.symm (h : HomotopyL p q) : HomotopyL q p :=
  CompStruct.assoc h (CompStruct.compId _) (CompStruct.compId p)

noncomputable def HomotopyR.symm (h : HomotopyR p q) : HomotopyR q p :=
  CompStruct.assoc' (CompStruct.idComp _) h (CompStruct.idComp p)

noncomputable def HomotopyL.homotopyR (h : HomotopyL p q) : HomotopyR p q :=
  HomotopyR.symm (CompStruct.assoc' (CompStruct.idComp p) h (CompStruct.compId p))

noncomputable def HomotopyR.homotopyL (h : HomotopyR p q) : HomotopyL p q :=
  HomotopyL.symm (CompStruct.assoc h (CompStruct.compId p) (CompStruct.idComp p))

noncomputable def HomotopyL.trans (h : HomotopyL p q) (h' : HomotopyL q r) :
    HomotopyL p r :=
  CompStruct.assoc (CompStruct.idComp p) h h'.homotopyR

noncomputable def HomotopyR.trans (h : HomotopyR p q) (h' : HomotopyR q r) :
    HomotopyR p r :=
  CompStruct.assoc' h (CompStruct.compId p) h'.homotopyL

end

namespace CompStruct

variable [IsFibrant X]

noncomputable def unique {p₀₁ : Edge x₀ x₁} {p₁₂ : Edge x₁ x₂} {p₀₂ : Edge x₀ x₂}
    (h : CompStruct p₀₁ p₁₂ p₀₂)
    {p₀₁' : Edge x₀ x₁} {p₁₂' : Edge x₁ x₂} {p₀₂' : Edge x₀ x₂}
    (h' : CompStruct p₀₁' p₁₂' p₀₂')
    (h₀₁ : HomotopyL p₀₁ p₀₁') (h₁₂ : HomotopyL p₁₂ p₁₂') :
    HomotopyL p₀₂ p₀₂' :=
  assoc h (compId p₁₂) (assoc (compId p₀₁) h₁₂.homotopyR (assoc' h₀₁ (idComp p₁₂') h'))

end CompStruct

namespace Homotopy

variable {p q : Edge x₀ x₁} (h : Homotopy p q)

lemma h_app_zero_of_fst_zero (x : Δ[1] _⦋0⦌) :
    h.h.app _ (⟨stdSimplex.obj₀Equiv.symm 0, x⟩) = x₀.pt := by
  have := (stdSimplex.leftUnitor _).inv ≫= boundary₁.ι₀ ▷ _ ≫= h.rel
  rw [Category.assoc, ChosenFiniteProducts.whiskerRight_fst_assoc,
    boundary₁.ι₀_desc_assoc, yonedaEquiv_symm_zero, const_comp,
    FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe,
    comp_const, comp_const, ← comp_whiskerRight_assoc,
    boundary₁.ι₀_ι, stdSimplex.leftUnitor_inv_map_δ_one_assoc] at this
  replace this := congr_fun (NatTrans.congr_app this _) x
  dsimp at this
  rw [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply] at this
  exact this

lemma h_app_zero_of_fst_one (x : Δ[1] _⦋0⦌) :
    h.h.app _ (⟨stdSimplex.obj₀Equiv.symm 1, x⟩) = x₁.pt := by
  have := (stdSimplex.leftUnitor _).inv ≫= boundary₁.ι₁ ▷ _ ≫= h.rel
  rw [Category.assoc, ChosenFiniteProducts.whiskerRight_fst_assoc,
    boundary₁.ι₁_desc_assoc, yonedaEquiv_symm_zero, const_comp,
    FunctorToTypes.comp, Subpresheaf.ι_app, Subcomplex.topIso_inv_app_coe,
    comp_const, comp_const, ← comp_whiskerRight_assoc,
    boundary₁.ι₁_ι, stdSimplex.leftUnitor_inv_map_δ_zero_assoc] at this
  replace this := congr_fun (NatTrans.congr_app this _) x
  dsimp at this
  rw [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply] at this
  exact this

@[simp]
lemma h_app_obj₀Equiv_zero :
    h.h.app _ (prodStdSimplex.obj₀Equiv.symm 0) = x₀.pt := by
  apply h_app_zero_of_fst_zero

@[simp]
lemma h_app_obj₀Equiv_one :
    h.h.app _ (prodStdSimplex.obj₀Equiv.symm 1) = x₁.pt := by
  apply h_app_zero_of_fst_one

noncomputable abbrev diagonal : Edge x₀ x₁ :=
  Edge.mk (square.diagonal ≫ h.h) (by simp) (by simp)

noncomputable def homotopyLDiagonal : HomotopyL p h.diagonal where
  map := square.ιTriangle₀ ≫ h.h
  h₀₁ := by rw [← h.h₀, square.δ₂_ιTriangle₀_assoc]

noncomputable def homotopyRDiagonal : HomotopyR q h.diagonal where
  map := square.ιTriangle₁ ≫ h.h

noncomputable def homotopyL [IsFibrant X] : HomotopyL p q :=
  h.homotopyLDiagonal.trans h.homotopyRDiagonal.homotopyL.symm

noncomputable def homotopyR [IsFibrant X] : HomotopyR p q :=
  h.homotopyL.homotopyR

end Homotopy

variable [IsFibrant X]

section

variable {p q : Edge x₀ x₁}

noncomputable def HomotopyL.homotopy (h : p.HomotopyL q) : Homotopy p q where
  h := square.isPushout.desc h.map
      (stdSimplex.σ 0 ≫ q.map) (by
        have := stdSimplex.{u}.δ_comp_σ_succ (i := (0 : Fin 2))
        dsimp at this
        rw [h.h₀₂, reassoc_of% this])
  h₀ := by rw [← square.δ₂_ιTriangle₀, assoc, IsPushout.inl_desc, h.h₀₁]
  h₁ := by
    have := stdSimplex.{u}.δ_comp_σ_self (i := (0 : Fin 2))
    dsimp at this
    rw [← square.δ₀_ιTriangle₁, assoc, IsPushout.inr_desc,
      reassoc_of% this]
  rel := by
    apply boundary₁.hom_ext_rightTensor
    · have := stdSimplex.{u}.δ_comp_σ_of_gt (n := 0) (i := 1) (j := 0) (by simp)
      dsimp at this ⊢
      rw [assoc, Subcomplex.topIso_inv_ι, comp_id, whiskerRight_fst_assoc,
        boundary₁.ι₀_desc, yonedaEquiv_symm_zero, comp_const,
        ← MonoidalCategory.comp_whiskerRight_assoc,
        boundary₁.ι₀_ι, square.δ₁_whiskerRight, assoc, assoc,
        IsPushout.inr_desc, reassoc_of% this,
        q.comm₀, comp_const, comp_const]
    · rw [assoc, Subcomplex.topIso_inv_ι, comp_id, whiskerRight_fst_assoc,
        boundary₁.ι₁_desc, yonedaEquiv_symm_zero, comp_const,
        ← MonoidalCategory.comp_whiskerRight_assoc,
        boundary₁.ι₁_ι, square.δ₀_whiskerRight, assoc, assoc,
        IsPushout.inl_desc, h.h₁₂, id_map, comp_const]

noncomputable def HomotopyR.homotopy (h : p.Homotopy q) : Homotopy p q :=
  h.homotopyL.homotopy

end

noncomputable def compUniqueUpToHomotopy [IsFibrant X]
    {p₀₁ p₀₁' : Edge x₀ x₁} {p₁₂ p₁₂' : Edge x₁ x₂} {p₀₂ p₀₂' : Edge x₀ x₂}
    (s : CompStruct p₀₁ p₁₂ p₀₂) (s' : CompStruct p₀₁' p₁₂' p₀₂')
    (h₀₁ : p₀₁.Homotopy p₀₁') (h₁₂ : p₁₂.Homotopy p₁₂') :
    p₀₂.Homotopy p₀₂' :=
  (CompStruct.unique s s' h₀₁.homotopyL h₁₂.homotopyL).homotopy

noncomputable def comp (p₀₁ : Edge x₀ x₁) (p₁₂ : Edge x₁ x₂) :
    Edge x₀ x₂ :=
  (exists_compStruct p₀₁ p₁₂).choose

noncomputable def compStruct (p₀₁ : Edge x₀ x₁) (p₁₂ : Edge x₁ x₂) :
    CompStruct p₀₁ p₁₂ (p₀₁.comp p₁₂) :=
  (exists_compStruct p₀₁ p₁₂).choose_spec.some

noncomputable def inv (p : Edge x₀ x₁) : Edge x₁ x₀ :=
  (CompStruct.right_inverse p).choose

noncomputable def CompStruct.mulInv (p : Edge x₀ x₁) : CompStruct p p.inv (id x₀) :=
  (CompStruct.right_inverse p).choose_spec.some

end Edge

def Hom.id (x : FundamentalGroupoid X) : Hom x x :=
  (Edge.id x).homotopyClass

def Hom.map {x₀ x₁ : FundamentalGroupoid X}
    (p : Hom x₀ x₁) {Y : SSet.{u}} (f : X ⟶ Y) :
    Hom (x₀.map f) (x₁.map f) :=
  p.postcomp (Subcomplex.RelativeMorphism.ofHom f) (by
    apply boundary₁.hom_ext
    · dsimp
      rw [assoc, boundary₁.ι₀_desc_assoc,
        boundary₁.ι₀_desc_assoc,
        yonedaEquiv_symm_zero, yonedaEquiv_symm_zero,
        Subcomplex.topIso_inv_ι_assoc, const_comp,
        FunctorToTypes.comp, const_comp]
    · dsimp
      rw [assoc, boundary₁.ι₁_desc_assoc,
        boundary₁.ι₁_desc_assoc,
        yonedaEquiv_symm_zero, yonedaEquiv_symm_zero,
        Subcomplex.topIso_inv_ι_assoc, const_comp,
        FunctorToTypes.comp, const_comp])

@[simp]
lemma Hom.mapHomotopyClass {x₀ x₁ : FundamentalGroupoid X}
    (p : Edge x₀ x₁) {Y : SSet.{u}} (f : X ⟶ Y) :
    Hom.map p.homotopyClass f = (p.pushforward f).homotopyClass :=
  rfl

lemma Hom.id_map (x : FundamentalGroupoid X)
    {Y : SSet.{u}} (f : X ⟶ Y) :
    (Hom.id x).map f = Hom.id (x.map f) := by
  simp [Hom.id]

lemma Hom.homotopyClass_surjective
    {x y : FundamentalGroupoid X} (f : Hom x y) :
    ∃ (p : Edge x y), p.homotopyClass = f :=
  Quot.mk_surjective f

@[simp]
lemma Hom.map_id {x y : FundamentalGroupoid X} (f : Hom x y) :
    Hom.map f (𝟙 X) = f := by
  obtain ⟨p, rfl⟩ := homotopyClass_surjective f
  simp

@[simp]
lemma Hom.map_comp {x y : FundamentalGroupoid X} (f : Hom x y)
    {Y Z : SSet.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    Hom.map f (g ≫ h) = Hom.map (Hom.map f g) h := by
  obtain ⟨p, rfl⟩ := homotopyClass_surjective f
  simp

variable [IsFibrant X]

noncomputable def Hom.comp {x₀ x₁ x₂ : FundamentalGroupoid X} (f : Hom x₀ x₁) (g : Hom x₁ x₂) :
    Hom x₀ x₂ := by
  refine Quot.lift₂ (fun p₀₁ p₁₂ ↦ (Edge.comp p₀₁ p₁₂).homotopyClass) ?_ ?_ f g
  · rintro p₀₁ p₁₂ p₁₂' ⟨h⟩
    exact (Edge.compUniqueUpToHomotopy (p₀₁.compStruct p₁₂)
      (p₀₁.compStruct p₁₂') (.refl _) h).eq
  · rintro p₀₁ p₀₁' p₁₂ ⟨h⟩
    exact (Edge.compUniqueUpToHomotopy (p₀₁.compStruct p₁₂)
      (p₀₁'.compStruct p₁₂) h (.refl _)).eq

noncomputable instance : CategoryStruct (FundamentalGroupoid X) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

def homMk {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁) :
    x₀ ⟶ x₁ :=
  p.homotopyClass

@[simp]
lemma homMk_refl (x : FundamentalGroupoid X) :
    homMk (Edge.id x) = 𝟙 x := rfl

lemma homMk_eq_of_homotopy {x₀ x₁ : FundamentalGroupoid X}
    {p q : Edge x₀ x₁} (h : p.Homotopy q) :
    homMk p = homMk q :=
  h.eq

@[simp]
lemma map_homMk {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁)
    {Y : SSet.{u}} [IsFibrant Y] (f : X ⟶ Y) :
    Hom.map (homMk p) f = homMk (p.pushforward f) := rfl

variable {x₀ x₁ x₂ : FundamentalGroupoid X}

lemma homMk_surjective : Function.Surjective (homMk (x₀ := x₀) (x₁ := x₁)) := by
  apply Quot.mk_surjective

lemma Edge.CompStruct.fac {x₀ x₁ x₂ : FundamentalGroupoid X}
    {p₀₁ : Edge x₀ x₁} {p₁₂ : Edge x₁ x₂} {p₀₂ : Edge x₀ x₂}
    (h : CompStruct p₀₁ p₁₂ p₀₂) : homMk p₀₁ ≫ homMk p₁₂ = homMk p₀₂ :=
  homMk_eq_of_homotopy (compUniqueUpToHomotopy (Edge.compStruct p₀₁ p₁₂)
    h (.refl _) (.refl _))

noncomputable instance : Category (FundamentalGroupoid X) where
  id_comp f := by
    obtain ⟨p, rfl⟩ := homMk_surjective f
    exact (Edge.CompStruct.idComp p).fac
  comp_id f:= by
    obtain ⟨p, rfl⟩ := homMk_surjective f
    exact (Edge.CompStruct.compId p).fac
  assoc {x₀ x₁ x₂ x₃} f₀₁ f₁₂ f₂₃ := by
    obtain ⟨p₀₁, rfl⟩ := homMk_surjective f₀₁
    obtain ⟨p₁₂, rfl⟩ := homMk_surjective f₁₂
    obtain ⟨p₂₃, rfl⟩ := homMk_surjective f₂₃
    exact (Edge.CompStruct.assoc (Edge.compStruct p₀₁ p₁₂)
      (Edge.compStruct p₁₂ p₂₃) (Edge.compStruct p₀₁ (p₁₂.comp p₂₃))).fac

@[reassoc (attr := simp)]
lemma homMk_comp_homMk_inv (p : Edge x₀ x₁) :
    homMk p ≫ homMk p.inv = 𝟙 _ :=
  (Edge.CompStruct.mulInv p).fac

noncomputable instance : Groupoid (FundamentalGroupoid X) :=
  Groupoid.ofIsIso (fun {x₀ x₁} f ↦ by
    obtain ⟨p, hp⟩ := homMk_surjective f
    have ⟨g, hg⟩ : ∃ g, f ≫ g = 𝟙 x₀ := by
      obtain ⟨q, ⟨hq⟩⟩ := Edge.CompStruct.right_inverse p
      exact ⟨homMk q, by rw [← hp, hq.fac, homMk_refl]⟩
    have ⟨g', hg'⟩ : ∃ g', g' ≫ f = 𝟙 x₁ := by
      obtain ⟨q, ⟨hq⟩⟩ := Edge.CompStruct.left_inverse p
      exact ⟨homMk q, by rw [← hp, hq.fac, homMk_refl]⟩
    obtain rfl : g = g' := by
      replace hg := g' ≫= hg
      replace hg' := hg' =≫ g
      rw [comp_id] at hg
      rw [assoc, id_comp] at hg'
      rw [← hg', hg]
    exact ⟨g, hg, hg'⟩)

-- why is not this automatic...???
instance {x y : FundamentalGroupoid X} (f : x ⟶ y) : IsIso f :=
  ((Groupoid.isoEquivHom _ _).symm f).isIso_hom

instance {x y : FundamentalGroupoid X} (f : x ⟶ y) : Epi f where
  left_cancellation g₁ g₂ h := by
    have : 𝟙 _ ≫ g₁ = 𝟙 _ ≫ g₂ := by
      rw [← IsIso.inv_hom_id f, Category.assoc, Category.assoc, h]
    simpa using this

instance {x y : FundamentalGroupoid X} (f : x ⟶ y) : Mono f where
  right_cancellation g₁ g₂ h := by
    have : g₁ ≫ 𝟙 _ = g₂ ≫ 𝟙 _ := by
      rw [← IsIso.hom_inv_id f, reassoc_of% h]
    simpa using this

@[reassoc (attr := simp)]
lemma homMk_inv_comp_homMk (p : Edge x₀ x₁) :
    homMk p.inv ≫ homMk p = 𝟙 _ := by
  rw [← cancel_epi (homMk p), homMk_comp_homMk_inv_assoc, comp_id]

@[simp]
lemma Hom.ofEq_map {x y : FundamentalGroupoid X} (h : x = y) {Y : SSet.{u}} [IsFibrant Y]
    (f : X ⟶ Y) :
    Hom.map (eqToHom h) f = eqToHom (show x.map f = y.map f by rw [h]) := by
  subst h
  apply Hom.id_map

end FundamentalGroupoid

open FundamentalGroupoid

variable {X} {Y : SSet.{u}} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)

@[simps! -isSimp obj_pt map]
def mapFundamentalGroupoid :
    FundamentalGroupoid X ⥤ FundamentalGroupoid Y where
  obj x := x.map f
  map {x₀ x₁} g := g.map f
  map_id x := by
    simp only [← homMk_refl, map_homMk, Edge.id_pushforward]
  map_comp {x₀ x₁ x₂} f₀₁ f₁₂ := by
    dsimp only
    obtain ⟨p₀₁, rfl⟩ := homMk_surjective f₀₁
    obtain ⟨p₁₂, rfl⟩ := homMk_surjective f₁₂
    exact ((Edge.compStruct p₀₁ p₁₂).pushforward f).fac.symm

attribute [simp] mapFundamentalGroupoid_obj_pt
attribute [local simp] mapFundamentalGroupoid_map

@[simp]
lemma mapFundamentalGroupoid_map_homMk {x₀ x₁ : FundamentalGroupoid X} (p : Edge x₀ x₁)
    {Y : SSet.{u}} [IsFibrant Y] (f : X ⟶ Y) :
    (mapFundamentalGroupoid f).map (homMk p) = homMk (p.pushforward f) := rfl

variable {f}
noncomputable def congrMapFundamentalGroupoid {g : X ⟶ Y} (h : f = g) :
    mapFundamentalGroupoid f ≅ mapFundamentalGroupoid g :=
  NatIso.ofComponents (fun x ↦ eqToIso (by rw [h]))

variable (X) in
@[simps!]
noncomputable def idMapFundamentalGroupoidIso :
    mapFundamentalGroupoid (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

variable (f) {Z : SSet.{u}} [IsFibrant Z] (g : Y ⟶ Z)

@[simps!]
noncomputable def compMapFundamentalGroupoidIso'
    (fg : X ⟶ Z) (hfg : f ≫ g = fg) :
    mapFundamentalGroupoid fg ≅
      mapFundamentalGroupoid f ⋙ mapFundamentalGroupoid g :=
  NatIso.ofComponents
    (fun _ ↦ eqToIso (by rw [← hfg]; rfl))
    (fun f ↦ by subst hfg; simp)

@[simps!]
noncomputable def compMapFundamentalGroupoidIso :
    mapFundamentalGroupoid (f ≫ g) ≅
      mapFundamentalGroupoid f ⋙ mapFundamentalGroupoid g :=
  compMapFundamentalGroupoidIso' f g (f ≫ g) rfl

noncomputable def FundamentalGroupoid.equivalenceOfIso
    [IsFibrant X] [IsFibrant Y] (e : X ≅ Y) :
    FundamentalGroupoid X ≌ FundamentalGroupoid Y where
  functor := mapFundamentalGroupoid e.hom
  inverse := mapFundamentalGroupoid e.inv
  unitIso := (idMapFundamentalGroupoidIso X).symm ≪≫
    compMapFundamentalGroupoidIso' _ _ _ e.hom_inv_id
  counitIso := (compMapFundamentalGroupoidIso' _ _ _ e.inv_hom_id).symm ≪≫
    idMapFundamentalGroupoidIso Y
  functor_unitIso_comp x := by
    dsimp
    rw [comp_id]
    erw [id_comp]
    rw [Hom.ofEq_map, eqToHom_trans, eqToHom_refl]

instance [IsIso f] [IsFibrant X] [IsFibrant Y] :
    (mapFundamentalGroupoid f).IsEquivalence :=
  (FundamentalGroupoid.equivalenceOfIso (asIso f)).isEquivalence_functor

end KanComplex

end SSet
