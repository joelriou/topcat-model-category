import TopCatModelCategory.TopCat.Colimits
import TopCatModelCategory.ColimitsType
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Homeomorph.Lemmas

universe w' w v u

open CategoryTheory Topology Limits

lemma isHomeomorph_iff {X Y : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
    (f : X → Y) :
    IsHomeomorph f ↔ Function.Bijective f ∧ tY = .coinduced f tX := by
  refine ⟨fun hf ↦ ⟨hf.bijective, hf.isQuotientMap.eq_coinduced⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  have h₃ (V : Set Y) : IsOpen V ↔ IsOpen (f ⁻¹' V) := by
    rw [h₂, isOpen_coinduced]
  refine ⟨?_, ?_, h₁⟩
  · rw [continuous_def]
    intro V hV
    rwa [← h₃]
  · intro U hU
    rwa [h₃, h₁.injective.preimage_image]

lemma Topology.IsOpenEmbedding.comp_continuous_iff {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → Z} (hf : IsOpenEmbedding f) (g : X → Y) :
    Continuous (f ∘ g) ↔ Continuous g := by
  refine ⟨fun h ↦ ?_, fun h ↦ hf.continuous.comp h⟩
  rw [continuous_def]
  intro U hU
  rw [hf.isOpen_iff] at hU
  obtain ⟨V, hV, rfl⟩ := hU
  exact h.isOpen_preimage V hV

lemma Sigma.exists_continuousMap_of_connectedSpace
    {T : Type*} [TopologicalSpace T] [ConnectedSpace T]
    {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (f : C(T, Σ i, X i)) :
    ∃ (i : ι) (g : C(T, X i)), ContinuousMap.comp ⟨Sigma.mk i, by continuity⟩ g = f := by
  let t₀ : T := Classical.arbitrary _
  generalize hi : (f t₀).1 = i
  have (t : T) : (f t).1 = i := by
    letI : TopologicalSpace ι := ⊥
    have : DiscreteTopology ι := ⟨rfl⟩
    exact (PreconnectedSpace.constant (f := Sigma.fst ∘ f) inferInstance
      (by continuity) (x := t) (y := t₀)).trans hi
  have (t : T) : ∃ (x : X i), f t = ⟨i, x⟩ := by
    generalize hy : f t = y
    obtain ⟨j, y⟩ := y
    obtain rfl : i = j := (this t).symm.trans (congr_arg Sigma.fst hy)
    exact ⟨y, rfl⟩
  choose g hg using this
  refine ⟨i, ⟨g, ?_⟩, by ext t : 1; exact (hg t).symm⟩
  rw [← (IsOpenEmbedding.sigmaMk (σ := X) (i := i)).comp_continuous_iff]
  convert f.continuous
  ext t : 1
  exact (hg t).symm

namespace CategoryTheory

namespace Functor

section

variable {J : Type u} [Category.{v} J] (F : J ⥤ TopCat.{w})

instance (j : J) : TopologicalSpace ((F ⋙ forget _).obj j) :=
  inferInstanceAs (TopologicalSpace (F.obj j))

structure CoconeTop extends CoconeTypes.{w'} (F ⋙ forget _) where
  topPt : TopologicalSpace pt := by infer_instance
  continuous_ι (j : J) : Continuous (ι j) := by continuity

namespace CoconeTop

attribute [instance] topPt

instance : TopologicalSpace ((F ⋙ forget _).ColimitType) :=
  ⨆ (j : J) , (F.obj j).str.coinduced ((F ⋙ forget _).ιColimitType j)

variable {F} (c : F.CoconeTop)

@[continuity]
lemma continuous_descColimitType :
    Continuous ((F ⋙ forget _).descColimitType c.toCoconeTypes) := by
  rw [continuous_iSup_dom]
  intro i
  rw [continuous_coinduced_dom]
  exact c.continuous_ι i

structure IsColimit where
  isHomeomorph : IsHomeomorph ((F ⋙ forget _).descColimitType c.toCoconeTypes)

variable {c}

namespace IsColimit

lemma isColimit_coconeTypes (hc : c.IsColimit) :
    c.toCoconeTypes.IsColimit where
  bijective := hc.isHomeomorph.bijective

noncomputable def homeomorph (hc : c.IsColimit) :
    (F ⋙ forget _).ColimitType ≃ₜ c.pt :=
  hc.isHomeomorph.homeomorph

@[simp]
lemma homeomorph_apply (hc : c.IsColimit) (i : J) (x : F.obj i) :
    hc.homeomorph ((F ⋙ forget _).ιColimitType i x) = c.ι i x := rfl

@[simp]
lemma homeomorph_symm_apply (hc : c.IsColimit) (i : J) (x : F.obj i) :
    hc.homeomorph.symm (c.ι i x) = (F ⋙ forget _).ιColimitType i x :=
  hc.homeomorph.injective (by simp)

end IsColimit

variable (c) in
lemma isColimit_iff_toCoconeTypes_isColimit_and_coinduced :
    c.IsColimit ↔ c.toCoconeTypes.IsColimit ∧
      (inferInstance : TopologicalSpace c.pt) =
        ⨆ (j : J), (F.obj j).str.coinduced (c.ι j) := by
  let φ := ((F ⋙ forget _).descColimitType c.toCoconeTypes)
  have h₁ : c.toCoconeTypes.IsColimit ↔ Function.Bijective φ :=
    ⟨fun h ↦ h.bijective, fun h ↦ ⟨h⟩⟩
  have h₂ : c.IsColimit ↔ IsHomeomorph φ :=
    ⟨fun h ↦ h.isHomeomorph, fun h ↦ ⟨h⟩⟩
  rw [h₁, h₂, isHomeomorph_iff]
  refine and_congr Iff.rfl (Eq.congr_right ?_)
  ext U
  rw [isOpen_iSup_iff, isOpen_coinduced, isOpen_iSup_iff]
  rfl

end CoconeTop

end

section

variable {J : Type u} (F : Discrete J ⥤ TopCat.{w})

abbrev CofanTop := CoconeTop.{w'} F

variable {F}

namespace CofanTop

variable (c : F.CofanTop)

abbrev inj (i : J) : F.obj ⟨i⟩ → c.pt := c.ι ⟨i⟩

@[continuity]
lemma continuous_inj (i : J) : Continuous (c.inj i) :=
  c.continuous_ι ⟨i⟩

def toCofanTypes : (F ⋙ forget _).CofanTypes := c.toCoconeTypes

@[simp]
lemma toCofanTypes_inj (i : J) : c.toCofanTypes.inj i = c.inj i := rfl

lemma _root_.CategoryTheory.Functor.CoconeTop.IsColimit.isColimit_toCofanTypes
    {c : F.CofanTop} (hc : c.IsColimit) :
    c.toCofanTypes.IsColimit := hc.isColimit_coconeTypes

variable (F) in
def sigma : F.CofanTop where
  toCoconeTypes := CofanTypes.sigma (F ⋙ forget _)
  topPt := inferInstanceAs (TopologicalSpace (Σ (i : J), F.obj ⟨i⟩))
  continuous_ι := by
    rintro ⟨i⟩
    exact continuous_sigmaMk (σ := fun i ↦ F.obj ⟨i⟩) (i := i)

variable (F) in
lemma isColimit_sigma : (sigma F).IsColimit where
  isHomeomorph := by
    constructor
    · continuity
    · intro U hU
      let e := (CofanTypes.isColimit_sigma (F ⋙ forget _)).equiv
      obtain ⟨V, rfl⟩ : ∃ (V : Set (Σ i, F.obj ⟨i⟩)), U = e ⁻¹' V := ⟨e.symm ⁻¹' U, by simp⟩
      rw [isOpen_iSup_iff] at hU ⊢
      intro i
      replace hU := hU ⟨i⟩
      rw [isOpen_coinduced] at hU ⊢
      convert hU
      ext (x : F.obj ⟨i⟩)
      simp only [CofanTypes.sigma_pt, comp_obj, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, h⟩
        obtain ⟨⟨i'⟩, x', rfl⟩ := ιColimitType_jointly_surjective _ y
        obtain rfl : i' = i := congr_arg Sigma.fst h
        obtain rfl : x' = x := by
          rw [Sigma.ext_iff, heq_eq_eq] at h
          exact h.2
        exact hy
      · intro hx
        exact ⟨ιColimitType _ ⟨i⟩ x, hx, rfl⟩
    · exact (CofanTypes.isColimit_sigma (F ⋙ forget _)).bijective

section

variable {c}

variable (hc : c.IsColimit)

variable (T : Type*) [TopologicalSpace T] [ConnectedSpace T]

include hc in
lemma bijective_continuousMap_of_isColimit_of_connectedSpace :
    Function.Bijective (α := Σ (i : J), C(T, F.obj ⟨i⟩))
      (fun ⟨i, f⟩ ↦ (ContinuousMap.comp ⟨c.inj i, by continuity⟩ f)) := by
  let t₀ : T := Classical.arbitrary _
  have hc' := hc.isColimit_toCofanTypes
  constructor
  · intro ⟨i, f⟩ ⟨j, g⟩ h
    have (t : T) : (⟨i, f t⟩ : Σ i, F.obj ⟨i⟩) = ⟨j, g t⟩ :=
      (CofanTypes.equivOfIsColimit hc').injective (DFunLike.congr_fun h t)
    obtain rfl : i = j := congr_arg Sigma.fst (this t₀)
    aesop
  · intro f
    let e₁ := (CofanTop.isColimit_sigma F).homeomorph
    let e₂ := hc.homeomorph
    let e := e₂.symm.trans e₁
    obtain ⟨i, g, hg⟩ := Sigma.exists_continuousMap_of_connectedSpace ⟨e ∘ f,
      (Homeomorph.continuous _).comp f.continuous⟩
    refine ⟨⟨i, g⟩, ?_⟩
    ext x
    apply e.injective
    have h₁ := DFunLike.congr_fun hg x
    dsimp at h₁ ⊢
    rw [← h₁]
    apply e₁.symm.injective
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply, e]
    rw [CoconeTop.IsColimit.homeomorph_symm_apply]
    symm
    apply CoconeTop.IsColimit.homeomorph_symm_apply

variable {T} in
noncomputable def equivOfIsColimitOfConnectedSpace :
    (Σ (i : J), C(T, F.obj ⟨i⟩)) ≃ C(T, c.pt) :=
  Equiv.ofBijective _ (bijective_continuousMap_of_isColimit_of_connectedSpace hc T)

lemma equivOfIsColimitOfConnectedSpace_apply (i : J) (f : C(T, F.obj ⟨i⟩)) :
    equivOfIsColimitOfConnectedSpace hc ⟨i, f⟩ =
      ContinuousMap.comp ⟨c.inj i, by continuity⟩ f := rfl

end

end CofanTop

end

variable {J : Type u} [Category.{v} J] (F : J ⥤ TopCat.{w})

@[simps]
def coconeTopEquiv : CoconeTop.{w} F ≃ Cocone F where
  toFun c :=
    { pt := TopCat.of c.pt
      ι :=
        { app j := TopCat.ofHom ⟨c.ι j, c.continuous_ι j⟩
          naturality _ _ f := by
            ext
            apply c.ι_naturality_apply } }
  invFun c :=
    { pt := c.pt
      ι j := c.ι.app j
      ι_naturality f := by
        ext x
        exact ConcreteCategory.congr_hom (c.w f) x }
  left_inv _ := rfl
  right_inv _ := rfl

lemma CoconeTop.isColimit_iff (c : CoconeTop.{w} F) :
    c.IsColimit ↔ Nonempty (Limits.IsColimit (F.coconeTopEquiv c)) := by
  rw [TopCat.nonempty_isColimit_iff, isColimit_iff_toCoconeTypes_isColimit_and_coinduced,
    CoconeTypes.isColimit_iff]
  rfl

end Functor

end CategoryTheory

namespace TopCat

variable {J : Type u} [Category.{v} J] {F : J ⥤ TopCat.{w}}

theorem isColimit_iff_coconeTopIsColimit (c : Cocone F) :
    Nonempty (IsColimit c) ↔ (F.coconeTopEquiv.symm c).IsColimit := by
  rw [Functor.CoconeTop.isColimit_iff, Equiv.apply_symm_apply]

end TopCat
