import Mathlib.Topology.ContinuousMap.Basic

universe v t u

open Topology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

namespace TopologicalSpace

variable {Y : Type v} [TopologicalSpace Y]

def generatedBy : TopologicalSpace Y :=
  ⨆ (i : ι) (f : C(X i, Y)), coinduced f inferInstance

end TopologicalSpace

section

def Topology.WithGeneratedByTopology (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    (Y : Type v) [TopologicalSpace Y] := Y

variable {X} in
def Topology.withGeneratedByTopologyEquiv {Y : Type v} [TopologicalSpace Y] :
    WithGeneratedByTopology X Y ≃ Y := Equiv.refl _

instance {Y : Type v} [TopologicalSpace Y] :
    TopologicalSpace (WithGeneratedByTopology X Y) :=
  .generatedBy X (Y := Y)

end

section

variable {Y : Type v} [tY : TopologicalSpace Y]

lemma isOpen_generatedBy_iff {U : Set Y} :
    IsOpen[.generatedBy X] U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsOpen (f ⁻¹' U) := by
  simp [isOpen_iSup_iff, isOpen_coinduced]

lemma isClosed_generatedBy_iff {U : Set Y} :
    IsClosed[.generatedBy X] U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsClosed (f ⁻¹' U) := by
  simp [isClosed_iSup_iff, isClosed_coinduced]

lemma continuous_generatedBy_dom_iff {Z : Type*} [TopologicalSpace Z] (g : Y → Z) :
    Continuous[.generatedBy X, _] g ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g.comp f) := by
  simp only [continuous_iSup_dom]
  exact forall_congr' (fun i ↦ forall_congr'
    (fun f ↦ (by rw [continuous_coinduced_dom])))

lemma TopologicalSpace.generatedBy_le :
    generatedBy X ≤ tY := by
  intro U hU
  rw [isOpen_generatedBy_iff]
  intro i f
  exact f.continuous.isOpen_preimage U hU

end

section

variable (Y : Type v) [tY : TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace Topology

class IsGeneratedBy : Prop where
  le_generatedBy : tY ≤ .generatedBy X

instance (i : ι) : IsGeneratedBy X (X i) where
  le_generatedBy := by
    intro U hU
    rw [isOpen_generatedBy_iff] at hU
    exact hU (.id _)

namespace IsGeneratedBy

section

variable [IsGeneratedBy X Y]

lemma generatedBy_eq : .generatedBy X = tY :=
  le_antisymm (TopologicalSpace.generatedBy_le X) le_generatedBy

lemma isOpen_iff {U : Set Y} :
    IsOpen U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsOpen (f ⁻¹' U) := by
  rw [← isOpen_generatedBy_iff, generatedBy_eq X]

lemma isClosed_iff {U : Set Y} :
    IsClosed U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsClosed (f ⁻¹' U) := by
  rw [← isClosed_generatedBy_iff, generatedBy_eq X]

lemma continuous_iff (g : Y → Z) :
    Continuous g ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g.comp f) := by
  rw [← continuous_generatedBy_dom_iff, generatedBy_eq X]

lemma continuous_generatedBy_cod_iff (g : Y → Z) :
    Continuous[_, .generatedBy X] g ↔ Continuous g := by
  refine ⟨fun hg ↦ ?_, fun hg ↦ ?_⟩
  · rw [continuous_def]
    intro U hU
    exact @Continuous.isOpen_preimage _ _ _  (.generatedBy X) _ hg _
      (TopologicalSpace.generatedBy_le X _ hU)
  · rw [continuous_iff X]
    intro i f
    rw [continuous_def]
    intro U hU
    rw [isOpen_generatedBy_iff] at hU
    exact hU (ContinuousMap.comp ⟨_, hg⟩ f)

end

end IsGeneratedBy

variable {Y}

variable {X} in
lemma IsQuotientMap.isGeneratedBy {f : Y → Z} (hf : IsQuotientMap f)
    [IsGeneratedBy X Y] :
    IsGeneratedBy X Z where
  le_generatedBy U hU := by
    rw [isOpen_generatedBy_iff] at hU
    rw [← hf.isOpen_preimage, IsGeneratedBy.isOpen_iff X]
    intro i g
    exact hU (ContinuousMap.comp ⟨f, hf.continuous⟩ g)

def ContinuousGeneratedBy (g : Y → Z) : Prop :=
  ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g.comp f)

lemma continuousGeneratedBy_def (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g.comp f) := Iff.rfl

lemma continuousGeneratedBy_iff (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      Continuous[.generatedBy X, .generatedBy X] g := by
  simp [continuousGeneratedBy_def, continuous_generatedBy_dom_iff,
    IsGeneratedBy.continuous_generatedBy_cod_iff]

variable {X} in
lemma ContinuousGeneratedBy.comp
    {g : Y → Z} (hg : ContinuousGeneratedBy X g)
    {T : Type*} [TopologicalSpace T] {f : T → Y}
    (hf : ContinuousGeneratedBy X f) :
    ContinuousGeneratedBy X (g.comp f) := by
  rw [continuousGeneratedBy_def] at hf hg ⊢
  intro i a
  exact hg ⟨_, hf a⟩

end Topology

variable {X} in
lemma Continuous.continuousGeneratedBy {g : Y → Z}
    (hg : Continuous g) : ContinuousGeneratedBy X g := by
  rw [continuousGeneratedBy_def]
  intro i f
  exact hg.comp f.continuous

variable (Z) in
@[ext]
structure ContinuousMapGeneratedBy where
  toFun : Y → Z
  prop : ContinuousGeneratedBy X toFun

instance : FunLike (ContinuousMapGeneratedBy X Y Z) Y Z where
  coe f := f.toFun
  coe_injective' _ _ _ := by aesop

variable {X Y}

@[simps]
def ContinuousMapGeneratedBy.id : ContinuousMapGeneratedBy X Y Y where
  toFun := _root_.id
  prop := continuous_id.continuousGeneratedBy

@[simps]
def ContinuousMapGeneratedBy.comp
    {Z : Type*} [TopologicalSpace Z]
    {T : Type*} [TopologicalSpace T]
    (g : ContinuousMapGeneratedBy X Y Z)
    (f : ContinuousMapGeneratedBy X T Y) :
    ContinuousMapGeneratedBy X T Z where
  toFun := g.toFun.comp f.toFun
  prop := g.prop.comp f.prop

end

namespace Topology

namespace WithGeneratedByTopology

variable (Y : Type v) [TopologicalSpace Y]

def continuousMapFrom : C(WithGeneratedByTopology X Y, Y) where
  toFun := withGeneratedByTopologyEquiv
  continuous_toFun := by
    rw [continuous_def]
    intro U hU
    exact TopologicalSpace.generatedBy_le X U hU

def continuousMapGeneratedByTo :
    ContinuousMapGeneratedBy X Y (WithGeneratedByTopology X Y) where
  toFun := withGeneratedByTopologyEquiv.symm
  prop := by
    rw [continuousGeneratedBy_def]
    intro i f
    rw [IsGeneratedBy.continuous_generatedBy_cod_iff]
    exact f.continuous

def continuousMapGeneratedByFrom :
    ContinuousMapGeneratedBy X (WithGeneratedByTopology X Y) Y where
  toFun := withGeneratedByTopologyEquiv
  prop := (continuousMapFrom X Y).continuous.continuousGeneratedBy

end WithGeneratedByTopology

end Topology
