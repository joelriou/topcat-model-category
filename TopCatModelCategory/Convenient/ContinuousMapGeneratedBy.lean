import TopCatModelCategory.Convenient.GeneratedBy

open Topology

variable {ι : Type t} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

variable {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace Topology

variable (X) in
def ContinuousGeneratedBy (g : Y → Z) : Prop :=
  ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f)

lemma continuousGeneratedBy_def (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f) := Iff.rfl

lemma continuousGeneratedBy_iff (g : Y → Z) :
    ContinuousGeneratedBy X g ↔
      Continuous ((WithGeneratedByTopology.equiv (X := X)).symm ∘ g ∘
        WithGeneratedByTopology.equiv (X := X)) := by
  rw [IsGeneratedBy.equiv_symm_comp_continuous_iff,
    WithGeneratedByTopology.continuous_from_iff]
  rfl

def ContinuousGeneratedBy.continuousMap {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    C(WithGeneratedByTopology X Y, WithGeneratedByTopology X Z) :=
  ⟨WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv, by
    rwa [← continuousGeneratedBy_iff]⟩

@[simp]
lemma ContinuousGeneratedBy.continuousMap_coe {g : Y → Z}
    (hg : ContinuousGeneratedBy X g) :
    ⇑hg.continuousMap = WithGeneratedByTopology.equiv.symm ∘ g ∘ WithGeneratedByTopology.equiv :=
  rfl

lemma ContinuousGeneratedBy.comp {g : Y → Z} (hg : ContinuousGeneratedBy X g)
    {T : Type*} [TopologicalSpace T] {f : T → Y} (hf : ContinuousGeneratedBy X f) :
    ContinuousGeneratedBy X (g ∘ f) := by
  rw [continuousGeneratedBy_iff]
  exact (hg.continuousMap.comp hf.continuousMap).continuous

end Topology

lemma Continuous.continuousGeneratedBy {g : Y → Z}
    (hg : Continuous g) : ContinuousGeneratedBy X g := by
  rw [continuousGeneratedBy_def]
  intro i f
  exact hg.comp f.continuous

namespace Topology

variable (X Y Z) in
@[ext]
structure ContinuousMapGeneratedBy where
  toFun : Y → Z
  prop : ContinuousGeneratedBy X toFun

instance : FunLike (ContinuousMapGeneratedBy X Y Z) Y Z where
  coe f := f.toFun
  coe_injective' _ _ _ := by aesop

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

namespace WithGeneratedByTopology

variable (X Y)

def equivSymmAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X Y (WithGeneratedByTopology X Y) where
  toFun := equiv.symm
  prop := by
    rw [continuousGeneratedBy_def]
    intro i f
    rw [IsGeneratedBy.equiv_symm_comp_continuous_iff]
    continuity

@[simp]
lemma equivSymmAsContinuousMapGeneratedBy_coe :
    ⇑(equivSymmAsContinuousMapGeneratedBy X Y) = equiv.symm := rfl

def equivAsContinuousMapGeneratedBy :
    ContinuousMapGeneratedBy X (WithGeneratedByTopology X Y) Y where
  toFun := equiv
  prop := continuous_equiv.continuousGeneratedBy

@[simp]
lemma equivAsContinuousMapGeneratedBy_coe :
    ⇑(equivAsContinuousMapGeneratedBy X Y) = equiv := rfl

end WithGeneratedByTopology
