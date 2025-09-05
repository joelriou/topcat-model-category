/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Topology.ContinuousMap.Basic

/-!
# The `X`-generated topology for a family of topological spaces

Let `X : ι → Type u` be a family of topological spaces.
Let `Y` be a topological space. We introduce a type synonym
`WithGeneratedByTopology X Y` for `Y`. This type endowed
with the `X`-generated topology, which is coinduced by
all continuous maps `X i → Y`. When the bijection
`WithGeneratedByTopology X Y ≃ Y` is an homeomorphism,
we say that `Y` is `X`-generated (typeclass `IsGeneratedBy X Y`).

-/
-- #29341
universe v v' t u

open Topology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
  {Y : Type v} [tY : TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]

namespace TopologicalSpace

/-- Given a family of topological spaces `X i`, the `X`-generated topology on
a topological space `Y` is the topology that is coinduced
by all continuous maps `X i → Y`. -/
def generatedBy : TopologicalSpace Y :=
  ⨆ (i : ι) (f : C(X i, Y)), coinduced f inferInstance

end TopologicalSpace

variable {X}

namespace Topology

/-- Given a family of topological spaces `X i`, and a topological space `Y`,
this is a type synonym for `Y` which we endow with `X`-generated topology. -/
@[nolint unusedArguments]
def WithGeneratedByTopology (X : ι → Type u) [∀ i, TopologicalSpace (X i)]
    (Y : Type v) [TopologicalSpace Y] := Y

namespace WithGeneratedByTopology

/-- The obvious bijection `WithGeneratedByTopology X Y ≃ Y`, where
the source is endowed with the `X`-generated topology. See `continuous_equiv`
for the continuity of `equiv`. The inverse map `equiv.symm` is continuous
iff `Y` is `X`-generated, see `isGeneratedBy_iff`. -/
def equiv :
    WithGeneratedByTopology X Y ≃ Y :=
  Equiv.refl _

instance {Y : Type v} [TopologicalSpace Y] :
    TopologicalSpace (WithGeneratedByTopology X Y) :=
  .generatedBy X (Y := Y)

lemma isOpen_iff {U : Set (WithGeneratedByTopology X Y)} :
    IsOpen U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsOpen (f ⁻¹' (equiv.symm ⁻¹' U)) := by
  simp [isOpen_iSup_iff, isOpen_coinduced, equiv, Equiv.refl]

lemma isClosed_iff {U : Set (WithGeneratedByTopology X Y)} :
    IsClosed U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsClosed (f ⁻¹' (equiv.symm ⁻¹' U)) := by
  simp [isClosed_iSup_iff, isClosed_coinduced, equiv, Equiv.refl]

lemma continuous_from_iff (g : WithGeneratedByTopology X Y → Z) :
    Continuous g ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ equiv.symm ∘ f : X i → Z) := by
  simp only [continuous_iSup_dom,]
  exact forall_congr' (fun i ↦ forall_congr'
    (fun f ↦ (by rw [continuous_coinduced_dom]; simp [equiv, Equiv.refl])))

@[continuity]
lemma continuous_equiv : Continuous (equiv (X := X) (Y := Y)) := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff]
  intro i f
  exact f.continuous.isOpen_preimage _ hU

end WithGeneratedByTopology

end Topology

lemma TopologicalSpace.generatedBy_le : generatedBy X ≤ tY := by
  intro U hU
  exact WithGeneratedByTopology.continuous_equiv.isOpen_preimage U hU

namespace Topology

variable (X Y) in
/-- Given a family of topological spaces `X i`, we say that a topological space is
`X`-generated (`IsGeneratedBy X Y`) when the topology on `Y` is the `X`-generated
topology, i.e. when the identity is an homeomorphism
`WithGeneratedByTopology X Y ≃ₜ Y` (see `IsGeneratedBy.homeomorph`). -/
@[mk_iff]
class IsGeneratedBy : Prop where
  continuous_equiv_symm : Continuous (WithGeneratedByTopology.equiv (X := X) (Y := Y)).symm

namespace IsGeneratedBy

attribute [continuity] continuous_equiv_symm

lemma le_generatedBy [IsGeneratedBy X Y] : tY ≤ .generatedBy X :=
  fun U hU ↦ continuous_equiv_symm.isOpen_preimage U hU

lemma generatedBy_eq [IsGeneratedBy X Y] : .generatedBy X = tY := by
  refine le_antisymm TopologicalSpace.generatedBy_le le_generatedBy

lemma iff_le_generatedBy :
    IsGeneratedBy X Y ↔ tY ≤ .generatedBy X :=
  ⟨fun _ ↦ le_generatedBy, fun h ↦ ⟨by rwa [continuous_def]⟩⟩

section

variable [IsGeneratedBy X Y]

/-- The homeomorphism `WithGeneratedByTopology X Y ≃ₜ Y` when `Y` is `X`-generated. -/
def homeomorph [IsGeneratedBy X Y] : WithGeneratedByTopology X Y ≃ₜ Y where
  toEquiv := WithGeneratedByTopology.equiv
  continuous_toFun := by continuity
  continuous_invFun := by continuity

@[simp]
lemma homeomorph_coe :
   ⇑(homeomorph (X := X) (Y := Y)) = WithGeneratedByTopology.equiv := rfl

@[simp]
lemma homeomorph_symm_coe :
   ⇑(homeomorph (X := X) (Y := Y)).symm = WithGeneratedByTopology.equiv.symm := rfl

variable (X)

lemma isOpen_iff {U : Set Y} :
    IsOpen U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsOpen (f ⁻¹' U) := by
  simp [← (homeomorph (X := X)).isQuotientMap.isOpen_preimage,
    WithGeneratedByTopology.isOpen_iff]

lemma isClosed_iff {U : Set Y} :
    IsClosed U ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), IsClosed (f ⁻¹' U) := by
  simp [← (homeomorph (X := X)).isQuotientMap.isClosed_preimage,
    WithGeneratedByTopology.isClosed_iff]

lemma continuous_iff (g : Y → Z) :
    Continuous g ↔ ∀ ⦃i : ι⦄ (f : C(X i, Y)), Continuous (g ∘ f) := by
  rw [(homeomorph (X := X)).isQuotientMap.continuous_iff,
    WithGeneratedByTopology.continuous_from_iff]
  rfl

lemma equiv_symm_comp_continuous_iff (g : Y → Z) :
    Continuous ((WithGeneratedByTopology.equiv (X := X)).symm ∘ g) ↔ Continuous g := by
  refine ⟨fun hg ↦ WithGeneratedByTopology.continuous_equiv.comp hg, fun hg ↦ ?_⟩
  rw [continuous_iff (X := X)]
  intro i f
  rw [continuous_def]
  intro U hU
  rw [WithGeneratedByTopology.isOpen_iff] at hU
  exact hU (ContinuousMap.comp ⟨g, hg⟩ f)

end

instance (i : ι) : IsGeneratedBy X (X i) where
  continuous_equiv_symm := by
    rw [continuous_def]
    intro U hU
    rw [WithGeneratedByTopology.isOpen_iff] at hU
    exact hU ⟨_, continuous_id⟩

instance : IsGeneratedBy X (WithGeneratedByTopology X Y) where
  continuous_equiv_symm := by
    rw [continuous_def]
    intro U hU
    rw [WithGeneratedByTopology.isOpen_iff] at hU ⊢
    intro i f
    refine hU ⟨WithGeneratedByTopology.equiv.symm ∘ f, ?_⟩
    rw [continuous_iff X]
    intro j g
    rw [Function.comp_assoc, equiv_symm_comp_continuous_iff]
    continuity

instance : IsGeneratedBy X (PUnit.{v + 1}) := by
  rw [iff_le_generatedBy]
  exact Eq.le (by subsingleton)

lemma mk' {α : Type*} {T : α → Type*} [∀ a, TopologicalSpace (T a)]
    [∀ a, IsGeneratedBy X (T a)] (f : ∀ a, C(T a, Y))
    (hf : ∀ (U : Set Y), (∀ a, IsOpen (f a ⁻¹' U)) → IsOpen U) :
    IsGeneratedBy X Y := by
  rw [iff_le_generatedBy]
  intro U hU
  refine hf _ (fun a ↦ ?_)
  rw [isOpen_iff X]
  intro i g
  simp only [isOpen_iSup_iff, isOpen_coinduced, Set.preimage_id'] at hU
  exact hU _ ((f a).comp g)

end IsGeneratedBy

lemma IsQuotientMap.isGeneratedBy {f : Y → Z} (hf : IsQuotientMap f) [IsGeneratedBy X Y] :
    IsGeneratedBy X Z where
  continuous_equiv_symm := by
    rw [continuous_def]
    intro U hU
    rw [WithGeneratedByTopology.isOpen_iff] at hU
    rw [← hf.isOpen_preimage, IsGeneratedBy.isOpen_iff X]
    intro i g
    exact hU ⟨f ∘ g, hf.continuous.comp g.continuous⟩

end Topology
