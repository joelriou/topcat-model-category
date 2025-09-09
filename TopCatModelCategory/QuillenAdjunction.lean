import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

open HomotopicalAlgebra

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D] [ModelCategory C] [ModelCategory D]
  (F : C ⥤ D) (G : D ⥤ C)

namespace Functor

class PreservesCofibrations : Prop where
  cofibration_map {A B : C} (i : A ⟶ B) [Cofibration i] : Cofibration (F.map i)

lemma preservesCofibrations_iff :
    F.PreservesCofibrations ↔ cofibrations C ≤ (cofibrations D).inverseImage F := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · simp only [cofibration_iff] at h
    tauto
  · simp only [cofibration_iff]
    tauto

attribute [instance] PreservesCofibrations.cofibration_map

class PreservesFibrations : Prop where
  fibration_map {X Y : C} (p : X ⟶ Y) [Fibration p] : Fibration (F.map p)

lemma preservesFibrations_iff :
    F.PreservesFibrations ↔ fibrations C ≤ (fibrations D).inverseImage F := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · simp only [fibration_iff] at h
    tauto
  · simp only [fibration_iff]
    tauto

attribute [instance] PreservesFibrations.fibration_map

@[mk_iff]
class PreservesTrivialCofibrations (F : C ⥤ D) : Prop where
  trivialCofibrations_le (F) : trivialCofibrations C ≤ (trivialCofibrations D).inverseImage F

namespace PreservesTrivialCofibrations

variable [F.PreservesTrivialCofibrations]

section

variable {A B : C} (i : A ⟶ B) [Cofibration i] [WeakEquivalence i]

instance : Cofibration (F.map i) := by
  simpa only [cofibration_iff] using
    (trivialCofibrations_le F i (mem_trivialCofibrations i)).1

instance : WeakEquivalence (F.map i) := by
  simpa only [weakEquivalence_iff] using
    (trivialCofibrations_le F i (mem_trivialCofibrations i)).2

end

/-instance {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B) [WeakEquivalence f] :
    WeakEquivalence (F.map f) := by
  have : F.PreservesTrivialCofibrations := inferInstance
  sorry-/

end PreservesTrivialCofibrations

@[mk_iff]
class PreservesTrivialFibrations (G : D ⥤ C) : Prop where
  trivialFibrations_le (G) : trivialFibrations D ≤ (trivialFibrations C).inverseImage G

namespace PreservesTrivialFibrations

variable [G.PreservesTrivialFibrations]

section

variable {X Y : D} (p : X ⟶ Y) [Fibration p] [WeakEquivalence p]

instance : Fibration (G.map p) := by
  simpa only [fibration_iff] using
    (trivialFibrations_le G p (mem_trivialFibrations p)).1

instance : WeakEquivalence (G.map p) := by
  simpa only [weakEquivalence_iff] using
    (trivialFibrations_le G p (mem_trivialFibrations p)).2

end

/-instance {X Y : D} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (G.map f) := by
  have : G.PreservesTrivialFibrations := inferInstance
  sorry-/

end PreservesTrivialFibrations

end Functor

namespace Adjunction

variable {F G} (adj : F ⊣ G)

section

lemma preservesTrivialCofibrations_iff_hasLiftingProperty :
    F.PreservesTrivialCofibrations ↔
      ∀ ⦃A B : C⦄ (i : A ⟶ B) [Cofibration i] [WeakEquivalence i] ⦃X Y : D⦄ (p : X ⟶ Y)
        [Fibration p], HasLiftingProperty (F.map i) p := by
  rw [F.preservesTrivialCofibrations_iff]
  trans ∀ ⦃A B : C⦄ (i : A ⟶ B) [Cofibration i] [WeakEquivalence i],
    trivialCofibrations D (F.map i)
  · refine ⟨fun h A B i _ _ ↦ h i (mem_trivialCofibrations _),
      fun h A B i hi ↦ ?_⟩
    obtain ⟨_, _⟩ := (mem_trivialCofibrations_iff i).1 hi
    exact h i
  · refine forall_congr' (fun A ↦ forall_congr' (fun B ↦ forall_congr' (fun i ↦ forall_congr'
      (fun _ ↦ forall_congr' (fun _ ↦ ?_)))))
    rw [← fibrations_llp]
    exact ⟨fun h X Y p _ ↦ h p (by rwa [← fibration_iff]),
      fun h X Y p hp ↦ by rw [← fibration_iff] at hp; infer_instance⟩

lemma preservesCofibrations_iff_hasLiftingProperty :
    F.PreservesCofibrations ↔
      ∀ ⦃A B : C⦄ (i : A ⟶ B) [Cofibration i] ⦃X Y : D⦄ (p : X ⟶ Y)
        [Fibration p] [WeakEquivalence p], HasLiftingProperty (F.map i) p := by
  rw [F.preservesCofibrations_iff]
  trans ∀ ⦃A B : C⦄ (i : A ⟶ B) [Cofibration i], cofibrations D (F.map i)
  · exact ⟨fun h A B i _ ↦ h i (mem_cofibrations _),
      fun h A B i hi ↦ by rw [← cofibration_iff] at hi; exact h i⟩
  · refine forall_congr' (fun A ↦ forall_congr' (fun B ↦ forall_congr' (fun i ↦ forall_congr'
      (fun _ ↦ ?_))))
    rw [← trivialFibrations_llp]
    exact ⟨fun h X Y p _ ↦ h p (mem_trivialFibrations _),
      fun h X Y p hp ↦ by
        obtain ⟨_, _⟩ := (mem_trivialFibrations_iff p).1 hp
        infer_instance⟩

lemma preservesFibrations_iff_hasLiftingProperty :
    G.PreservesFibrations ↔
      ∀ ⦃X Y : D⦄ (p : X ⟶ Y) [Fibration p] ⦃A B : C⦄
        (i : A ⟶ B) [Cofibration i] [WeakEquivalence i], HasLiftingProperty i (G.map p) := by
  rw [G.preservesFibrations_iff]
  trans ∀ ⦃X Y : D⦄ (p : X ⟶ Y) [Fibration p], fibrations C (G.map p)
  · exact ⟨fun h X Y p _ ↦ h p (mem_fibrations _),
      fun h X Y p hp ↦ by rw [← fibration_iff] at hp; exact h p⟩
  · refine forall_congr' (fun X ↦ forall_congr' (fun Y ↦ forall_congr' (fun p ↦ forall_congr'
      (fun _ ↦ ?_))))
    rw [← trivialCofibrations_rlp]
    exact ⟨fun h A B i _ ↦ h i (mem_trivialCofibrations _),
      fun h A B i hi ↦ by
        obtain ⟨_, _⟩ := (mem_trivialCofibrations_iff i).1 hi
        infer_instance⟩

lemma preservesTrivialFibrations_iff_hasLiftingProperty :
    G.PreservesTrivialFibrations ↔
      ∀ ⦃X Y : D⦄ (p : X ⟶ Y) [Fibration p] [WeakEquivalence p]
      ⦃A B : C⦄ (i : A ⟶ B) [Cofibration i], HasLiftingProperty i (G.map p) := by
  rw [G.preservesTrivialFibrations_iff]
  trans ∀ ⦃X Y : D⦄ (p : X ⟶ Y) [Fibration p] [WeakEquivalence p], trivialFibrations C (G.map p)
  · exact ⟨fun h X Y p _ ↦ h p (mem_trivialFibrations _),
      fun h X Y p hp ↦ by
        obtain ⟨_, _⟩ := (mem_trivialFibrations_iff p).1 hp
        exact h p⟩
  · refine forall_congr' (fun A ↦ forall_congr' (fun B ↦ forall_congr'
      (fun i ↦ forall_congr' (fun _ ↦ forall_congr' (fun _ ↦ ?_)))))
    rw [← cofibrations_rlp]
    exact ⟨fun h A B i _ ↦ h i (mem_cofibrations _),
      fun h A B i hi ↦ by rw [← cofibration_iff] at hi; infer_instance⟩

include adj
lemma preservesTrivialCofibrations_iff_preservesFibrations :
    F.PreservesTrivialCofibrations ↔ G.PreservesFibrations := by
  simp only [preservesTrivialCofibrations_iff_hasLiftingProperty,
    preservesFibrations_iff_hasLiftingProperty,
    adj.hasLiftingProperty_iff]
  tauto

lemma preservesTrivialFibrations_iff_preservesCofibrations :
    G.PreservesTrivialFibrations ↔ F.PreservesCofibrations := by
  simp only [preservesCofibrations_iff_hasLiftingProperty,
    preservesTrivialFibrations_iff_hasLiftingProperty,
    adj.hasLiftingProperty_iff]
  tauto

end

class IsQuillenAdjunction (adj : F ⊣ G) : Prop extends
  F.PreservesCofibrations, G.PreservesFibrations

namespace IsQuillenAdjunction

variable [adj.IsQuillenAdjunction]

include adj

lemma preservesCofibrations : F.PreservesCofibrations :=
  IsQuillenAdjunction.toPreservesCofibrations adj

lemma preservesFibrations : G.PreservesFibrations :=
  IsQuillenAdjunction.toPreservesFibrations adj

lemma preservesTrivialCofibrations : F.PreservesTrivialCofibrations :=
  adj.preservesTrivialCofibrations_iff_preservesFibrations.2 (preservesFibrations adj)

lemma preservesTrivialFibrations : G.PreservesTrivialFibrations :=
  adj.preservesTrivialFibrations_iff_preservesCofibrations.2 (preservesCofibrations adj)

end IsQuillenAdjunction

class IsQuillenEquivalence (adj : F ⊣ G) : Prop extends adj.IsQuillenAdjunction where
  weakEquivalence_homEquiv_iff (adj) {A : C} {X : D} [IsCofibrant A] [IsFibrant X]
      (f : F.obj A ⟶ X) :
      WeakEquivalence (adj.homEquiv _ _ f) ↔ WeakEquivalence f

alias weakEquivalence_homEquiv_iff := IsQuillenEquivalence.weakEquivalence_homEquiv_iff

attribute [simp] weakEquivalence_homEquiv_iff

@[simp]
lemma weakEquivalence_homEquiv_symm_iff [adj.IsQuillenEquivalence] {A : C} {X : D}
    [IsCofibrant A] [IsFibrant X]
    (g : A ⟶ G.obj X) :
    WeakEquivalence ((adj.homEquiv _ _).symm g) ↔ WeakEquivalence g := by
  simp only [← adj.weakEquivalence_homEquiv_iff, Equiv.apply_symm_apply]

/-open IsQuillenAdjunction
lemma IsQuillenEquivalence.mk' [adj.IsQuillenAdjunction]
    [∀ (A : C), IsCofibrant A] [∀ (X : D), IsFibrant X]
    (h₁ : ∀ (A : C), WeakEquivalence (adj.unit.app A))
    (h₂ : ∀ (X : D), WeakEquivalence (adj.counit.app X)) :
    adj.IsQuillenEquivalence where
  weakEquivalence_homEquiv_iff {A X _ _} f := by
    have := preservesTrivialCofibrations adj
    have := preservesTrivialFibrations adj
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have : F.map ((adj.homEquiv A X) f) ≫ adj.counit.app X = f := by simp [homEquiv_unit]
      rw [← this]
      infer_instance
    · have : WeakEquivalence (G.map f) := inferInstance
      rw [homEquiv_unit]
      infer_instance-/

end Adjunction

end CategoryTheory
