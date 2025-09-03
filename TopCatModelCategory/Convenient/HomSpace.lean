import Mathlib.Topology.CompactOpen
import TopCatModelCategory.Convenient.Category

-- Escardó, Lawson, Simpson

open Topology

universe v v' v'' t u

open Topology

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

variable {Y : Type v} [TopologicalSpace Y] {Z : Type v'} [TopologicalSpace Z]
  {T : Type v''} [TopologicalSpace T]

namespace Topology

namespace ContinuousMapGeneratedBy

variable {X}

def precomp {i : ι} (f : C(X i, Z)) : ContinuousMapGeneratedBy X Z T → C(X i, T) :=
  fun g ↦ ⟨_, g.prop f⟩

@[simp]
lemma precomp_apply {i : ι} (f : C(X i, Z)) (g : ContinuousMapGeneratedBy X Z T) :
    ⇑(precomp f g) = g ∘ f := rfl

instance : TopologicalSpace (ContinuousMapGeneratedBy X Z T) :=
  ⨅ (i : ι) (f : C(X i, Z)), .induced (precomp f) inferInstance

lemma continuous_iff {A : Type*} [TopologicalSpace A] {φ : A → ContinuousMapGeneratedBy X Z T} :
    Continuous φ ↔ ∀ (i : ι) (f : C(X i, Z)), Continuous (precomp f ∘ φ) := by
  simp only [continuous_iInf_rng, continuous_induced_rng]

lemma continuousGeneratedBy_iff_uncurry [∀ i, LocallyCompactSpace (X i)]
    (g : Z → ContinuousMapGeneratedBy X Y T) :
    ContinuousGeneratedBy X g ↔
      ∀ (i₁ : ι) (f₁ : C(X i₁, Z)) (i₂ : ι) (f₂ : C(X i₂, Y)) ,
        Continuous (fun (x₁, x₂) ↦ g (f₁ x₁) (f₂ x₂)) := by
  simp only [continuousGeneratedBy_def, continuous_iff]
  exact forall_congr' (fun i₁ ↦ forall_congr' (fun f₁ ↦
    forall_congr' (fun i₂ ↦ forall_congr' (fun f₂ ↦
      ⟨fun h ↦ ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
        fun h ↦ (ContinuousMap.curry ⟨_, h⟩).continuous⟩))))

lemma continuousGeneratedBy_dom_prod_iff [∀ i j, IsGeneratedBy X (X i × X j)]
    (g : Y × Z → T) :
    ContinuousGeneratedBy X g ↔
      ∀ (i₁ : ι) (f₁ : C(X i₁, Z)) (i₂ : ι) (f₂ : C(X i₂, Y)),
        Continuous (fun (x₁, x₂) ↦ g ⟨f₂ x₂, f₁ x₁⟩) := by
  refine ⟨fun h i₁ f₁ i₂ f₂ ↦ ?_, fun h ↦ ?_⟩
  · rw [IsGeneratedBy.continuous_iff X]
    intro j p
    let φ : X i₁ × X i₂ → Y × Z := fun (x₁, x₂) ↦ (f₂ x₂, f₁ x₁)
    have hφ : Continuous φ := by continuity
    replace h := h.comp hφ.continuousGeneratedBy
    rw [continuousGeneratedBy_def] at h
    exact h p
  · rw [continuousGeneratedBy_def]
    intro i f
    exact (h i (ContinuousMap.snd.comp f) i (ContinuousMap.fst.comp f)).comp
      (Continuous.prodMk continuous_id continuous_id)

variable [∀ i, LocallyCompactSpace (X i)] [∀ i j, IsGeneratedBy X (X i × X j)]

def curryEquiv :
  ContinuousMapGeneratedBy X (Y × Z) T ≃
    ContinuousMapGeneratedBy X Z (ContinuousMapGeneratedBy X Y T) where
  toFun g :=
    { toFun z := g.comp ⟨fun y ↦ (y, z), (Continuous.prodMk_left z).continuousGeneratedBy⟩
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using g.prop }
  invFun g :=
    { toFun x := g x.2 x.1
      prop := by
        simpa only [continuousGeneratedBy_iff_uncurry,
          continuousGeneratedBy_dom_prod_iff] using g.prop }
  left_inv _ := rfl
  right_inv _ := rfl

def ev : ContinuousMapGeneratedBy X (Y × ContinuousMapGeneratedBy X Y Z) Z :=
  curryEquiv.symm .id

def postcomp (p : ContinuousMapGeneratedBy X Z T) :
    ContinuousMapGeneratedBy X (ContinuousMapGeneratedBy X Y Z)
      (ContinuousMapGeneratedBy X Y T) :=
  curryEquiv (p.comp ev)

end ContinuousMapGeneratedBy

end Topology
