module

public import Mathlib.Topology.Homotopy.HomotopyGroup

@[expose] public section

universe v u₁ u₂ u₃

open Topology

variable {X : Type u₁} {Y : Type u₂} {Z : Type u₃}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

section

variable {T : Type v} {x : X}

@[simps]
def GenLoop.map (γ : GenLoop T X x) (f : ContinuousMap X Y) {y : Y} (hy : f x = y) :
    GenLoop T Y y :=
  ⟨f.comp γ.1, fun u hu ↦ by
    dsimp
    rw [γ.2 u hu, hy]⟩

lemma GenLoop.map_id (γ : GenLoop T X x) : GenLoop.map γ (.id X) rfl = γ := rfl

lemma GenLoop.map_comp (γ : GenLoop T X x)
    (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    {y : Y} (hy : f x = y) {z : Z} (hz : g y = z) :
    GenLoop.map (GenLoop.map γ f hy) g hz =
      GenLoop.map γ (g.comp f) (by aesop) :=
  rfl

def HomotopyGroup.map (z : HomotopyGroup T X x) (f : ContinuousMap X Y) {y : Y} (hy : f x = y) :
    HomotopyGroup T Y y := by
  refine Quotient.lift (s := GenLoop.Homotopic.setoid T x)
    (fun γ ↦ ⟦GenLoop.map γ f hy⟧) ?_ z
  rintro γ₁ γ₂ ⟨h⟩
  dsimp [ContinuousMap.HomotopyRel] at h
  apply Quotient.sound
  exact ⟨⟨⟨f.comp h.1.1, by aesop, by aesop⟩, fun i b hb ↦ congr_arg f (h.2 i b hb)⟩⟩

def HomotopyGroup.map_id (γ : HomotopyGroup T X x) :
    γ.map (.id X) rfl = γ := by
  obtain ⟨γ, rfl⟩ := Quotient.mk_surjective γ
  rfl

def HomotopyGroup.map_comp (γ : HomotopyGroup T X x)
    (f : ContinuousMap X Y) (g : ContinuousMap Y Z)
    {y : Y} (hy : f x = y) {z : Z} (hz : g y = z) :
    (γ.map f hy).map g hz = γ.map (g.comp f) (by aesop) := by
  obtain ⟨γ, rfl⟩ := Quotient.mk_surjective γ
  rfl

end
