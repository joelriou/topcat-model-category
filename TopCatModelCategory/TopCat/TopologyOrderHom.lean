import Mathlib.Topology.Category.TopCat.Basic

variable (A B : Type*) [Preorder A] [Preorder B] [TopologicalSpace B]

namespace OrderHom

instance topologicalSpace : TopologicalSpace (A →o B) :=
  TopologicalSpace.induced OrderHom.toFun
    (inferInstanceAs (TopologicalSpace (A → B)))

lemma isInducing : Topology.IsInducing (OrderHom.toFun : (A →o B) → (A → B)) where
  eq_induced := rfl

variable {A} in
@[continuity]
protected lemma continuous_apply (a : A) : Continuous (fun (f : A →o B) ↦ f a) :=
  (continuous_apply _).comp continuous_induced_dom

variable {A B}

lemma continuous_iff {X : Type*} [TopologicalSpace X] (f : X → (A →o B)) :
    Continuous f ↔ ∀ (a : A), Continuous (fun x ↦ f x a) := by
  rw [(isInducing A B).continuous_iff, continuous_pi_iff]
  rfl

instance [T2Space B] : T2Space (A →o B) :=
  T2Space.of_injective_continuous (f := OrderHom.toFun)
    (fun _ _ h ↦ by ext; apply congr_fun h) (by continuity)

end OrderHom
