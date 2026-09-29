module

public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

universe v u

noncomputable def Ordinal.toTypeTypeOrderIso
    {α : Type u} [LinearOrder α] [IsWellOrder α (· < · )] :
    (Ordinal.type (α := α) (· < · )).toType ≃o α := by
  apply OrderIso.ofRelIsoLT
  apply Nonempty.some
  rw [← Ordinal.type_eq]
  simp only [Ordinal.type_toType]

noncomputable def Ordinal.liftToTypeOrderIso (o : Ordinal.{v}) :
    (Ordinal.lift.{u} o).toType ≃o o.toType := by
  apply OrderIso.ofRelIsoLT
  apply Nonempty.some
  rw [← lift_type_eq.{max u v, v, u},
    type_toType, type_toType, lift_id, Ordinal.lift_umax.{v, u}]

noncomputable irreducible_def Cardinal.aleph0OrdToTypeOrderIso :
    Cardinal.aleph0.{u}.ord.toType ≃o ℕ := by
  rw [Cardinal.ord_aleph0]
  exact (Ordinal.liftToTypeOrderIso _).trans
    (OrderIso.ofRelIsoLT (Nonempty.some (by simp [← Ordinal.type_eq])))
