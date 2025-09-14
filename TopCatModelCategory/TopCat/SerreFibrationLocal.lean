import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.SmallObject
import TopCatModelCategory.TopCat.ToTopSdIso
import TopCatModelCategory.SmallObject

open CategoryTheory Simplicial HomotopicalAlgebra

universe u

namespace SSet

open modelCategoryQuillen SmallObject

namespace anodyneExtensions

attribute [local instance] Cardinal.aleph0_isRegular
  Cardinal.orderbot_aleph0_ord_to_type

variable {X Y E B : SSet.{u}}
  {i : X ⟶ Y}

lemma hasLiftingPropertyFixedBot_of_simplices_aux
    {α : Type*} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
    (hi : RelativeCellComplex.{u} (fun (i : α) ↦ J.homFamily) i)
    (p : E ⟶ B) (b : Y ⟶ B)
    (h : ∀ ⦃n : ℕ⦄ (y : Y _⦋n + 1⦌) (i : Fin (n + 2)),
      HasLiftingPropertyFixedBot (horn (n + 1) i).ι p (yonedaEquiv.symm y ≫ b)) :
    HasLiftingPropertyFixedBot i p b := by
  sorry

lemma hasLiftingPropertyFixedBot_of_simplices
    (hi : anodyneExtensions i) (p : E ⟶ B) (b : Y ⟶ B)
    (h : ∀ ⦃n : ℕ⦄ (y : Y _⦋n + 1⦌) (i : Fin (n + 2)),
      HasLiftingPropertyFixedBot (horn (n + 1) i).ι p (yonedaEquiv.symm y ≫ b)) :
    HasLiftingPropertyFixedBot i p b := by
  replace hi : J.rlp.llp i := fun _ _ p hp ↦ hi _ (by rwa [fibrations_eq])
  obtain ⟨Y', r, i', fac, ⟨hi'⟩⟩ :=
    exists_retract_relativeCellComplex_of_llp_rlp hi Cardinal.aleph0.{u}
  replace hi' := hasLiftingPropertyFixedBot_of_simplices_aux hi' p (r.r ≫ b) (by
    intro n u i
    rw [← Category.assoc, yonedaEquiv_symm_comp]
    apply h)
  intro t sq
  have sq' : CommSq t i' p (r.r ≫ b) := ⟨by
    rw [sq.w, ← reassoc_of% fac, reassoc_of% r.retract]⟩
  have := hi' t sq'
  exact ⟨⟨
    { l := r.i ≫ sq'.lift
      fac_left := by rw [reassoc_of% fac, sq'.fac_left] } ⟩⟩

end anodyneExtensions

end SSet
