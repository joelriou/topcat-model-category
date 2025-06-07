import TopCatModelCategory.SSet.Subcomplex
import TopCatModelCategory.SSet.PiZero

universe u

open CategoryTheory Simplicial Limits

namespace SSet

variable {X : SSet.{u}}

namespace π₀

lemma congr_mk_map {n : SimplexCategoryᵒᵖ} (x : X.obj n) (α β : ⦋0⦌ ⟶ n.unop) :
    π₀.mk (X.map α.op x) = π₀.mk (X.map β.op x) := by
  obtain ⟨n⟩ := n
  induction' n using SimplexCategory.rec with n
  let f (i : Fin (n + 1)) : X.π₀ := π₀.mk (X.map (⦋0⦌.const ⦋n⦌ i).op x)
  have hf (i : Fin n) : f i.castSucc = f i.succ := by
    refine π₀.sound (X.map (SimplexCategory.mkOfLe _ _ i.castSucc_le_succ).op x) ?_ ?_
    all_goals
    · dsimp [SimplicialObject.δ]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      apply congr_fun
      congr 2
      ext j : 3
      fin_cases j
      rfl
  dsimp at α β
  have h (γ : ⦋0⦌ ⟶ ⦋n⦌) : ∃ i, γ = ⦋0⦌.const ⦋n⦌ i :=
    ⟨γ 0, by ext a : 3; fin_cases a; rfl⟩
  obtain ⟨i, rfl⟩ := h α
  obtain ⟨j, rfl⟩ := h β
  suffices ∀ i, f i = f 0 from (this i).trans (this j).symm
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i hi => rw [← hf, hi]

def component (c : X.π₀) : X.Subcomplex where
  obj n := setOf (fun s ↦ ∀ (α : ⦋0⦌ ⟶ n.unop), π₀.mk (X.map α.op s) = c)
  map {n m} f s hs α := by simpa using hs (α ≫ f.unop)

lemma min_component (c₁ c₂ : X.π₀) (h : c₁ ≠ c₂) :
    c₁.component ⊓ c₂.component = ⊥ := by
  ext ⟨n⟩ x
  dsimp [component]
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨h₁, h₂⟩
  exact h ((h₁ (⦋0⦌.const n 0)).symm.trans (h₂ (⦋0⦌.const n 0)))

variable (X)

lemma iSup_component : ⨆ (c : X.π₀), c.component = ⊤ := by
  ext ⟨n⟩ x
  simp only [Subpresheaf.iSup_obj, Set.mem_iUnion, Subpresheaf.top_obj, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  exact ⟨π₀.mk (X.map (⦋0⦌.const n 0).op x), fun i ↦ congr_mk_map _ _ _⟩

lemma coproductDiagram :
    CompleteLattice.CoproductDiagram ⊤ (fun (c : X.π₀) ↦ c.component) where
  iSup_eq := iSup_component X
  min_eq i j := by
    by_cases hij : i = j
    · subst hij
      simp
    · rw [min_component _ _ hij, if_neg hij]

abbrev cofan : Cofan (fun (c : X.π₀) ↦ (c.component : SSet)) :=
  Cofan.mk X (fun c ↦ c.component.ι)

noncomputable def isColimitCofan : IsColimit (cofan X) :=
  Subcomplex.isColimitCofan' (coproductDiagram X)

end π₀

end SSet
