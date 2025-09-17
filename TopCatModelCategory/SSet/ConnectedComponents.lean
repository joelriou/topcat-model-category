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

lemma subsingleton_π₀_of_subcomplex (S : X.Subcomplex)
    (hS₀ : ∀ (x : X _⦋1⦌), X.δ 1 x ∈ S.obj _ ↔ X.δ 0 x ∈ S.obj _)
    (hS : ∀ (x : X _⦋1⦌), X.δ 1 x ∈ S.obj _ → X.δ 0 x ∈ S.obj _ → x ∈ S.obj _) :
    Function.Injective (mapπ₀ S.ι) := by
  have h₁ {x y : X _⦋0⦌} (h : Relation.EqvGen π₀Rel x y) :
      x ∈ S.obj _ ↔ y ∈ S.obj _ := by
    induction h with
    | rel x y h =>
      obtain ⟨s, rfl, rfl⟩ := h
      rw [hS₀]
    | refl => tauto
    | symm y x h hyx => rw [hyx]
    | trans x y z hxy hyz hxy' hyz' => rw [hxy', hyz']
  have h₂ {x y : X _⦋0⦌} (h : Relation.EqvGen π₀Rel x y) :
      ∀ (hx : x ∈ S.obj _),
        Relation.EqvGen (π₀Rel (X := S)) ⟨x, hx⟩ ⟨y, (h₁ h).1 hx⟩ := by
    intro hx
    induction h with
    | rel x y h =>
      have hy := (h₁ (.rel _ _ h)).1 hx
      obtain ⟨s, rfl, rfl⟩ := h
      exact .rel _ _ ⟨⟨s, hS _ hx hy⟩, rfl, rfl⟩
    | refl =>
      exact .refl _
    | symm y x h hyx =>
      exact (hyx _).symm
    | trans x y z hxy hyz hxy' hyz' =>
      apply (hxy' hx).trans
      apply hyz' ((h₁ hxy).1 hx)
  intro x y h
  obtain ⟨⟨x, hx⟩, rfl⟩ := x.mk_surjective
  obtain ⟨⟨y, hy⟩, rfl⟩ := y.mk_surjective
  simp only [mapπ₀_mk, Subpresheaf.ι_app, π₀.mk_eq_mk_iff] at h ⊢
  exact h₂ h hx

instance (c : X.π₀) : Subsingleton (c.component.toSSet.π₀) := by
  obtain ⟨x₀, rfl⟩ := c.mk_surjective
  constructor
  intro p₁ p₂
  apply subsingleton_π₀_of_subcomplex
  · intro s
    have hs := π₀.sound s rfl rfl
    simp only [component, Opposite.op_unop, Fin.isValue, Set.mem_setOf_eq]
    refine ⟨fun h α ↦ ?_, fun h α ↦ ?_⟩
    all_goals
      obtain rfl := Subsingleton.elim α (𝟙 _)
      simpa [← hs] using h (𝟙 _)
  · intro s hs₁ hs₀
    simp [component] at hs₀ hs₁ ⊢
    intro α
    have : Mono α := by
      rw [SimplexCategory.mono_iff_injective]
      rintro x y h
      fin_cases x
      fin_cases y
      rfl
    obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono α
    fin_cases i
    · simpa using hs₀ (𝟙 _)
    · simpa using hs₁ (𝟙 _)
  · obtain ⟨⟨x₁, hx₁⟩, rfl⟩ := p₁.mk_surjective
    obtain ⟨⟨x₂, hx₂⟩, rfl⟩ := p₂.mk_surjective
    simp [component] at hx₁ hx₂
    replace hx₁ := hx₁ (𝟙 _)
    replace hx₂ := hx₂ (𝟙 _)
    simp only [op_id, FunctorToTypes.map_id_apply] at hx₁ hx₂
    simp [hx₁, hx₂]

instance (c : X.π₀) : (c.component.toSSet).Nonempty := by
  obtain ⟨x, rfl⟩ := c.mk_surjective
  refine ⟨⟨x, ?_⟩⟩
  simp [component]
  intro f
  obtain rfl := Subsingleton.elim f (𝟙 _)
  simp

instance (c : X.π₀) : IsConnected (c.component.toSSet) where

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
