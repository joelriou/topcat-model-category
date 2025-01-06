import Mathlib.AlgebraicTopology.SimplicialSet.Basic

universe u

open CategoryTheory Category Simplicial Limits Opposite

lemma SimplexCategory.congr_toOrderHom_apply {m n : SimplexCategory} {f g : m ⟶ n} (h : f = g)
    (x : Fin (m.len + 1)) : f.toOrderHom x = g.toOrderHom x := by rw [h]

namespace SSet

variable (X : SSet.{u})

def Degenerate (n : ℕ) : Set (X _[n]) :=
  setOf (fun x ↦ ∃ (m : SimplexCategory) (_ : m.len < n) (f : ([n] : SimplexCategory) ⟶ m),
    x ∈ Set.range (X.map f.op))

def NonDegenerate (n : ℕ) : Set (X _[n]) := (X.Degenerate n)ᶜ

@[simp]
lemma degenerate_zero : X.Degenerate 0 = ⊥ := by
  ext x
  simp only [Set.bot_eq_empty, Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, hm, _⟩
  simp at hm

@[simp]
lemma nondegenerate_zero : X.NonDegenerate 0 = ⊤ := by
  simp [NonDegenerate]

variable {n : ℕ}

lemma mem_nondegenerate_iff_not_mem_degenerate (x : X _[n]) :
    x ∈ X.NonDegenerate n ↔ x ∉ X.Degenerate n := Iff.rfl

lemma mem_degenerate_iff_non_mem_nondegenerate (x : X _[n]) :
    x ∈ X.Degenerate n ↔ x ∉ X.NonDegenerate n := by
  simp [NonDegenerate]

lemma σ_mem_degenerate (i : Fin (n + 1)) (x : X _[n]) :
    X.σ i x ∈ X.Degenerate (n + 1) :=
  ⟨[n], by dsimp; omega, SimplexCategory.σ i, Set.mem_range_self x⟩

lemma mem_degenerate_iff (x : X _[n]) :
    x ∈ X.Degenerate n ↔ ∃ (m : ℕ) (_ : m < n)
      (f : ([n] : SimplexCategory) ⟶ [m]) (_ : Epi f),
        x ∈ Set.range (X.map f.op) := by
  trans ∃ (m : SimplexCategory) (_ : m.len < n)
      (f : ([n] : SimplexCategory) ⟶ m) (_ : Epi f),
        x ∈ Set.range (X.map f.op)
  · constructor
    · rintro ⟨m, hm, f, hf, hx⟩
      rw [← image.fac f, op_comp] at hx
      have := SimplexCategory.len_le_of_mono (f := image.ι f) inferInstance
      exact ⟨_, by omega, factorThruImage f, inferInstance, by aesop⟩
    · rintro ⟨m, hm, f, hf, hx⟩
      exact ⟨m, hm, f, hx⟩
  · constructor
    · rintro ⟨m, hm, f, hf, hx⟩
      exact ⟨m.len, hm, f, hf, hx⟩
    · rintro ⟨m, hm, f, hf, hx⟩
      exact ⟨[m], hm, f, hf, hx⟩

lemma degenerate_eq_iUnion_range_σ :
    X.Degenerate (n + 1) = ⨆ (i : Fin (n + 1)), Set.range (X.σ i) := by
  ext x
  constructor
  · intro hx
    rw [mem_degenerate_iff] at hx
    obtain ⟨m, hm, f, hf, y, rfl⟩ := hx
    obtain ⟨i, θ, rfl⟩ := SimplexCategory.eq_σ_comp_of_not_injective f (fun hf ↦ by
      have := SimplexCategory.le_of_mono (f := f) (by
        rwa [SimplexCategory.mono_iff_injective])
      omega)
    aesop
  · intro hx
    simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨i, y, rfl⟩ := hx
    apply σ_mem_degenerate

lemma exists_non_degenerate (x : X _[n]) :
    ∃ (m : ℕ) (f : ([n] : SimplexCategory) ⟶ [m]) (_ : Epi f)
      (y : X.NonDegenerate m), x = X.map f.op y := by
  revert x
  induction n with
  | zero =>
      intro x
      exact ⟨0, 𝟙 _, inferInstance, ⟨x, by simp⟩, by simp⟩
  | succ n hn =>
      intro x
      by_cases hx : x ∈ X.NonDegenerate (n + 1)
      · exact ⟨n + 1, 𝟙 _, inferInstance, ⟨x, hx⟩, by simp⟩
      · simp only [← mem_degenerate_iff_non_mem_nondegenerate,
          degenerate_eq_iUnion_range_σ, Set.iSup_eq_iUnion,
          Set.mem_iUnion, Set.mem_range] at hx
        obtain ⟨i, y, rfl⟩ := hx
        obtain ⟨m, f, hf, z, rfl⟩ := hn y
        exact ⟨_, SimplexCategory.σ i ≫ f, inferInstance, z, by simp; rfl⟩

lemma isIso_of_non_degenerate (x : X.NonDegenerate n)
    {m : SimplexCategory} (f : ([n] : SimplexCategory) ⟶ m) [Epi f]
    (y : X.obj (op m)) (hy : X.map f.op y = x) :
    IsIso f := by
  obtain ⟨x, hx⟩ := x
  induction' m using SimplexCategory.rec with m
  rw [mem_nondegenerate_iff_not_mem_degenerate] at hx
  by_contra!
  refine hx ⟨_ ,?_, f, y, hy⟩
  by_contra!
  obtain rfl : m = n :=
    le_antisymm (SimplexCategory.len_le_of_epi (f := f) inferInstance) this
  obtain rfl := SimplexCategory.eq_id_of_epi f
  exact this inferInstance

namespace unique_non_degenerate

section

variable {X} {x : X _[n]}
  {m₁ m₂ : ℕ} {f₁ : ([n] : SimplexCategory) ⟶ [m₁]} (hf₁ : SplitEpi f₁)
  (y₁ : X.NonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
  (f₂ : ([n] : SimplexCategory) ⟶ [m₂])
  (y₂ : X _[m₂]) (hy₂ : x = X.map f₂.op y₂)

def g := hf₁.section_ ≫ f₂

variable {f₂ y₁ y₂}

include hf₁ hy₁ hy₂

lemma map_g_op_y₂ : X.map (g hf₁ f₂).op y₂ = y₁ := by
  dsimp [g]
  rw [FunctorToTypes.map_comp_apply, ← hy₂, hy₁, ← FunctorToTypes.map_comp_apply, ← op_comp,
    SplitEpi.id, op_id, FunctorToTypes.map_id_apply]

lemma isIso_factorThruImage_g :
    IsIso (factorThruImage (g hf₁ f₂)) := by
  have := map_g_op_y₂ hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂), op_comp, FunctorToTypes.map_comp_apply] at this
  exact X.isIso_of_non_degenerate y₁ (factorThruImage (g hf₁ f₂)) _ this

lemma mono_g : Mono (g hf₁ f₂) := by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  rw [← image.fac (g hf₁ f₂)]
  infer_instance

lemma le : m₁ ≤ m₂ := by
  have := isIso_factorThruImage_g hf₁ hy₁ hy₂
  exact SimplexCategory.len_le_of_mono
    (f := factorThruImage (g hf₁ f₂) ≫ image.ι _) inferInstance

end

section

variable {X} {x : X _[n]} {m : ℕ} {f₁ : ([n] : SimplexCategory) ⟶ [m]}
  {y₁ : X.NonDegenerate m} (hy₁ : x = X.map f₁.op y₁)
  {f₂ : ([n] : SimplexCategory) ⟶ [m]} {y₂ : X _[m]} (hy₂ : x = X.map f₂.op y₂)

include hy₁ hy₂

lemma g_eq_id (hf₁ : SplitEpi f₁) : g hf₁ f₂ = 𝟙 _ := by
  have := mono_g hf₁ hy₁ hy₂
  apply SimplexCategory.eq_id_of_mono

end

end unique_non_degenerate
section

open unique_non_degenerate
lemma unique_non_degenerate₁ (x : X _[n])
    {m₁ m₂ : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m₁]) [Epi f₁]
    (y₁ : X.NonDegenerate m₁) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ([n] : SimplexCategory) ⟶ [m₂]) [Epi f₂]
    (y₂ : X.NonDegenerate m₂) (hy₂ : x = X.map f₂.op y₂) : m₁ = m₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  obtain ⟨⟨hf₂⟩⟩ := isSplitEpi_of_epi f₂
  exact le_antisymm (le hf₁ hy₁ hy₂) (le hf₂ hy₂ hy₁)

lemma unique_non_degenerate₂ (x : X _[n])
    {m : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m]) [Epi f₁]
    (y₁ : X.NonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ([n] : SimplexCategory) ⟶ [m])
    (y₂ : X.NonDegenerate m) (hy₂ : x = X.map f₂.op y₂) : y₁ = y₂ := by
  obtain ⟨⟨hf₁⟩⟩ := isSplitEpi_of_epi f₁
  ext
  simpa [g_eq_id hy₁ hy₂ hf₁] using (map_g_op_y₂ hf₁ hy₁ hy₂).symm

lemma unique_non_degenerate₃ (x : X _[n])
    {m : ℕ} (f₁ : ([n] : SimplexCategory) ⟶ [m]) [Epi f₁]
    (y₁ : X.NonDegenerate m) (hy₁ : x = X.map f₁.op y₁)
    (f₂ : ([n] : SimplexCategory) ⟶ [m])-- [Epi f₂]
    (y₂ : X.NonDegenerate m) (hy₂ : x = X.map f₂.op y₂) : f₁ = f₂ := by
  ext x : 3
  suffices ∃ (hf₁ : SplitEpi f₁), hf₁.section_.toOrderHom (f₁.toOrderHom x) = x by
    obtain ⟨hf₁, hf₁'⟩ := this
    dsimp at hf₁'
    simpa [g, hf₁'] using (SimplexCategory.congr_toOrderHom_apply (g_eq_id hy₁ hy₂ hf₁)
      (f₁.toOrderHom x)).symm
  obtain ⟨⟨hf⟩⟩ := isSplitEpi_of_epi f₁
  let α (y : Fin (m + 1)) : Fin (n + 1) :=
    if y = f₁.toOrderHom x then x else hf.section_.toOrderHom y
  have hα₁ (y : Fin (m + 1)) : f₁.toOrderHom (α y) = y := by
    dsimp [α]
    split_ifs with hy
    · rw [hy]
    · apply SimplexCategory.congr_toOrderHom_apply hf.id
  have hα₂ : Monotone α := by
    rintro y₁ y₂ h
    by_contra! h'
    suffices y₂ ≤ y₁ by simp [show y₁ = y₂ by omega] at h'
    simpa only [hα₁, hα₁] using f₁.toOrderHom.monotone h'.le
  exact ⟨{ section_ := SimplexCategory.Hom.mk ⟨α, hα₂⟩, id := by ext : 3; apply hα₁ },
    by simp [α]⟩

end

end SSet
