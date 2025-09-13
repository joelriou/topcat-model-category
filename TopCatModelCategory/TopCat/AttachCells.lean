import TopCatModelCategory.TopCat.ClosedEmbeddings
import TopCatModelCategory.SSet.Monomorphisms

universe w w' t v u

open HomotopicalAlgebra CategoryTheory Limits

namespace HomotopicalAlgebra

namespace AttachCells

section

variable {C : Type*} [Category C] {α : Type t} {A B : α → C} {g : (i : α) → A i ⟶ B i}
  {X₀ X : C} {f : X₀ ⟶ X} (hf : AttachCells g f)

open MorphismProperty in
lemma colimitsOfShape_m :
    (MorphismProperty.ofHoms g).colimitsOfShape (Discrete hf.ι) hf.m :=
  colimitsOfShape.mk' _ _ _ _ hf.isColimit₁ hf.isColimit₂
    (Discrete.natTrans (fun _ ↦ g _)) (fun _ ↦ .mk _) _ (fun _ ↦ hf.hm _)

end

variable {α : Type t} {A B : α → Type u} {g : (i : α) → A i ⟶ B i}
  {X₀ X : Type u} {f : X₀ ⟶ X} (hf : AttachCells g f)
  (hg : ∀ i, Function.Injective (g i))

lemma w_apply (x : hf.cofan₁.pt) : f (hf.g₁ x) = hf.g₂ (hf.m x) :=
    congr_fun hf.isPushout.w x

section

variable (i : hf.ι)

def fullCell : Set X := Set.range (hf.cell i)

def boundaryCell : Set X := Set.range (Function.comp (hf.cell i) (g (hf.π i)))

def interiorCell : Set X := hf.fullCell i \ hf.boundaryCell i

lemma disjoint_boundaryCell_interiorCell :
    Disjoint (hf.boundaryCell i) (hf.interiorCell i) :=
  Set.disjoint_sdiff_right

lemma boundaryCell_subset : hf.boundaryCell i ⊆ hf.fullCell i := by
  rintro _ ⟨x, rfl⟩
  exact ⟨g _ x, rfl⟩

lemma interiorCell_subset : hf.interiorCell i ⊆ hf.fullCell i := Set.diff_subset

@[simp]
lemma boundaryCell_union_interiorCell :
    hf.boundaryCell i ∪ hf.interiorCell i = hf.fullCell i :=
  Set.union_diff_cancel (boundaryCell_subset hf i)

open MorphismProperty in
include hg in
lemma injective_m : Function.Injective hf.m := by
  rw [← mono_iff_injective, ← monomorphisms.iff]
  refine colimitsOfShape_le _ (colimitsOfShape_monotone ?_ _ _ (hf.colimitsOfShape_m))
  rintro _ _ _ ⟨_⟩
  rw [monomorphisms.iff, mono_iff_injective]
  apply hg

variable {i} in
lemma hm_apply (x : A (hf.π i)) :
    hf.m (hf.cofan₁.inj i x) = hf.cofan₂.inj i (g (hf.π i) x) :=
  congr_fun (hf.hm i) x

variable {i} in
lemma cell_apply (a : B (hf.π i)) :
    hf.cell i a = hf.g₂ (hf.cofan₂.inj i a) := rfl

lemma cofan₂_inj_mem_range_m_iff {i : hf.ι} (x : B (hf.π i)) :
    hf.cofan₂.inj i x ∈ (Set.range hf.m) ↔ x ∈ (Set.range (g (hf.π i))) := by
  constructor
  · rintro ⟨y, hx⟩
    obtain ⟨j, z, rfl⟩ := Types.jointly_surjective_of_isColimit_cofan hf.isColimit₁ y
    rw [hm_apply, Types.cofanInj_apply_eq_iff_of_isColimit hf.isColimit₂] at hx
    obtain ⟨rfl, rfl⟩ := hx
    simp
  · rintro ⟨a, rfl⟩
    rw [← hf.hm_apply]
    apply Set.mem_range_self

include hg in
lemma cell_mem_boundaryCell_iff {i : hf.ι} (x : B (hf.π i)) :
    hf.cell i x ∈ hf.boundaryCell i ↔ x ∈ Set.range (g (hf.π i)) := by
  constructor
  · rintro ⟨a, ha⟩
    dsimp [cell_apply] at ha
    rw [← hm_apply, ← w_apply] at ha
    obtain ⟨y, h₁, h₂⟩ :=
      Types.exists_of_inl_eq_inr_of_isPushout hf.isPushout.flip (hf.injective_m hg) _ _ ha.symm
    obtain ⟨j, a', rfl⟩ := Types.jointly_surjective_of_isColimit_cofan hf.isColimit₁ y
    rw [hm_apply, Types.cofanInj_apply_eq_iff_of_isColimit hf.isColimit₂] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    simp
  · rintro ⟨a, rfl⟩
    simp [boundaryCell]

end

noncomputable def equivComplRangeM :
    (Σ (i : hf.ι), ((Set.range (g (hf.π i)))ᶜ : Set _)) ≃ ((Set.range hf.m)ᶜ : Set _) :=
  Equiv.ofBijective (fun ⟨i, x, hx⟩ ↦ ⟨hf.cofan₂.inj i x, by
    simpa only [Set.mem_compl_iff, cofan₂_inj_mem_range_m_iff]⟩) (by
      constructor
      · rintro ⟨i, x, hx⟩ ⟨j, y, hy⟩ h
        rw [Subtype.ext_iff, Types.cofanInj_apply_eq_iff_of_isColimit hf.isColimit₂] at h
        obtain rfl : i = j := h.1
        obtain rfl : y = x := by simpa using h
        rfl
      · rintro ⟨x, hx⟩
        obtain ⟨i, x, rfl⟩ := Types.jointly_surjective_of_isColimit_cofan hf.isColimit₂ x
        rw [Set.mem_compl_iff, cofan₂_inj_mem_range_m_iff] at hx
        exact ⟨⟨i, ⟨x, by rwa [Set.mem_compl_iff]⟩⟩, rfl⟩)

@[simp]
lemma equivComplRangeM_apply_coe (x) :
    (hf.equivComplRangeM x).1 = hf.cofan₂.inj x.1 x.2 := rfl

noncomputable def equiv :
    (Σ (i : hf.ι), ((Set.range (g (hf.π i)))ᶜ : Set _)) ≃ ((Set.range f)ᶜ : Set _) :=
  hf.equivComplRangeM.trans
    (Types.equivOfIsPushoutOfInjective hf.isPushout.flip (hf.injective_m hg))

lemma equiv_apply {i : hf.ι} (x : ((Set.range (g (hf.π i)))ᶜ : Set _)) :
    hf.equiv hg ⟨i, x⟩ = ⟨hf.cell i x, (hf.equiv hg ⟨i, x⟩).2⟩ := rfl

@[simp]
lemma equiv_apply_coe {i : hf.ι} (x : ((Set.range (g (hf.π i)))ᶜ : Set _)) :
    ↑(hf.equiv hg ⟨i, x⟩) = hf.cell i x := rfl

section

include hg

lemma interiorCell_eq_range (i : hf.ι) :
    hf.interiorCell i = Set.image (hf.cell i) (Set.range (g (hf.π i)))ᶜ := by
  ext x
  constructor
  · simp [interiorCell, fullCell, boundaryCell]
    rintro b rfl hb
    refine ⟨b, ?_, rfl⟩
    rintro a rfl
    exact hb a rfl
  · intro hx
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_range, not_exists] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    simpa [interiorCell, fullCell, hf.cell_mem_boundaryCell_iff hg a]

lemma cell_injective_on {i : hf.ι} {b₁ b₂ : B (hf.π i)}
    (hb : hf.cell i b₁ = hf.cell i b₂)
    (hb₁ : b₁ ∉ Set.range (g (hf.π i))) (hb₂ : b₂ ∉ Set.range (g (hf.π i))) :
    b₁ = b₂ := by
  simpa using (equiv hf hg).injective (a₁ := ⟨i, ⟨b₁, hb₁⟩⟩) (a₂ := ⟨i, ⟨b₂, hb₂⟩⟩)
    (by rwa [Subtype.ext_iff])

lemma disjoint_interiorCell {i i' : hf.ι} (hi : i ≠ i') :
    Disjoint (hf.interiorCell i) (hf.interiorCell i') := by
  rw [Set.disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  rw [interiorCell_eq_range _ hg] at hx hx'
  obtain ⟨b, hb₁, hb₂⟩ := hx
  obtain ⟨b', hb'₁, hb'₂⟩ := hx'
  exact hi (congr_arg Sigma.fst ((equiv hf hg).injective
    (a₁ := ⟨i, b, hb₁⟩) (a₂ := ⟨i', b', hb'₁⟩)
    (by simp_rw [Subtype.ext_iff, equiv_apply_coe, hb₂, hb'₂])))

end

end AttachCells

end HomotopicalAlgebra
