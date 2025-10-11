import TopCatModelCategory.SSet.AnodyneExtensions
import TopCatModelCategory.SSet.PairingSubdivision
import TopCatModelCategory.SSet.Subdivision

universe v u

open CategoryTheory SSet Simplicial Opposite HomotopicalAlgebra

instance (X : Type u) [Nontrivial X] :
    Nontrivial (ULift.{v} X) where
  exists_pair_ne := by
    obtain ⟨x, y, h⟩ := exists_pair_ne X
    exact ⟨ULift.up x, ULift.up y, by simpa⟩

lemma Set.complSingleton_le_iff {X : Type u} (S : Set X) (x₀ : X) :
    {x₀}ᶜ ⊆ S ↔ S = .univ ∨ S = {x₀}ᶜ := by
  constructor
  · intro hS
    obtain hS | rfl := hS.lt_or_eq
    · obtain ⟨y, hy₁, hy₂⟩ : ∃ (y : X), y ∈ S ∧ y ∉ ({x₀}ᶜ : Set X) := by
        by_contra!
        have h : S = {x₀}ᶜ := le_antisymm (fun _ hx ↦ this _ hx) hS.le
        simp [h] at hS
      obtain rfl : y = x₀ := by simpa using hy₂
      apply Or.inl (le_antisymm (by simp) ?_)
      simp only [← union_compl_self {y}, le_eq_subset, union_subset_iff]
      exact ⟨by simpa, hS.le⟩
    · simp
  · rintro (rfl | rfl) <;> simp

lemma SSet.mem_horn_iff_not_subset {n : ℕ} {i : Fin (n + 1)}
    {d : SimplexCategoryᵒᵖ} (x : (Δ[n] : SSet.{u}).obj d) :
    x ∈ Λ[n, i].obj d ↔ ¬ ({i}ᶜ ⊆ Set.range (stdSimplex.objEquiv x)) := by
  obtain ⟨d⟩ := d
  induction d using SimplexCategory.rec with | _ d
  simp [horn_eq_iSup]
  constructor
  · rintro ⟨j, hj, hj'⟩ h
    obtain ⟨k, rfl⟩ := @h j (by simpa)
    exact hj' k rfl
  · intro h
    by_contra!
    exact h this

lemma SSet.mem_range_B_map_ι_app_iff {X : SSet.{u}} (A : X.Subcomplex)
    {d : ℕ} (x : (B.obj X) _⦋d⦌) :
    x ∈ Set.range ((B.map A.ι).app (op ⦋d⦌)) ↔
      (x.obj (Fin.last d)).simplex ∈ A.obj _ := by
  constructor
  · generalize hz : x.obj (Fin.last d) = z
    rintro ⟨y, rfl⟩
    obtain ⟨s, hs, rfl⟩ := z.mk'_surjective
    dsimp at hz
    rw [N.ext_iff, toS_mapN_of_mono, N.mk'_toS] at hz
    subst hz
    exact (y.obj (Fin.last d)).simplex.2
  · intro h
    refine ⟨Monotone.functor (f := fun i ↦ N.toSubcomplex (x.obj i) ?_) ?_, ?_⟩
    · simp only [← Subpresheaf.ofSection_le_iff] at h ⊢
      refine le_trans ?_ h
      rw [← N.le_iff]
      exact x.monotone i.le_last
    · intro i j h
      simpa [N.toSubcomplex_le_toSubcomplex_iff] using x.monotone h
    · apply Preorder.nerveExt (by aesop)

namespace PartialOrder

variable {X : Type u} [LinearOrder X] (x₀ : X)

@[simps]
def horn : (nerve X).Subcomplex where
  obj n := setOf (fun s ↦ ¬ ({x₀}ᶜ ⊆ Set.range s.obj))
  map f x hx h' := hx (h'.trans (by
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩))

def hornArrowIso (n : ℕ) (i : Fin (n + 2)) :
    Arrow.mk (horn.{u} (ULift.up i)).ι ≅ Arrow.mk (SSet.horn (n + 1) i).ι :=
  (Subcomplex.congrArrowι' ((stdSimplex.isoNerve' _ (orderIsoULift _).symm)) (by
    ext ⟨d⟩ x
    induction d using SimplexCategory.rec with | _ d
    simp [SSet.mem_horn_iff_not_subset, not_iff_not]
    constructor
    · rintro h j hj
      obtain ⟨k, hk⟩ := @h (ULift.up j) (by simpa)
      exact ⟨k, by rwa [ULift.ext_iff] at hk⟩
    · rintro h j hj
      obtain ⟨k, hk⟩ := @h (ULift.down j) (by aesop)
      exact ⟨k, by rwa [ULift.ext_iff]⟩)).symm


namespace NonemptyFiniteChains

variable [Fintype X] [Nontrivial X]

noncomputable def hornArrowIsoB' :
    Arrow.mk (Subcomplex.range (B.map (PartialOrder.horn x₀).ι)).ι ≅
      Arrow.mk (NonemptyFiniteChains.horn x₀).ι :=
  Subcomplex.congrArrowι'
    (PartOrd.nerveFunctor.mapIso (PartOrd.nerveFunctorCompNIso.app (.of X))) (by
      ext ⟨n⟩ x
      induction n using SimplexCategory.rec with | _ n
      dsimp at x
      conv_lhs =>
        simp [PartOrd.nerveFunctorCompNIso, Functor.mapComposableArrows]
        rw [mem_horn_iff'']
        simp [ofN, ofS]
      dsimp
      rw [SSet.mem_range_B_map_ι_app_iff]
      simp only [SimplexCategory.len_mk, N.functor_obj_coe, nerve_obj, horn_obj, Set.mem_setOf_eq]
      rw [not_iff_not]
      constructor
      · intro h i hi
        simpa using @h i (by simpa)
      · intro h i hi
        simpa using @h i (by simpa using hi))

noncomputable def hornArrowIsoB :
    Arrow.mk (B.map (PartialOrder.horn x₀).ι) ≅
      Arrow.mk (NonemptyFiniteChains.horn x₀).ι :=
  (by exact Arrow.isoMk (asIso (toRangeSubcomplex _)) (Iso.refl _)) ≪≫
    hornArrowIsoB' _

noncomputable def hornArrowIso :
    Arrow.mk (NonemptyFiniteChains.horn x₀).ι ≅
      sd.map (PartialOrder.horn x₀).ι :=
  (hornArrowIsoB x₀).symm ≪≫
    (Arrow.isoMk (asIso (sdToB.app _)) (asIso (sdToB.app _))).symm

end NonemptyFiniteChains

lemma anodyneExtensions_sd_map_horn_ι [Fintype X] [Nontrivial X] :
    anodyneExtensions (sd.map (PartialOrder.horn x₀).ι) :=
  (anodyneExtensions.arrow_mk_iso_iff
    (NonemptyFiniteChains.hornArrowIso x₀)).1
      (NonemptyFiniteChains.horn.pairing x₀).anodyneExtensions

end PartialOrder

namespace SSet

lemma anodyneExtensions_sd_map_horn_ι (n : ℕ) (i : Fin (n + 2)) :
    anodyneExtensions (sd.{u}.map (horn (n + 1) i).ι) :=
  (anodyneExtensions.arrow_mk_iso_iff
    (sd.mapArrow.mapIso (PartialOrder.hornArrowIso.{u} n i))).1
      (PartialOrder.anodyneExtensions_sd_map_horn_ι _)

section

variable {X Y : SSet.{u}} (f : X ⟶ Y)

open modelCategoryQuillen MorphismProperty

instance [Fibration f] : Fibration (ex.map f) := by
  rw [fibration_iff]
  intro _ _ g hg
  simp only [J, iSup_iff] at hg
  obtain ⟨n, ⟨i⟩⟩ := hg
  rw [← sdExAdjunction.hasLiftingProperty_iff]
  exact (anodyneExtensions_sd_map_horn_ι n i).hasLeftLiftingProperty f

lemma anodyneExtensions.sd_map {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : anodyneExtensions f) :
    anodyneExtensions (sd.map f) := by
  intro E S p hp
  rw [← HomotopicalAlgebra.fibration_iff] at hp
  rw [sdExAdjunction.hasLiftingProperty_iff]
  exact hf.hasLeftLiftingProperty _

end

end SSet
