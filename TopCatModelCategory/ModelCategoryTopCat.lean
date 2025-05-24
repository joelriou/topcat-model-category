import TopCatModelCategory.TopPackage
import TopCatModelCategory.TopCat.W
import TopCatModelCategory.TopCat.T1Inclusion
import TopCatModelCategory.SSet.Finite
import TopCatModelCategory.SSet.Skeleton
import TopCatModelCategory.SSet.KanComplexKeyLemma
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SingularSet

open HomotopicalAlgebra CategoryTheory MorphismProperty

namespace TopCat

namespace modelCategory

open SSet.modelCategoryQuillen

def I : MorphismProperty TopCat.{0} :=
  ofHoms (fun n ↦ SSet.toTop.map (SSet.boundary.{0} n).ι)

def J : MorphismProperty TopCat.{0} :=
  ⨆ n, ofHoms (fun i ↦ SSet.toTop.map (SSet.horn.{0} (n + 1) i).ι)

lemma rlp_I_iff {E B : TopCat} (p : E ⟶ B) :
    I.rlp p ↔ SSet.modelCategoryQuillen.I.rlp (toSSet.map p) := by
  constructor
  · rintro hp _ _ _ ⟨i⟩
    rw [← sSetTopAdj.hasLiftingProperty_iff]
    exact hp _ ⟨i⟩
  · rintro hp _ _ _ ⟨i⟩
    rw [sSetTopAdj.hasLiftingProperty_iff]
    exact hp _ ⟨i⟩

lemma rlp_J_iff {E B : TopCat} (p : E ⟶ B) :
    J.rlp p ↔ SSet.modelCategoryQuillen.J.rlp (toSSet.map p) := by
  constructor
  · intro hp _ _ _ h
    rw [← sSetTopAdj.hasLiftingProperty_iff]
    apply hp
    simp only [SSet.modelCategoryQuillen.J, J, iSup_iff] at h ⊢
    obtain ⟨n, ⟨i⟩⟩ := h
    exact ⟨n, ⟨i⟩⟩
  · intro hp _ _u _ h
    simp only [J, iSup_iff] at h
    obtain ⟨n, ⟨i⟩⟩ := h
    rw [sSetTopAdj.hasLiftingProperty_iff]
    apply hp
    simp only [SSet.modelCategoryQuillen.J, iSup_iff]
    exact ⟨n, ⟨i⟩⟩

instance : IsSmall.{0} I := by dsimp [I]; infer_instance
instance : IsSmall.{0} J := by dsimp [J]; infer_instance

instance (X : TopCat.{0}) : IsFibrant (TopCat.toSSet.obj X) := by
  sorry

instance (T : SSet.{0}) [T.IsFinite] :
    CompactSpace (SSet.toTop.obj T) := by
  sorry

lemma t₁Inclusions_sSet_toObj_map_of_mono {X Y : SSet.{0}} (i : X ⟶ Y) [Mono i] :
    t₁Inclusions (SSet.toTop.map i) := by
  sorry

def packageTopCat : TopPackage.{0} TopCat.{0} where
  I' := TopCat.modelCategory.I
  J' := TopCat.modelCategory.J
  S' := Set.range (fun (X : {(X : SSet.{0}) | SSet.IsFinite X}) ↦ SSet.toTop.obj X)
  src_I_le_S' := by
    rintro _ _ _ ⟨i⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop]
    exact ⟨_, inferInstance, rfl⟩
  src_J_le_S' := by
    rintro _ _ _ hf
    simp only [J, iSup_iff] at hf
    obtain ⟨_, ⟨_⟩⟩ := hf
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, exists_prop]
    exact ⟨_, inferInstance, rfl⟩
  rlp_I'_le_rlp_J' := by
    intro _ _ f hf _ _ g hg
    rw [rlp_I_iff, SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp] at hf
    simp only [J, iSup_iff] at hg
    obtain ⟨n, ⟨i⟩⟩ := hg
    rw [sSetTopAdj.hasLiftingProperty_iff]
    exact hf _ (monomorphisms.infer_property _)
  -- the next two sorries were formalised in Lean 3 by Reid Barton
  preservesColimit' := by
    rintro _ ⟨⟨T, hT⟩, rfl⟩ X Y f hf
    have : T.IsFinite := hT
    refine TopCat.t₁Inclusions.preservesColimit_coyoneda_obj_of_compactSpace
      ((hf.transfiniteCompositionOfShape).ofLE ?_) _
    simp only [ofHoms_homFamily, pushouts_le_iff, coproducts_le_iff, sup_le_iff]
    constructor
    · intro _ _ _ ⟨n⟩
      apply t₁Inclusions_sSet_toObj_map_of_mono
    · intro _ _ _ h
      simp only [J, iSup_iff] at h
      obtain ⟨n, ⟨i⟩⟩ := h
      apply t₁Inclusions_sSet_toObj_map_of_mono
  infiniteCompositions_le_W' := by
    sorry
  fibration_is_trivial_iff' {X Y} p hp := by
    rw [rlp_J_iff, ← SSet.modelCategoryQuillen.fibration_iff] at hp
    rw [weakEquivalence_iff, rlp_I_iff, SSet.KanComplex.weakEquivalence_iff_of_fibration]

scoped instance instModelCategory : ModelCategory TopCat.{0} :=
  packageTopCat.modelCategoryCat

lemma weakEquivalence_iff_of_fibration {X Y : TopCat.{0}} (f : X ⟶ Y) [Fibration f] :
    (ofHoms (fun n ↦ SSet.toTop.map (SSet.boundary.{0} n).ι)).rlp f ↔
      WeakEquivalence f :=
  packageTopCat.I_rlp_iff_weakEquivalence_of_fibration f

open SSet

instance (n : ℕ) : Cofibration (toTop.map (boundary n).ι) := by
  rw [HomotopicalAlgebra.cofibration_iff]
  apply MorphismProperty.le_llp_rlp
  constructor

lemma trivialCofibrations_eq_llp_rlp :
    trivialCofibrations TopCat =
      (⨆ n, ofHoms (fun i ↦ SSet.toTop.map (SSet.horn.{0} (n + 1) i).ι)).rlp.llp :=
  packageTopCat.trivialCofibrations_eq_llp_rlp_J

end modelCategory

open modelCategory

end TopCat
