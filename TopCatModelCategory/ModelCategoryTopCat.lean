import TopCatModelCategory.SSet.KanComplexKeyLemma
import TopCatModelCategory.SSet.KanComplexWColimits
import TopCatModelCategory.TopPackage
import TopCatModelCategory.TopCat.HornDeformationRetract
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings

open HomotopicalAlgebra CategoryTheory MorphismProperty Limits Opposite

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

-- could be generalized to more general well ordered types...
instance :
    (t₁Inclusions ⊓ weakEquivalences TopCat).IsStableUnderTransfiniteCompositionOfShape ℕ where
  le := by
    rintro X Y f ⟨hf⟩
    refine ⟨t₁Inclusions.isT₁Inclusion_of_transfiniteCompositionOfShape
      (hf.ofLE inf_le_left), ?_⟩
    rw [weakEquivalences_eq, inverseImage_iff]
    apply (SSet.KanComplex.W.isStableUnderColimitsOfShape ℕ).colimitsOfShape_le
    have : PreservesColimit hf.F toSSet :=
        preservesColimit_of_preserves_colimit_cocone hf.isColimit
          (evaluationJointlyReflectsColimits _ (fun ⟨n⟩ ↦ by
            have : PreservesColimit hf.F _ :=
              t₁Inclusions.preservesColimit_coyoneda_obj_of_compactSpace
                (hf.ofLE inf_le_left) (.of n.toTopObj)
            exact isColimitOfPreserves
              (coyoneda.obj (op (TopCat.of n.toTopObj))) hf.isColimit))
    have hc₁ := isColimitConstCocone ℕ (toSSet.obj X)
    let c₂ := toSSet.mapCocone { pt := Y, ι := hf.incl }
    let φ : (Functor.const _).obj (toSSet.obj X) ⟶ hf.F ⋙ toSSet :=
      { app n := toSSet.map (hf.isoBot.inv ≫ hf.F.map (homOfLE bot_le))
        naturality n₁ n₂ g := by
          dsimp
          simp only [Category.id_comp, ← Functor.map_comp, Category.assoc]
          rfl }
    have hf' (n : ℕ) : SSet.KanComplex.W (toSSet.map (hf.F.map (homOfLE bot_le : ⊥ ⟶ n))) := by
      induction n with
      | zero => simpa using SSet.KanComplex.W.id _
      | succ n hn =>
        rw [← homOfLE_comp bot_le (Nat.le_add_right n 1), Functor.map_comp,
          Functor.map_comp]
        exact SSet.KanComplex.W.comp _ _ hn (hf.map_mem n (by simp)).2
    have : toSSet.map f = hc₁.desc (Cocone.mk _ (φ ≫ c₂.ι)) := hc₁.hom_ext (fun n ↦ by
      rw [hc₁.fac]
      dsimp [φ, c₂]
      simp only [Category.id_comp, ← Functor.map_comp]
      congr 1
      simpa using hf.fac.symm)
    rw [this]
    refine ⟨_, _, _, _, _, isColimitOfPreserves toSSet hf.isColimit, _, fun n ↦ ?_⟩
    dsimp [φ]
    rw [Functor.map_comp]
    exact MorphismProperty.comp_mem _ _ _ (.of_iso _) (hf' _)

lemma deformationRetracts_le_weakEquivalences :
    deformationRetracts ≤ weakEquivalences TopCat.{0} := by
  rintro X Y _ ⟨r, rfl⟩
  rw [weakEquivalences_eq, inverseImage_iff]
  exact SSet.KanComplex.W.homotopyEquivHom (.ofDeformationRetract r.toSSet)

lemma I_le_t₁Inclusions : TopCat.modelCategory.I ≤ t₁Inclusions := by
  intro _ _ _ ⟨n⟩
  apply SSet.t₁Inclusions_toObj_map_of_mono

lemma J_le_t₁Inclusions : TopCat.modelCategory.J ≤ t₁Inclusions := by
  intro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  apply SSet.t₁Inclusions_toObj_map_of_mono

lemma J_le_deformationRetracts : TopCat.modelCategory.J ≤ deformationRetracts := by
  intro _ _ _ h
  simp only [J, iSup_iff] at h
  obtain ⟨n, ⟨i⟩⟩ := h
  exact ⟨SSet.horn.deformationRetractToTopMap i, by simp⟩

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
  preservesColimit' := by
    rintro _ ⟨⟨T, hT⟩, rfl⟩ X Y f hf
    have : T.IsFinite := hT
    refine TopCat.t₁Inclusions.preservesColimit_coyoneda_obj_of_compactSpace
      ((hf.transfiniteCompositionOfShape).ofLE ?_) _
    simp only [ofHoms_homFamily, pushouts_le_iff, coproducts_le_iff, sup_le_iff]
    exact ⟨I_le_t₁Inclusions, J_le_t₁Inclusions⟩
  infiniteCompositions_le_W' := by
    refine (transfiniteCompositionsOfShape_monotone ℕ ?_).trans
      (((t₁Inclusions ⊓ weakEquivalences TopCat).transfiniteCompositionsOfShape_le ℕ).trans
        (by simp))
    trans t₁Inclusions ⊓ deformationRetracts
    · simp only [le_inf_iff, pushouts_le_iff, coproducts_le_iff]
      exact ⟨J_le_t₁Inclusions, J_le_deformationRetracts⟩
    · exact inf_le_inf (by simp) deformationRetracts_le_weakEquivalences
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
