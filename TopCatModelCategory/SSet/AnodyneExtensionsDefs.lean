import TopCatModelCategory.SSet.Horn
import TopCatModelCategory.SSet.CategoryWithFibrations
import TopCatModelCategory.SSet.ChosenFiniteProducts
import TopCatModelCategory.SSet.SimplexCategory
import TopCatModelCategory.SSet.NonDegenerateProdSimplex
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

open HomotopicalAlgebra CategoryTheory Limits SSet.modelCategoryQuillen MonoidalCategory
  Simplicial Opposite

universe v u

namespace SSet

def anodyneExtensions : MorphismProperty SSet.{u} :=
  (fibrations _).llp

instance : anodyneExtensions.{u}.IsMultiplicative := by
  dsimp [anodyneExtensions]
  infer_instance

instance : anodyneExtensions.{u}.RespectsIso := by
  dsimp [anodyneExtensions]
  infer_instance

instance : anodyneExtensions.{u}.IsStableUnderCobaseChange := by
  dsimp [anodyneExtensions]
  infer_instance

instance : MorphismProperty.IsStableUnderTransfiniteComposition.{v} anodyneExtensions.{u} := by
  dsimp [anodyneExtensions]
  constructor
  infer_instance

instance : MorphismProperty.IsStableUnderCoproducts.{u} anodyneExtensions.{u} where
  isStableUnderCoproductsOfShape :=
    MorphismProperty.llp_isStableUnderCoproductsOfShape _

namespace anodyneExtensions

lemma hasLeftLiftingProperty {A B : SSet.{u}} {f : A ⟶ B} (hf : anodyneExtensions f)
    ⦃X Y : SSet.{u}⦄ (p : X ⟶ Y) [Fibration p] :
    HasLiftingProperty f p :=
  hf _ (mem_fibrations p)

lemma exists_lift_of_isFibrant {A B X : SSet.{u}} (f : A ⟶ X) [IsFibrant X] {g : A ⟶ B}
    (hg : anodyneExtensions g) :
    ∃ (h : B ⟶ X), g ≫ h = f := by
  have := hg.hasLeftLiftingProperty
  have sq : CommSq f g (terminal.from _) (terminal.from _) := ⟨by simp⟩
  exact ⟨sq.lift, by simp⟩

lemma of_isIso {X Y : SSet.{u}} (f : X ⟶ Y) [IsIso f] :
    anodyneExtensions f :=
  MorphismProperty.of_isIso _ _

lemma horn_ι_mem (n : ℕ) (i : Fin (n + 2)) :
    anodyneExtensions (horn.{u} (n + 1) i).ι := by
  apply MorphismProperty.le_llp_rlp
  simp only [J, MorphismProperty.iSup_iff]
  exact ⟨n, ⟨i⟩⟩

end anodyneExtensions

def hornOneUnionProdInclusions : MorphismProperty SSet.{u} :=
  ⨆ (i : Fin 2) (X : SSet.{u}),
    .ofHoms (fun (A : X.Subcomplex) ↦ (A.unionProd (horn.{u} 1 i)).ι)

lemma mem_hornOneUnionProdInclusions (i : Fin 2) {X : SSet.{u}} (A : X.Subcomplex) :
    hornOneUnionProdInclusions (A.unionProd (horn.{u} 1 i)).ι := by
  simp only [hornOneUnionProdInclusions, MorphismProperty.iSup_iff]
  exact ⟨i, X, ⟨A⟩⟩

end SSet
