import TopCatModelCategory.ModelCategorySSet

universe u

open HomotopicalAlgebra

example : ModelCategory TopCat.{u} := TopCat.modelCategory.inst

example : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.inst

#print axioms TopCat.modelCategory.inst
#print axioms SSet.modelCategoryQuillen.inst

#check CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument

#check TopCat.fibration_of_isOpenCover
#check SSet.instFibrationTopCatMapToTop_topCatModelCategory

#check SSet.KanComplex.weakEquivalence_iff_of_fibration
#check TopCat.modelCategory.weakEquivalence_iff_of_fibration
#check SSet.modelCategoryQuillen.weakEquivalence_iff_of_fibration
