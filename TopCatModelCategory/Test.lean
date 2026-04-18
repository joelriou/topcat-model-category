import TopCatModelCategory.ModelCategorySSet

universe u

open HomotopicalAlgebra

example : ModelCategory TopCat.{u} := TopCat.modelCategory.inst

example : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.inst

#print axioms TopCat.modelCategory.inst
#print axioms SSet.modelCategoryQuillen.inst

#check TopCat.fibration_of_isOpenCover
#check SSet.AffineMap
#check SSet.AffineMap.sd
#check SSet.AffineMap.sdIter
#check SSet.AffineMap.mesh_sd_le
#check SSet.toTopSdIso
#check SemiSimplexCategory.sdIso


#check CategoryTheory.MorphismProperty.IsCardinalForSmallObjectArgument
#check TopCat.fibration_of_isOpenCover
#check SSet.instFibrationTopCatMapToTop_topCatModelCategory
#check SSet.KanComplex.weakEquivalence_iff_of_fibration
#check TopCat.modelCategory.weakEquivalence_iff_of_fibration
#check SSet.modelCategoryQuillen.weakEquivalence_iff_of_fibration
