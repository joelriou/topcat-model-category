import TopCatModelCategory.ModelCategorySSet

universe u

open HomotopicalAlgebra

example : ModelCategory TopCat.{u} := TopCat.modelCategory.inst

example : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.inst

#print axioms TopCat.modelCategory.inst
#print axioms SSet.modelCategoryQuillen.inst
