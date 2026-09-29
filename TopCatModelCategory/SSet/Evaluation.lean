module

public import TopCatModelCategory.SSet.Subcomplex
public import TopCatModelCategory.Set

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet.Subcomplex

@[simps]
def evaluation (X : SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    X.Subcomplex ⥤ Set (X.obj j) where
  obj A := A.obj j
  map f := CategoryTheory.homOfLE (leOfHom f j)

instance {J : Type*} [Category J] {X : SSet.{u}} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subcomplex.toPresheafFunctor (X := X)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone (CompleteLattice.colimitCocone F).isColimit
      (evaluationJointlyReflectsColimits _ (fun j ↦
        IsColimit.ofIsoColimit (isColimitOfPreserves Set.functorToTypes
          (CompleteLattice.colimitCocone (F ⋙ evaluation _ j)).isColimit)
            (Cocones.ext (Set.functorToTypes.mapIso (eqToIso (by aesop))))))

end SSet.Subcomplex
