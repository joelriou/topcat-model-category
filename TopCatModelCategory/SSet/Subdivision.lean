import Mathlib.CategoryTheory.Limits.Presheaf
import TopCatModelCategory.SSet.NonemptyFiniteChains
import TopCatModelCategory.SSet.NonDegenerateSimplices
import TopCatModelCategory.ULift

universe v u

open CategoryTheory Limits

instance : HasColimitsOfSize.{u, u} SSet.{u} := by
  dsimp [SSet, SimplicialObject]
  infer_instance

instance : HasColimitsOfSize.{0, u} SSet.{u} := by
  dsimp [SSet, SimplicialObject]
  infer_instance

def PartOrd.uliftFUnctor : PartOrd.{u} ⥤ PartOrd.{max u v} where
  obj X := .of (ULift.{v} X)
  map f := PartOrd.ofHom ⟨fun x ↦ ULift.up (f (ULift.down x)),
    fun x y hxy ↦ f.hom.monotone hxy⟩

namespace SimplexCategory

def toPartOrd : SimplexCategory ⥤ PartOrd.{u} :=
  skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ⋙
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.uliftFUnctor

@[simp]
lemma toPartOrd_obj (n : SimplexCategory) :
    toPartOrd.{u}.obj n = .of (ULift.{u} (Fin (n.len + 1))) := by
  rfl

@[simp]
lemma toPartOrd_map_apply {n m : SimplexCategory} (f : n ⟶ m)
    (i : (Fin (n.len + 1))) :
    toPartOrd.{u}.map f (ULift.up i) = ULift.up (f i) := by
  rfl

noncomputable def sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd.{u} ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

end SimplexCategory

namespace SSet

noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.{u}.leftKanExtension SimplexCategory.sd

noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

noncomputable def sdExAdjunction : sd.{u} ⊣ ex.{u} :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

namespace stdSimplex

noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  Presheaf.isExtensionAlongULiftYoneda _

def partOrdIso : stdSimplex.{u} ≅ SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents (fun n ↦ by
    induction' n using SimplexCategory.rec with n
    exact isoNerve _ (orderIsoULift _).symm)

end stdSimplex

instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd.{u}))

@[simps!]
noncomputable def B : SSet.{u} ⥤ SSet.{u} := SSet.N.functor ⋙ PartOrd.nerveFunctor

open Functor in
noncomputable def stdSimplexCompBIso : stdSimplex.{u} ⋙ B ≅ SimplexCategory.sd :=
  isoWhiskerRight stdSimplex.partOrdIso _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    isoWhiskerLeft _ (isoWhiskerRight PartOrd.nerveFunctorCompNIso PartOrd.nerveFunctor)

noncomputable def sdToB : sd.{u} ⟶ B :=
  sd.{u}.descOfIsLeftKanExtension stdSimplex.sdIso.inv _ stdSimplexCompBIso.{u}.inv

end SSet
