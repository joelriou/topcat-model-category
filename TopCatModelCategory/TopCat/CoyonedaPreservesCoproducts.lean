import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.CoconeTop

universe v u

open CategoryTheory Limits Opposite
instance PathConnectedSpace.ulift (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    PathConnectedSpace (ULift.{v} X) :=
  Equiv.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous

namespace TopCat

instance {J : Type v} (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (F : J → TopCat.{u}) :
    PreservesColimit (Discrete.functor F) (coyoneda.obj (op (TopCat.of X))) where
  preserves {c : Cofan _} hc :=
    ⟨(isColimitMapCoconeCofanMkEquiv (g := c.inj) _).2 (by
      refine ((Types.isColimit_iff_coconeTypesIsColimit ..).2 ?_).some
      have hc' := (isColimitMapCoconeCofanMkEquiv (forget _) (g := c.inj)).1
          (isColimitOfPreserves (forget _) hc)
      let x₀ : X := Classical.arbitrary _
      apply Functor.CofanTypes.isColimit_mk
      · intro f
        dsimp at f ⊢
        replace hc := (TopCat.isColimit_iff_coconeTopIsColimit _).1 ⟨hc⟩
        obtain ⟨⟨i, g⟩, hg⟩ :=
          (Functor.CofanTop.bijective_continuousMap_of_isColimit_of_connectedSpace hc X).2 f.hom
        refine ⟨i, TopCat.ofHom g, ?_⟩
        ext x
        exact DFunLike.congr_fun hg x
      · intro j f g h
        apply (forget _).map_injective
        dsimp at f g h ⊢
        ext x
        exact Types.cofanInj_injective_of_isColimit hc' j (ConcreteCategory.congr_hom h x)
      · intro i j f g h
        exact Types.eq_cofanInj_apply_eq_of_isColimit
          hc' _ _ (ConcreteCategory.congr_hom h x₀))⟩

instance (J : Type v) (X : Type u) [TopologicalSpace X] [PathConnectedSpace X] :
    PreservesColimitsOfShape (Discrete J) (coyoneda.obj (op (TopCat.of X))) where
  preservesColimit := preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

open Simplicial

instance (J : Type v) (n : SimplexCategory) :
    PreservesColimitsOfShape (Discrete J)
      (coyoneda.obj (op (SimplexCategory.toTop.{u}.obj n))) := by
  dsimp [SimplexCategory.toTop, uliftFunctor]
  infer_instance

instance (J : Type v) :
    PreservesColimitsOfShape (Discrete J) toSSet.{u} where
  preservesColimit := ⟨fun hc ↦ ⟨evaluationJointlyReflectsColimits _
    (fun ⟨n⟩ ↦ (IsColimit.equivOfNatIsoOfIso
      (NatIso.ofComponents (fun ⟨j⟩ ↦ Equiv.ulift.symm.toIso)) _  _
      (Cocones.ext Equiv.ulift.symm.toIso)).1
      (isColimitOfPreserves (coyoneda.obj (op (SimplexCategory.toTop.obj n))) hc))⟩⟩

end TopCat
