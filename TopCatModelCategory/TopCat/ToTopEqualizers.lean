import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings

open CategoryTheory Limits Simplicial Topology

namespace SSet

namespace Subcomplex

abbrev equalizer {X Y : SSet.{u}} {A : X.Subcomplex}
    (f g : (A : SSet) ⟶ Y) : X.Subcomplex :=
  Subpresheaf.equalizer f g

variable {X Y : SSet.{u}} (f g : X ⟶ Y)

abbrev equalizer' : X.Subcomplex :=
  equalizer ((topIso X).hom ≫ f) ((topIso X).hom ≫ g)

lemma equalizer'_condition :
    (equalizer' f g).ι ≫ f = (equalizer' f g).ι ≫ g := by
  ext n ⟨x, hx⟩
  simpa [equalizer', equalizer, Subpresheaf.equalizer] using hx

abbrev fork' : Fork f g := Fork.ofι _ (equalizer'_condition f g)

def isLimitFork' : IsLimit (fork' f g) := by
  refine (IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_).1
    (Subpresheaf.equalizer.forkIsLimit ((topIso X).hom ≫ f) ((topIso X).hom ≫ g))
  · exact parallelPair.ext (topIso _) (Iso.refl _) (by simp) (by simp)
  · exact Fork.ext (Iso.refl _)

end Subcomplex

namespace toTopPreservesEqualizers

variable {X Y : SSet.{u}} (f g : X ⟶ Y)

def equalizerTop : Set (|X|) := { x | toTop.map f x = toTop.map g x }

lemma mem_equalizerTop_iff (e : |X|) :
    e ∈ equalizerTop f g ↔ toTop.map f e = toTop.map g e :=
  Iff.rfl

noncomputable abbrev fork : Fork (toTop.map f) (toTop.map g) :=
  Fork.ofι (P := .of (equalizerTop f g))
    (ι := ConcreteCategory.ofHom ⟨Subtype.val, continuous_subtype_val⟩) (by ext x; exact x.2)

noncomputable def isLimitFork : IsLimit (fork f g) :=
  Fork.IsLimit.mk _
    (fun s ↦ ConcreteCategory.ofHom
      ⟨fun x ↦ ⟨s.ι x, congr_fun (Functor.congr_map (forget _) s.condition) x⟩,
        Continuous.subtype_mk s.ι.hom.continuous _⟩)
    (fun _ ↦ rfl)
    (fun s m hm ↦ by
      ext x
      rw [Subtype.ext_iff]
      exact congr_fun ((Functor.congr_map (forget _)) hm) x)

noncomputable def toEqualizerTop : |Subcomplex.equalizer' f g| ⟶ TopCat.of (equalizerTop f g) :=
  Fork.IsLimit.lift (isLimitFork f g) (k := toTop.map (Subcomplex.ι _)) (by
    rw [← Functor.map_comp, ← Functor.map_comp, Subcomplex.equalizer'_condition])

lemma isEmbedding : IsEmbedding (toEqualizerTop f g) := by
  dsimp
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  exact (t₁Inclusions_toObj_map_of_mono (Subcomplex.equalizer' f g).ι).toIsEmbedding

lemma surjective : Function.Surjective (toEqualizerTop f g) := sorry

lemma isHomeomorph : IsHomeomorph (toEqualizerTop f g) :=
  (isEmbedding f g).isHomeomorph (surjective f g)

instance : IsIso (toEqualizerTop f g) :=
  (TopCat.isoOfHomeo (isHomeomorph f g).homeomorph).isIso_hom

instance : PreservesLimit (parallelPair f g) toTop.{u} :=
  preservesLimit_of_preserves_limit_cone (Subcomplex.isLimitFork' f g)
    ((isLimitMapConeForkEquiv _ _).2
      (IsLimit.ofIsoLimit (isLimitFork f g) (Iso.symm (Fork.ext (asIso (toEqualizerTop f g))))))

end toTopPreservesEqualizers

instance toTopPreservesEqualizers :
    PreservesLimitsOfShape WalkingParallelPair toTop.{u} where
  preservesLimit := preservesLimit_of_iso_diagram _ (diagramIsoParallelPair _).symm

end SSet
