import TopCatModelCategory.TopCat.Adj
import TopCatModelCategory.TopCat.BoundaryClosedEmbeddings
import TopCatModelCategory.TopCat.ToTopDecomposition

open CategoryTheory Limits Simplicial Topology

namespace SSet

lemma exists_n {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    ∃ (t : X.N) (g : ⦋n⦌ ⟶ ⦋t.dim⦌) (_ : Epi g), X.map g.op t.simplex = x := by
  obtain ⟨d, g, _, ⟨y, hy⟩, rfl⟩ := X.exists_nonDegenerate x
  exact ⟨N.mk _ hy, g, inferInstance, rfl⟩

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

lemma mem_equalizer'_iff {n : SimplexCategoryᵒᵖ} (x : X.obj n) :
    x ∈ (equalizer' f g).obj _ ↔ f.app _ x = g.app _ x := by
  simp [equalizer', equalizer, Subpresheaf.equalizer]

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

@[simp]
lemma toEqualizerTop_coe (x : |Subcomplex.equalizer' f g|) :
    (toEqualizerTop f g x).1 = toTop.map (Subcomplex.ι _) x := rfl

lemma isEmbedding : IsEmbedding (toEqualizerTop f g) := by
  dsimp
  rw [← IsEmbedding.subtypeVal.of_comp_iff]
  exact (t₁Inclusions_toObj_map_of_mono (Subcomplex.equalizer' f g).ι).toIsEmbedding

lemma surjective : Function.Surjective (toEqualizerTop f g) := by
  rintro ⟨e, he⟩
  rw [mem_equalizerTop_iff] at he
  obtain ⟨⟨s, p⟩, rfl⟩ := sigmaEquivToTop.surjective e
  dsimp at he
  suffices f.app _ s.simplex = g.app _ s.simplex by
    exact ⟨toTopObjToTop (n := s.dim) ⟨s.simplex, by
      rwa [Subcomplex.mem_equalizer'_iff]⟩ p.1, by
        rw [Subtype.ext_iff, toEqualizerTop_coe, toTopObjToTop_naturality]
        rfl⟩
  obtain ⟨t, q, _, ht⟩ := SSet.exists_n (f.app _ s.simplex)
  obtain ⟨u, r, _, hu⟩ := SSet.exists_n (g.app _ s.simplex)
  rw [sigmaToTop_naturality f s p t q ht.symm,
    sigmaToTop_naturality g s p u r hu.symm] at he
  replace he := sigmaToTop_bijective.1 he
  obtain rfl : t = u := congr_arg Sigma.fst he
  obtain rfl : q = r := by
    simp only [Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq, true_and] at he
    exact stdSimplex.toTopMap_apply_injective_of_epi_of_mem_interior he p.2
  rw [← ht, hu]

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
