import TopCatModelCategory.SSet.Rev
import TopCatModelCategory.SSet.StandardSimplex

universe u

open CategoryTheory Simplicial

namespace SSet

namespace stdSimplex

def revIso {n : SimplexCategory} : (stdSimplex.{u}.obj n).rev ≅ stdSimplex.obj n :=
  NatIso.ofComponents (fun d ↦ Equiv.toIso (revObjEquiv.trans
    { toFun x := objEquiv.symm (SimplexCategory.rev.map (objEquiv x))
      invFun x := objEquiv.symm (SimplexCategory.rev.map (objEquiv x))
      left_inv x := objEquiv.injective (by aesop)
      right_inv x := objEquiv.injective (by aesop) })) (fun f ↦ by
        ext g
        apply objEquiv.injective
        ext i : 3
        simp [rev, objEquiv, stdSimplex, uliftFunctor, revObjEquiv, revFunctor])

@[simp]
lemma revObjEquiv_revIso_inv_app {n d : ℕ}
    (x : Δ[n] _⦋d⦌) (i : Fin (d + 1)):
    revObjEquiv (revIso.inv.app _ x) i = (x i.rev).rev := by
  rfl

def subcomplexRev {n : SimplexCategory}
    (A : (stdSimplex.{u}.obj n).Subcomplex) :
      (stdSimplex.obj n).Subcomplex :=
  A.rev.preimage revIso.inv

lemma mem_subcomplexRev_obj_iff {n : SimplexCategory}
    (A : (stdSimplex.{u}.obj n).Subcomplex) {d : SimplexCategoryᵒᵖ}
    (x : (stdSimplex.obj n).obj d) :
    x ∈ (subcomplexRev A).obj d ↔ revObjEquiv (revIso.inv.app d x) ∈ A.obj d := by
  simp [subcomplexRev]

@[simp]
lemma subcomplexRev_iSup {n : SimplexCategory} {ι : Type*}
    (A : ι → (stdSimplex.{u}.obj n).Subcomplex) :
    subcomplexRev (iSup A) = ⨆ i, subcomplexRev (A i) := by
  ext
  simp [mem_subcomplexRev_obj_iff]


lemma subcomplexRev_face {n : ℕ} (S : Finset (Fin (n + 1))) :
    subcomplexRev (face S) = face (Finset.image Fin.rev S) := by
  ext ⟨d⟩ x
  induction' d using SimplexCategory.rec with d
  simp [mem_subcomplexRev_obj_iff]
  refine ⟨fun hx i ↦ ?_, fun hx i ↦ ?_⟩
  · exact ⟨_, hx i.rev, by simp⟩
  · obtain ⟨a, h₁, h₂⟩ := hx i.rev
    simpa [← h₂]

lemma subcomplexRev_face_singleton_compl {n : ℕ} (i : Fin (n + 1)) :
    subcomplexRev (face {i}ᶜ) = face {i.rev}ᶜ := by
  rw [subcomplexRev_face]
  congr
  ext j
  rw [← not_iff_not]
  simp only [Finset.mem_image, Finset.mem_compl, Finset.mem_singleton, not_exists, not_and,
    Decidable.not_not]
  constructor
  · intro h
    have this := h j.rev
    simp only [Fin.rev_rev, not_true_eq_false, imp_false, Decidable.not_not] at this
    rw [← Fin.rev_inj, this, Fin.rev_rev]
  · aesop

lemma subcomplexRev_horn {n : ℕ} (i : Fin (n + 1)) :
    subcomplexRev (horn n i) = horn n i.rev := by
  simp only [horn_eq_iSup, subcomplexRev_iSup, subcomplexRev_face_singleton_compl]
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro j hj
    exact le_iSup (f := fun (k : ({i.rev}ᶜ : Set _)) ↦ face {k.1}ᶜ) ⟨j.rev, by simpa⟩
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro j hj
    obtain ⟨j, rfl⟩ := Fin.rev_surjective j
    exact le_iSup (f := fun (k : ({i}ᶜ : Set _)) ↦ face {k.1.rev}ᶜ) ⟨j, by simpa using hj⟩

end stdSimplex

end SSet
