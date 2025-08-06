import TopCatModelCategory.SSet.StandardSimplex

universe u

open CategoryTheory Simplicial

namespace SSet

variable {X : SSet.{u}}

@[simp]
lemma Subcomplex.ofSimplex_map {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
    (x : X _⦋m⦌) :
    ofSimplex (X.map f.op x) = ofSimplex x := by
  apply le_antisymm
  · rw [Subpresheaf.ofSection_le_iff]
    exact ⟨_, rfl⟩
  · rw [Subpresheaf.ofSection_le_iff]
    have := isSplitEpi_of_epi f
    exact ⟨(section_ f).op, by
      rw [← FunctorToTypes.map_comp_apply, ← op_comp,
        IsSplitEpi.id, op_id, FunctorToTypes.map_id_apply]⟩

variable (X) in
protected def S : Type u := Sigma (fun n ↦ X _⦋n⦌)

namespace S

abbrev mk {n : ℕ} (x : X _⦋n⦌) : X.S := ⟨_, x⟩

def map {Y : SSet.{u}} (f : X ⟶ Y) (x : X.S) : Y.S :=
  ⟨x.1, f.app _ x.2⟩

lemma dim_eq_of_mk_eq {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (h : S.mk x = S.mk y) : n = m :=
  congr_arg Sigma.fst h

@[simp]
lemma eq_iff {n : ℕ} (x y : X _⦋n⦌) :
    S.mk x = S.mk y ↔ x = y := by
  rw [Sigma.ext_iff]
  simp

lemma mk_map_eq_iff_of_mono {n m : ℕ} (x : X _⦋n⦌)
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] :
    S.mk (X.map f.op x) = S.mk x ↔ IsIso f := by
  constructor
  · intro h
    obtain rfl := S.dim_eq_of_mk_eq h
    obtain rfl := SimplexCategory.eq_id_of_mono f
    infer_instance
  · intro hf
    obtain rfl : n = m :=
      le_antisymm
        (SimplexCategory.len_le_of_epi (f := f) inferInstance)
        (SimplexCategory.len_le_of_mono (f := f) inferInstance)
    obtain rfl := SimplexCategory.eq_id_of_isIso f
    simp

instance : Preorder X.S where
  le x y := Subcomplex.ofSimplex x.2 ≤ Subcomplex.ofSimplex y.2
  le_refl _ := le_refl (α := Subcomplex X) _
  le_trans _ _ _ := le_trans (α := Subcomplex X)

lemma le_iff {x y : X.S} : x ≤ y ↔ Subcomplex.ofSimplex x.2 ≤ Subcomplex.ofSimplex y.2 :=
  Iff.rfl

end S

end SSet
