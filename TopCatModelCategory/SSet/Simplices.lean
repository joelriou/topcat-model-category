/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import TopCatModelCategory.SSet.StandardSimplex

/-!
# The type of simplices of a simplicial set

In this file, we define the type `X.S` of simplices of a simplicial set `X`,
where a simplex consists of the data of `dim : ℕ` and `simplex : X _⦋dim⦌`.
We endow this type with a preorder defined by
`x ≤ y ↔ Subcomplex.ofSimplex x.simplex ≤ Subcomplex.ofSimplex y.simplex`.

## TODO (@joelriou)

* Extend the `S` structure to as do define the type of nondegenerate
simplices of a simplicial set `X`, and also the type of nondegenerate
simplices of a simplicial set `X` which do not belong to a given subcomplex.

-/

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
/-- The type of simplices of a simpliciat set `X`. -/
structure S where
  /-- the dimension of the simplex -/
  {dim : ℕ}
  /-- the simplex -/
  simplex : X _⦋dim⦌

namespace S

lemma mk_surjective {s : X.S} :
    ∃ (n : ℕ) (x : X _⦋n⦌), s = mk x :=
  ⟨s.1, s.2, rfl⟩

/-- The image of a simplex by a morphism of simplicial sets. -/
def map {Y : SSet.{u}} (f : X ⟶ Y) (s : X.S) : Y.S :=
  S.mk (f.app _ s.2)

lemma dim_eq_of_eq {s t : X.S} (h : s = t) :
    s.dim = t.dim :=
  congr_arg dim h

lemma dim_eq_of_mk_eq {n m : ℕ} {x : X _⦋n⦌} {y : X _⦋m⦌}
    (h : S.mk x = S.mk y) : n = m :=
  dim_eq_of_eq h

section

variable (s : X.S) {d : ℕ} (hd : s.dim = d)

/-- When `s : X.S` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
@[simps dim]
def cast : X.S where
  dim := d
  simplex := _root_.cast (by simp only [hd]) s.simplex

lemma cast_eq_self : s.cast hd = s := by
  obtain ⟨d, _, rfl⟩ := s.mk_surjective
  obtain rfl := hd
  rfl

@[simp]
lemma cast_simplex_rfl : (s.cast rfl).simplex = s.simplex := rfl

end

lemma eq_iff' (s t : X.S) :
    s = t ↔ ∃ (h : s.dim = t.dim), (s.cast h).2 = t.2 :=
  ⟨by rintro rfl; exact ⟨rfl, rfl⟩, fun ⟨h₁, h₂⟩ ↦ by
    obtain ⟨_, _, rfl⟩ := s.mk_surjective
    obtain ⟨_, _, rfl⟩ := t.mk_surjective
    aesop⟩

@[simp]
lemma eq_iff {n : ℕ} (x y : X _⦋n⦌) :
    S.mk x = S.mk y ↔ x = y := by
  simp [eq_iff']

instance : Preorder X.S where
  le x y := Subcomplex.ofSimplex x.2 ≤ Subcomplex.ofSimplex y.2
  le_refl _ := le_refl (α := Subcomplex X) _
  le_trans _ _ _ := le_trans (α := Subcomplex X)

lemma le_iff {x y : X.S} : x ≤ y ↔ Subcomplex.ofSimplex x.2 ≤ Subcomplex.ofSimplex y.2 :=
  Iff.rfl

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

attribute [-simp] SSet.S.mk.injEq

end S

attribute [-simp] SSet.S.mk.injEq

end SSet

attribute [-simp] SSet.S.mk.injEq
