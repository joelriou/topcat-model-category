module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import TopCatModelCategory.SSet.Subcomplex

@[expose] public section

open CategoryTheory Simplicial

universe u

namespace SimplexCategory

@[simps obj]
def rev : SimplexCategory ⥤ SimplexCategory where
  obj n := n
  map {n m} f := Hom.mk ⟨fun i ↦ (f i.rev).rev, fun i j hij ↦ by
    rw [Fin.rev_le_rev]
    apply f.toOrderHom.monotone
    rwa [Fin.rev_le_rev]⟩

@[simp]
lemma rev_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (rev.map f).toOrderHom (a := n) (b := m) i = (f.toOrderHom i.rev).rev := by
  rfl

lemma rev_map_δ {n : ℕ} (i : Fin (n + 2)) :
    rev.map (δ i) = δ i.rev := by
  ext j : 3
  rw [rev_map_apply]
  dsimp [δ]
  rw [Fin.succAbove_rev_right, Fin.rev_rev]

lemma rev_map_σ {n : ℕ} (i : Fin (n + 1)) :
    rev.map (σ i) = σ i.rev := by
  ext j : 3
  rw [rev_map_apply]
  dsimp [σ]
  rw [Fin.predAbove_rev_right, Fin.rev_rev]

@[simps!]
def revCompRevIso : rev ⋙ rev ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

@[simps]
def revEquivalence : SimplexCategory ≌ SimplexCategory where
  functor := rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso

end SimplexCategory

namespace SimplicialObject

variable {C : Type*} [Category C]

@[simps!]
def revFunctor : SimplicialObject C ⥤ SimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SimplexCategory.rev.op

@[simps!]
def revFunctorCompRevFunctor : revFunctor (C := C) ⋙ revFunctor ≅ 𝟭 _ :=
  (Functor.whiskeringLeftObjCompIso _ _).symm ≪≫
    (Functor.whiskeringLeft _ _ _).mapIso
    ((Functor.opHom _ _).mapIso (SimplexCategory.revCompRevIso).symm.op) ≪≫
    Functor.whiskeringLeftObjIdIso

@[simps!]
def revEquivalence : SimplicialObject C ≌ SimplicialObject C where
  functor := revFunctor
  inverse := revFunctor
  unitIso := revFunctorCompRevFunctor.symm
  counitIso := revFunctorCompRevFunctor

end SimplicialObject

namespace SSet

def revFunctor : SSet.{u} ⥤ SSet.{u} := SimplicialObject.revFunctor

@[simps!]
def revFunctorCompRevFunctor : revFunctor.{u} ⋙ revFunctor ≅ 𝟭 _ :=
  SimplicialObject.revFunctorCompRevFunctor

@[simps!]
def revEquivalence : SSet.{u} ≌ SSet.{u} :=
  SimplicialObject.revEquivalence

abbrev rev (X : SSet.{u}) : SSet.{u} := revFunctor.obj X

def revObjEquiv {X : SSet.{u}} {n : SimplexCategoryᵒᵖ} :
    X.rev.obj n ≃ X.obj n := Equiv.refl _

lemma rev_map (X : SSet.{u}) {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : X.rev.obj n) :
    X.rev.map f x =
      revObjEquiv.symm (X.map (SimplexCategory.rev.map f.unop).op (revObjEquiv x)) := by
  rfl

namespace Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

def rev : X.rev.Subcomplex := Subcomplex.range (revFunctor.map A.ι)

@[simp]
lemma mem_rev_obj_iff {n : SimplexCategoryᵒᵖ} (x : X.rev.obj n) :
    x ∈ A.rev.obj n ↔ revObjEquiv x ∈ A.obj n := by
  dsimp [rev]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

lemma rev_iSup {ι : Type*} (A : ι → X.Subcomplex) :
    (iSup A).rev = ⨆ (i : ι), (A i).rev := by
  ext n x
  obtain ⟨x, rfl⟩ := revObjEquiv.symm.surjective x
  simp

end Subcomplex

end SSet
