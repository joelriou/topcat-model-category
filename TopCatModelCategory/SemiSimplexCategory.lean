import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialObject.Basic

open CategoryTheory Simplicial

namespace RelEmbedding

variable {α β : Type*} (r : α → α → Prop) (s : β → β → Prop)
  (f : RelEmbedding r s)

@[simp]
lemma trans_refl : f.trans (.refl _) = f := rfl

@[simp]
lemma refl_trans : (RelEmbedding.refl _).trans f = f := rfl

end RelEmbedding

@[ext]
structure SemiSimplexCategory : Type where
  mk :: len : ℕ

namespace SemiSimplexCategory

scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom n m := Fin (n.len + 1) ↪o Fin (m.len + 1)
  id _ := .refl _
  comp f g := f.trans g

def homEquiv {n m : SemiSimplexCategory} :
    (n ⟶ m) ≃ (Fin (n.len + 1) ↪o Fin (m.len + 1)) :=
  .refl _

@[simp]
lemma homEquiv_id (a : SemiSimplexCategory) :
    homEquiv (𝟙 a) = .refl _ := rfl

@[simp]
lemma homEquiv_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = (homEquiv f).trans (homEquiv g) := rfl

@[ext]
theorem hom_ext {a b : SemiSimplexCategory} {f g : a ⟶ b}
    (h : homEquiv f = homEquiv g) : f = g :=
  homEquiv.injective h

def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv.symm f).toOrderHom

@[simp]
lemma toSimplexCategory_obj (n : ℕ) :
    toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌ := rfl

instance : toSimplexCategory.Faithful where
  map_injective h := by
    ext : 2
    exact DFunLike.congr_fun (congr_arg SimplexCategory.Hom.toOrderHom h) _

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono (toSimplexCategory.map f) := by
  rw [SimplexCategory.mono_iff_injective]
  exact (homEquiv f).injective

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono f where
  right_cancellation g₁ g₂ h := by
    apply toSimplexCategory.map_injective
    simp only [← cancel_mono (toSimplexCategory.map f), ← Functor.map_comp, h]

def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

abbrev homOfMono' {n m : ℕ}
    (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono f] : ⦋n⦌ₛ ⟶ ⦋m⦌ₛ :=
  homOfMono (n := ⦋n⦌ₛ) (m := ⦋m⦌ₛ) f

@[simp]
lemma toSimplexCategory_map_homOfMono
    {n m : SemiSimplexCategory}
      (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] :
      toSimplexCategory.map (homOfMono f) = f := by
  aesop

end SemiSimplexCategory

namespace CategoryTheory

variable (C : Type*) [Category C]

def SemiSimplicialObject :=
  SemiSimplexCategoryᵒᵖ ⥤ C

namespace SemiSimplicialObject

@[simps!]
instance : Category (SemiSimplicialObject C) :=
  inferInstanceAs (Category (SemiSimplexCategoryᵒᵖ ⥤ C))

end SemiSimplicialObject

namespace SimplicialObject

variable {C}

@[simps!]
def toSemiSimplicialObjectFunctor : SimplicialObject C ⥤ SemiSimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SemiSimplexCategory.toSimplexCategory.op

abbrev toSemiSimplicialObject (X : SimplicialObject C) : SemiSimplicialObject C :=
  toSemiSimplicialObjectFunctor.obj X

end SimplicialObject

def SemiCosimplicialObject :=
  SemiSimplexCategory ⥤ C

namespace SemiCosimplicialObject

@[simps!]
instance : Category (SemiCosimplicialObject C) :=
  inferInstanceAs (Category (SemiSimplexCategory ⥤ C))

end SemiCosimplicialObject

namespace CosimplicialObject

variable {C}

@[simps!]
def toSemiCosimplicialObjectFunctor : CosimplicialObject C ⥤ SemiCosimplicialObject C :=
  (Functor.whiskeringLeft _ _ _).obj SemiSimplexCategory.toSimplexCategory

abbrev toSemiCosimplicialObject (X : CosimplicialObject C) : SemiCosimplicialObject C :=
  toSemiCosimplicialObjectFunctor.obj X

end CosimplicialObject

end CategoryTheory
