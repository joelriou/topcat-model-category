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

protected def Hom (a b : SemiSimplexCategory) :=
  Fin (a.len + 1) ↪o Fin (b.len + 1)

namespace Hom

def mk {a b : SemiSimplexCategory} (f : Fin (a.len + 1) ↪o Fin (b.len + 1)) :
    SemiSimplexCategory.Hom a b :=
  f

def toOrderEmbedding {a b : SemiSimplexCategory} (f : SemiSimplexCategory.Hom a b) :
    Fin (a.len + 1) ↪o Fin (b.len + 1) :=
  f

theorem ext' {a b : SemiSimplexCategory} (f g : SemiSimplexCategory.Hom a b) :
    f.toOrderEmbedding = g.toOrderEmbedding → f = g :=
  id

@[simp]
theorem mk_toOrderEmbedding {a b : SemiSimplexCategory} (f : SemiSimplexCategory.Hom a b) :
    mk f.toOrderEmbedding = f :=
  rfl

@[simp]
theorem toOrderEmbedding_mk {a b : SemiSimplexCategory} (f : Fin (a.len + 1) ↪o Fin (b.len + 1)) :
    (mk f).toOrderEmbedding = f :=
  rfl

theorem mk_toOrderEmbedding_apply {a b : SemiSimplexCategory}
    (f : Fin (a.len + 1) ↪o Fin (b.len + 1))
    (i : Fin (a.len + 1)) : (mk f).toOrderEmbedding i = f i :=
  rfl

@[simp]
def id (a : SemiSimplexCategory) : SemiSimplexCategory.Hom a a :=
  mk (.refl _)

@[simp]
def comp {a b c : SemiSimplexCategory}
    (f : SemiSimplexCategory.Hom b c) (g : SemiSimplexCategory.Hom a b) :
    SemiSimplexCategory.Hom a c :=
  mk <| g.toOrderEmbedding.trans f.toOrderEmbedding

end Hom

instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom n m := SemiSimplexCategory.Hom n m
  id _ := SemiSimplexCategory.Hom.id _
  comp f g := SemiSimplexCategory.Hom.comp g f

@[simp]
lemma id_toOrderEmbedding (a : SemiSimplexCategory) :
    Hom.toOrderEmbedding (𝟙 a) = .refl _ := rfl

@[simp]
lemma comp_toOrderEmbedding {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).toOrderEmbedding = f.toOrderEmbedding.trans g.toOrderEmbedding := rfl

@[ext]
theorem Hom.ext {a b : SemiSimplexCategory} (f g : a ⟶ b) :
    f.toOrderEmbedding = g.toOrderEmbedding → f = g :=
  Hom.ext' _ _

def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk f.toOrderEmbedding.toOrderHom

@[simp]
lemma toSimplexCategory_obj (n : ℕ) :
    toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌ := rfl

instance : toSimplexCategory.Faithful where
  map_injective h := by
    ext : 2
    exact DFunLike.congr_fun (congr_arg SimplexCategory.Hom.toOrderHom h) _

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono (toSimplexCategory.map f) := by
  rw [SimplexCategory.mono_iff_injective]
  exact f.toOrderEmbedding.injective

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono f where
  right_cancellation g₁ g₂ h := by
    apply toSimplexCategory.map_injective
    simp only [← cancel_mono (toSimplexCategory.map f), ← Functor.map_comp, h]

def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  Hom.mk (OrderEmbedding.ofStrictMono f.toOrderHom
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
