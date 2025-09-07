import TopCatModelCategory.II
import Mathlib.Data.Fin.VecNotation

open CategoryTheory Simplicial

universe v u u₁ u₂ u₃

section

variable {I₁ : Type u₁} [Preorder I₁] [OrderBot I₁] [OrderTop I₁]
  {I₂ : Type u₂} [Preorder I₂] [OrderBot I₂] [OrderTop I₂]
  {I₃ : Type u₃} [Preorder I₃] [OrderBot I₃] [OrderTop I₃]

variable (I₁ I₂) in
@[ext]
structure IntervalHom where
  orderHom : I₁ →o I₂
  map_bot' : orderHom ⊥ = ⊥ := by aesop
  map_top' : orderHom ⊤ = ⊤ := by aesop

namespace IntervalHom

attribute [simp] map_bot' map_top'

variable (I₁) in
@[simps]
def id : IntervalHom I₁ I₁ where
  orderHom := .id

@[simps]
def comp (g : IntervalHom I₂ I₃) (f : IntervalHom I₁ I₂) : IntervalHom I₁ I₃ where
  orderHom := g.orderHom.comp f.orderHom

instance : FunLike (IntervalHom I₁ I₂) I₁ I₂ where
  coe f := f.orderHom
  coe_injective' _ _ _ := by aesop

@[simp]
lemma map_bot (f : IntervalHom I₁ I₂) : f ⊥ = ⊥ := f.map_bot'

@[simp]
lemma map_top (f : IntervalHom I₁ I₂) : f ⊤ = ⊤ := f.map_top'

@[simps]
def toULift : IntervalHom I₁ (ULift.{v} I₁) where
  orderHom := ⟨ULift.up, fun _ _ h ↦ h⟩

@[simps]
def fromULift : IntervalHom (ULift.{v} I₁) I₁ where
  orderHom := ⟨ULift.down, fun _ _ h ↦ h⟩

open Simplicial Vector
instance : Unique (IntervalHom (Fin 2) I₁) where
  default :=
    { orderHom := ⟨![⊥, ⊤], by
        rw [Fin.monotone_iff_le_succ]
        aesop⟩ }
  uniq f := by
    ext i
    fin_cases i
    · exact f.map_bot
    · exact f.map_top

end IntervalHom

end

open CategoryTheory Opposite

namespace CategoryTheory

structure Interval where private mk ::
  I : Type u
  [linearOrder : LinearOrder I]
  [orderBot : OrderBot I]
  [orderTop : OrderTop I]

namespace Interval

abbrev of (I : Type u) [LinearOrder I] [OrderBot I] [OrderTop I] : Interval.{u} := mk I

variable (X Y : Interval.{u})

instance : CoeSort Interval.{u} (Type u) where
  coe := I

instance : LinearOrder X := X.linearOrder
instance : OrderBot X := X.orderBot
instance : OrderTop X := X.orderTop

@[ext]
structure Hom where
  hom : IntervalHom X Y

variable {X Y}

instance : FunLike (Hom X Y) X Y where
  coe f := f.hom
  coe_injective' _ _ _ := by aesop

instance : Category Interval.{u} where
  Hom := Hom
  id X := { hom := .id _ }
  comp f g := { hom := g.hom.comp f.hom}

instance : ConcreteCategory Interval.{u} Hom where
  hom := id
  ofHom := id

abbrev homMk (f : IntervalHom X Y) : X ⟶ Y where
  hom := f

@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g := Hom.ext h

def uliftFunctor : Interval.{u} ⥤ Interval.{max u v} where
  obj X := .of (ULift X)
  map f := homMk
    { orderHom := OrderHom.comp ⟨ULift.up, fun _ _ h ↦ by exact h⟩
        (OrderHom.comp f.hom.orderHom ⟨ULift.down, fun _ _ h ↦ by exact h⟩) }

end Interval

end CategoryTheory

namespace SimplexCategory

namespace Hom

def toIntervalHom {n m : SimplexCategory} (f : n ⟶ m) :
    IntervalHom (Fin (m.len + 2)) (Fin (n.len + 2)) where
  orderHom := (II.map f).unop.toOrderHom
  map_bot' := II.map'_zero _
  map_top' := II.map'_last _

@[simp]
lemma toIntervalHom_id (n : SimplexCategory) :
    toIntervalHom (𝟙 n) = .id _ := by
  dsimp [toIntervalHom]
  aesop

@[simp]
lemma toIntervalHom_comp {n m p : SimplexCategory} (f : n ⟶ m) (g : m ⟶ p) :
    toIntervalHom (f ≫ g) = f.toIntervalHom.comp g.toIntervalHom := by
  dsimp [toIntervalHom]
  aesop

end Hom

@[simps]
def toInterval₀ : SimplexCategory ⥤ Interval.{0}ᵒᵖ where
  obj n := op (Interval.of (Fin (n.len + 2)))
  map f := Quiver.Hom.op (Interval.homMk (f.toIntervalHom))

instance : toInterval₀.Faithful where
  map_injective {n m f₁ f₂} h :=
    II.map_injective (Quiver.Hom.unop_inj (by
      ext i : 3
      exact ConcreteCategory.congr_hom ((Quiver.Hom.op_inj (C := Interval.{0}) h)) i))

namespace toInterval₀Full

variable {n m : ℕ} (g : Interval.of (Fin (m + 2)) ⟶ Interval.of (Fin (n + 2)))

section

variable (i : Fin (n + 1))

def finset : Finset (Fin (m + 1)) :=
  { j : Fin (m + 1) | g j.castSucc ≤ i.castSucc }

@[simp]
lemma mem_finset_iff (j : Fin (m + 1)) :
    j ∈ finset g i ↔ g j.castSucc ≤ i.castSucc := by
  simp [finset]

lemma mem_finset_of_le {j₁ j₂ : Fin (m + 1)} (hj : j₁ ≤ j₂) (hj₂ : j₂ ∈ finset g i) :
    j₁ ∈ finset g i := by
  rw [mem_finset_iff] at hj₂ ⊢
  exact le_trans (g.hom.orderHom.monotone (by simpa)) hj₂

lemma zero_mem_finset : 0 ∈ finset g i := by
  rw [mem_finset_iff]
  exact le_of_eq_of_le (IntervalHom.map_bot _) (Fin.zero_le _)

lemma nonempty_finset : (finset g i).Nonempty := ⟨_, zero_mem_finset _ _⟩

def f (i : Fin (n + 1)) : Fin (m + 1) :=
  (finset g i).max' (nonempty_finset _ _)

lemma f_mem_finset : f g i ∈ finset g i := Finset.max'_mem _ _

lemma le_iff (i : Fin (n + 1)) (j : Fin (m + 1)) :
    j ≤ f g i ↔ g j.castSucc ≤ i.castSucc := by
  rw [← mem_finset_iff]
  exact ⟨fun h ↦ mem_finset_of_le _ _ h (f_mem_finset _ _), Finset.le_max' _ _⟩

end

lemma monotone_f : Monotone (f g) := by
  intro i₁ i₂ h
  rw [le_iff]
  exact le_trans ((le_iff _ _ _).1 (le_refl _)) (Fin.castSucc_le_castSucc_iff.2 h)

open ConcreteCategory

lemma map'_f_apply (j : Fin (m + 2)) :
    II.map' ⟨f g, monotone_f g⟩ j = g j := by
  obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last j
  · by_cases h : g j.castSucc = Fin.last (n + 1)
    · rw [h, II.map'_eq_last_iff]
      intro i
      simp only [OrderHom.coe_mk, Fin.castSucc_lt_castSucc_iff]
      rw [← not_le, le_iff]
      intro h'
      rw [h, ← not_lt] at h'
      exact h' (Fin.castSucc_lt_last i)
    · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last h
      rw [II.map'_eq_iff]
      constructor
      · rw [II.mem_finset_iff]
        refine Or.inr ⟨h, ?_⟩
        dsimp
        rw [Fin.castSucc_le_castSucc_iff, le_iff, Fin.castSucc_castPred]
      · intro k
        obtain ⟨k, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last k
        · intro h'
          simpa only [II.castSucc_mem_finset_iff, OrderHom.coe_mk,
            Fin.castSucc_le_castSucc_iff, le_iff] using h'
        · simpa using Fin.le_last _
  · dsimp
    simpa only [II.map'_last] using g.hom.map_top.symm

end toInterval₀Full

open toInterval₀Full in
instance : toInterval₀.Full where
  map_surjective g := ⟨Hom.mk ⟨f g.unop, monotone_f g.unop⟩,
    Quiver.Hom.unop_inj (by ext; apply map'_f_apply)⟩

def toInterval : SimplexCategory ⥤ Interval.{u}ᵒᵖ :=
  toInterval₀ ⋙ Interval.uliftFunctor.op

end SimplexCategory

namespace IntervalHom

open SimplexCategory.toInterval₀Full in
lemma exists_simplexCategoryHom {n m : ℕ} (g : IntervalHom (Fin (m + 2)) (Fin (n + 2))) :
    ∃ (f : ⦋n⦌ ⟶ ⦋m⦌), f.toIntervalHom = g :=
  ⟨.mk ⟨_, monotone_f ⟨g⟩⟩, by
    ext i : 3
    exact map'_f_apply ⟨g⟩ i⟩

end IntervalHom
