import TopCatModelCategory.II

universe u

open CategoryTheory Opposite

namespace CategoryTheory

structure Interval where private mk ::
  I : Type u
  [partialOrder : PartialOrder I]
  [orderBot : OrderBot I]
  [orderTop : OrderTop I]

namespace Interval

abbrev of (I : Type u) [PartialOrder I] [OrderBot I] [OrderTop I] : Interval.{u} := mk I

variable (X Y : Interval.{u})

instance : CoeSort Interval.{u} (Type u) where
  coe := I

instance : PartialOrder X := X.partialOrder
instance : OrderBot X := X.orderBot
instance : OrderTop X := X.orderTop

@[ext]
structure Hom where
  hom : X →o Y
  hom_bot : hom ⊥ = ⊥ := by aesop
  hom_top : hom ⊤ = ⊤ := by aesop

attribute [simp] Hom.hom_bot Hom.hom_top

instance : FunLike (Hom X Y) X Y where
  coe f := f.hom
  coe_injective' _ _ _ := by aesop

instance : Category Interval.{u} where
  Hom := Hom
  id X := { hom := .id }
  comp f g := { hom := g.hom.comp f.hom}

instance : ConcreteCategory Interval.{u} Hom where
  hom := id
  ofHom := id

variable {X Y}
@[ext]
lemma hom_ext {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g := Hom.ext h

@[simp]
lemma apply (f : X ⟶ Y) (x : X) : ConcreteCategory.hom f x = f.hom x := by rfl

end Interval

end CategoryTheory

namespace SimplexCategory

def toInterval₀ : SimplexCategory ⥤ Interval.{0}ᵒᵖ where
  obj n := op (Interval.of (Fin (n.len + 2)))
  map f := Quiver.Hom.op
    { hom := (II.map f).unop.toOrderHom
      hom_bot := II.map'_zero _
      hom_top := II.map'_last _ }

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
  exact le_trans (g.hom.monotone (by simpa)) hj₂

lemma zero_mem_finset : 0 ∈ finset g i := by
  rw [mem_finset_iff]
  exact le_of_eq_of_le (Interval.Hom.hom_bot _) (Fin.zero_le _)

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
  · simpa using g.hom_top.symm

end toInterval₀Full

open toInterval₀Full in
instance : toInterval₀.Full where
  map_surjective g := ⟨Hom.mk ⟨f g.unop, monotone_f g.unop⟩,
    Quiver.Hom.unop_inj (by ext; apply map'_f_apply)⟩

end SimplexCategory
