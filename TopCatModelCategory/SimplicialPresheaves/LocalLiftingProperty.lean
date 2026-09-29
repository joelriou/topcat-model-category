module

public import TopCatModelCategory.SSet.CategoryWithFibrations

@[expose] public section

universe v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {A B : D} (i : A ⟶ B) {F G : Cᵒᵖ ⥤ D} (f : F ⟶ G)

attribute [reassoc] CommSq.LiftStruct.fac_left CommSq.LiftStruct.fac_right
attribute [simp] CommSq.LiftStruct.fac_left_assoc CommSq.LiftStruct.fac_right_assoc

namespace GrothendieckTopology

section

variable {U : C} {t : A ⟶ F.obj ⟨U⟩} {b : B ⟶ G.obj ⟨U⟩}
  (sq : CommSq t i (f.app ⟨U⟩) b)

variable {i f} in
def liftingSieve : Sieve U where
  arrows V p := (CommSq.mk (g := i) (h := f.app ⟨V⟩) (f := t ≫ F.map p.op)
      (i := b ≫ G.map p.op) (by simp [sq.w_assoc])).HasLift
  downward_closed := by
    dsimp
    rintro V W p ⟨⟨l⟩⟩ q
    exact ⟨⟨{ l := l.l ≫ F.map q.op }⟩⟩

end

def localLiftingProperty : MorphismProperty (Cᵒᵖ ⥤ D) := fun F G f ↦
  ∀ {U : C} {t : A ⟶ F.obj ⟨U⟩} {b : B ⟶ G.obj ⟨U⟩}
      (sq : CommSq t i (f.app ⟨U⟩) b),
    liftingSieve sq ∈ J _

def trivialLocalFibrations : MorphismProperty (Cᵒᵖ ⥤ SSet.{u}) :=
  ⨅ (n : ℕ), J.localLiftingProperty (SSet.boundary.{u} n).ι

def localFibrations : MorphismProperty (Cᵒᵖ ⥤ SSet.{u}) :=
  ⨅ (n : ℕ) (i : Fin (n + 2)), J.localLiftingProperty (SSet.horn.{u} (n + 1) i).ι

end GrothendieckTopology

end CategoryTheory
