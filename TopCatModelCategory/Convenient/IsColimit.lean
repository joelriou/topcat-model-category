import TopCatModelCategory.Convenient.Category
import TopCatModelCategory.TopCat.Colimits
import Mathlib.CategoryTheory.Limits.Types.Colimits

universe t u

open CategoryTheory Topology Limits

variable {ι : Type t} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

namespace TopCat

variable (Y : TopCat.{u})

structure GeneratorsOverCat where
  i : ι
  f : C(X i, Y)

namespace GeneratorsOverCat

variable {X Y}

@[ext]
structure Hom (j k : GeneratorsOverCat X Y) where
  f : C(X j.i, X k.i)
  fac : k.f.comp f = j.f := by aesop

attribute [simp] Hom.fac

@[simp]
lemma Hom.fac_apply {j k : GeneratorsOverCat X Y} (φ : Hom j k) (x : X j.i) :
    k.f (φ.f x) = j.f x :=
  DFunLike.congr_fun φ.fac x

instance : Category (GeneratorsOverCat X Y) where
  Hom := Hom
  id j := { f := .id _ }
  comp φ ψ := { f := ψ.f.comp φ.f }

variable (X Y)

@[simps]
def functor : GeneratorsOverCat X Y ⥤ TopCat.{u} where
  obj j := TopCat.of (X j.i)
  map φ := TopCat.ofHom φ.f

@[simps]
def cocone : Cocone (functor X Y) where
  pt := Y
  ι := { app j := TopCat.ofHom j.f }

section

variable [Inhabited ι] [Nonempty (X default)]

variable {X Y} in
@[simps]
def constant (y : Y) : GeneratorsOverCat X Y where
  i := default
  f := ⟨fun _ ↦ y, continuous_const⟩

noncomputable def isColimitForget : IsColimit ((forget _).mapCocone (cocone X Y)) := by
  refine Nonempty.some ((Types.isColimit_iff_coconeTypesIsColimit _).2
    ⟨fun x₁ x₂ h ↦ ?_, fun y ↦ ?_⟩)
  · obtain ⟨j₁, x₁, rfl⟩ := Functor.ιColimitType_jointly_surjective _ x₁
    obtain ⟨j₂, x₂, rfl⟩ := Functor.ιColimitType_jointly_surjective _ x₂
    dsimp at h
    let k := constant (X := X) (j₁.f x₁)
    let z : X k.i := Classical.arbitrary (X default)
    let φ₁ : k ⟶ j₁ :=
      { f := ⟨fun _ ↦ x₁, continuous_const⟩
        fac := rfl }
    let φ₂ : k ⟶ j₂ :=
      { f := ⟨fun _ ↦ x₂, continuous_const⟩
        fac := by ext; exact h.symm }
    have hφ₁ := (functor X Y ⋙ forget _).ιColimitType_map φ₁ z
    have hφ₂ := (functor X Y ⋙ forget _).ιColimitType_map φ₂ z
    exact hφ₁.trans hφ₂.symm
  · exact ⟨(functor X Y ⋙ forget _).ιColimitType (constant y)
      (Classical.arbitrary (X default)), rfl⟩

noncomputable def isColimit [IsGeneratedBy X Y] : IsColimit (cocone X Y) := by
  refine Nonempty.some ((TopCat.nonempty_isColimit_iff _).2 ⟨⟨isColimitForget X Y⟩, ?_⟩)
  ext U
  dsimp at U ⊢
  rw [IsGeneratedBy.isOpen_iff X]
  simp only [isOpen_coinduced, Set.preimage_id', isOpen_iSup_iff]
  exact ⟨fun h i ↦ h i.f, fun h i f ↦ h ⟨i, f⟩⟩

end

end GeneratorsOverCat

end TopCat
