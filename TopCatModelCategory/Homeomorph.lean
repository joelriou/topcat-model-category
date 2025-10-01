import Mathlib.Topology.Homeomorph.Lemmas

@[simps]
def Equiv.ofSetEq {X : Type*} {S T : Set X} (h : S = T) : S ≃ T where
  toFun x := ⟨x.1, by simpa only [h] using x.2⟩
  invFun x := ⟨x.1, by simpa only [← h] using x.2⟩

@[simps!]
def Homeomorph.ofSetEq {X : Type*} [TopologicalSpace X] {S T : Set X} (h : S = T) :
    S ≃ₜ T where
  toEquiv := .ofSetEq h
  continuous_toFun := by subst h; exact continuous_id
  continuous_invFun := by subst h; exact continuous_id

/-@[simps]
def Equiv.restrict {X Y : Type*} (e : X ≃ Y) {S : Set X} {T : Set Y}
    (h : e ⁻¹' T = S) :
    S ≃ T where
  toFun x := ⟨e x.1, by aesop⟩
  invFun y := ⟨e.symm y.1, by aesop⟩
  left_inv x := by aesop
  right_inv y := by aesop

def Homeomorph.restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {S : Set X} {T : Set Y} (h : e ⁻¹' T = S) :
    S ≃ₜ T where
  toEquiv := e.toEquiv.restrict h
  continuous_toFun := by dsimp [Equiv.restrict]; continuity
  continuous_invFun := by dsimp [Equiv.restrict]; continuity-/
