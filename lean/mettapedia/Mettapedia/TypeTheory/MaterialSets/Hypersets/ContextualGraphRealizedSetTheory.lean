import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetConstructors
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedDeduction
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSetTheory

/-!
# Basic material axioms in the varying realized graph model

The independently stated first-order sentences are interpreted with
current existential witnesses and full-future implication and universal
quantification. The actual graph constructors validate these clauses at
every context. No pointwise or static set law is used as a future law.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetTheory

open CategoryTheory ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFormulaRealization ContextualGraphRealizedSetConstructors
open ContextualMaterialSetTheory (emptyAxiom pairingAxiom unionAxiom infinityAxiom extensionalityAxiom)

universe u
variable {D : Type u} [Category.{u} D]

def emptyLaw (point : D) (environment : Environment D 0 point) :
    realize D emptyAxiom point environment := by
  refine ⟨empty point, ?_⟩
  intro target path value future tail proof
  let normalized := Member.transportParent
    (Equal.ofEq (move_composition D path tail (empty point)).symm) proof.down
  exact PEmpty.elim (emptyEliminate (path ≫ tail) normalized)

def pairingLaw (point : D) (environment : Environment D 0 point) :
    realize D pairingAxiom point environment := by
  intro firstStage firstPath first secondStage secondPath second
  let previous := move D secondPath first
  let paired := pair previous second
  refine ⟨paired, ?_⟩
  intro target path value
  constructor
  · intro future tail proof
    let normalized := Member.transportParent
      (Equal.ofEq (move_composition D path tail paired).symm) proof.down
    match pairEliminate (path ≫ tail) normalized with
    | .inl same => exact .inl ⟨same.trans (Equal.ofEq (move_composition D path tail previous))⟩
    | .inr same => exact .inr ⟨same.trans (Equal.ofEq (move_composition D path tail second))⟩
  · intro future tail proof
    let current : Member (move D tail value) (move D (path ≫ tail) paired) :=
      match proof with
      | .inl same => Member.transportChild
          (same.down.trans (Equal.ofEq (move_composition D path tail previous).symm)).symm
          (pairFirst (path ≫ tail) previous second)
      | .inr same => Member.transportChild
          (same.down.trans (Equal.ofEq (move_composition D path tail second).symm)).symm
          (pairSecond (path ≫ tail) previous second)
    exact ⟨Member.transportParent (Equal.ofEq (move_composition D path tail paired)) current⟩

def unionLaw (point : D) (environment : Environment D 0 point) :
    realize D unionAxiom point environment := by
  intro source initialPath parent
  refine ⟨union parent, ?_⟩
  intro target path value
  constructor
  · intro future tail proof
    let normalized := Member.transportParent
      (Equal.ofEq (move_composition D path tail (union parent)).symm) proof.down
    let decoded := unionEliminate parent (path ≫ tail) normalized
    exact ⟨decoded.1,
      ⟨⟨Member.transportParent (Equal.ofEq (move_composition D path tail parent)) decoded.2.1⟩,
        ⟨decoded.2.2⟩⟩⟩
  · intro future tail proof
    let parentMember := Member.transportParent
      (Equal.ofEq (move_composition D path tail parent).symm) proof.2.1.down
    exact ⟨Member.transportParent (Equal.ofEq (move_composition D path tail (union parent)))
      (unionIntro parent (path ≫ tail) parentMember proof.2.2.down)⟩

def infinityLaw (point : D) (environment : Environment D 0 point) :
    realize D infinityAxiom point environment := by
  refine ⟨infinity point, ⟨?_, ?_⟩⟩
  · refine ⟨empty point, ⟨?_, ⟨infinityEmpty point⟩⟩⟩
    intro target path value future tail proof
    let normalized := Member.transportParent
      (Equal.ofEq (move_composition D path tail (empty point)).symm) proof.down
    exact PEmpty.elim (emptyEliminate (path ≫ tail) normalized)
  · intro target path value future tail proof
    let arrived := move D tail value
    refine ⟨successor arrived, ⟨?_, ⟨infinitySuccessor proof.down⟩⟩⟩
    intro later arrival child
    constructor
    · intro last terminal member
      let normalized := Member.transportParent
        (Equal.ofEq (move_composition D arrival terminal (successor arrived)).symm) member.down
      match successorEliminate (arrival ≫ terminal) normalized with
      | .inl old => exact .inl ⟨Member.transportParent
          (Equal.ofEq (move_composition D arrival terminal arrived)) old⟩
      | .inr self => exact .inr ⟨self.trans (Equal.ofEq (move_composition D arrival terminal arrived))⟩
    · intro last terminal member
      let current : Member (move D terminal child) (move D (arrival ≫ terminal) (successor arrived)) :=
        match member with
        | .inl old => successorOld (arrival ≫ terminal)
            (Member.transportParent (Equal.ofEq (move_composition D arrival terminal arrived).symm) old.down)
        | .inr self => successorSelf (arrival ≫ terminal)
            (self.down.trans (Equal.ofEq (move_composition D arrival terminal arrived).symm))
      exact ⟨Member.transportParent (Equal.ofEq (move_composition D arrival terminal (successor arrived))) current⟩

def extensionalityLaw (point : D) (environment : Environment D 2 point) :
    realize D extensionalityAxiom point environment := by
  intro target path premise
  refine ⟨extensionality ?_ ?_⟩
  · intro future tail child member
    have action := (premise future tail child).1 future (𝟙 future)
    rw [moveEnvironment_identity] at action
    exact (action ⟨member⟩).down
  · intro future tail child member
    have action := (premise future tail child).2 future (𝟙 future)
    rw [moveEnvironment_identity] at action
    exact (action ⟨member⟩).down

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphRealizedSetTheory
