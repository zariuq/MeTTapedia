import Mettapedia.Languages.Maude.PeanoEquationRules
import Mettapedia.Languages.Maude.PeanoNormalization

/-! Every well-sorted Peano term reaches its computed representative by
forward authored equation steps in typed contexts. This includes open terms;
symbolic stuck forms remain representatives rather than becoming numerals. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.Maude.PeanoNormalization

open PeanoEquationRules

theorem add_path (context : VariableContext) (left right : Term) :
    HasSort Examples.peano.signature context left "Nat" →
    HasSort Examples.peano.signature context right "Nat" →
    EquationPath Examples.peano context "Nat" (.app "peano.add" [left, right]) (add left right) := by
  refine add.induct (motive := fun left right =>
    HasSort Examples.peano.signature context left "Nat" →
    HasSort Examples.peano.signature context right "Nat" →
    EquationPath Examples.peano context "Nat" (.app "peano.add" [left, right]) (add left right))
    ?_ ?_ ?_ left right
  · intro right _ typed
    rw [add_zero]
    exact Relation.ReflTransGen.single (add_zero_step typed)
  · intro left right ih leftTyped rightTyped
    have inner := successor_argument_typed leftTyped
    have first := add_succ_step inner rightTyped
    have rest := (ih inner rightTyped).inArgument (successorFrame context)
    rw [add_succ]
    exact (Relation.ReflTransGen.single first).trans (by simpa only [successorFrame_plug] using rest)
  · intro left right notZero notSuccessor _ _
    rw [add.eq_3 left right notZero notSuccessor]

theorem multiply_path (context : VariableContext) (left right : Term) :
    HasSort Examples.peano.signature context left "Nat" →
    HasSort Examples.peano.signature context right "Nat" →
    EquationPath Examples.peano context "Nat" (.app "peano.mul" [left, right]) (multiply left right) := by
  refine multiply.induct (motive := fun left right =>
    HasSort Examples.peano.signature context left "Nat" →
    HasSort Examples.peano.signature context right "Nat" →
    EquationPath Examples.peano context "Nat" (.app "peano.mul" [left, right]) (multiply left right))
    ?_ ?_ ?_ left right
  · intro right _ typed
    rw [multiply_zero]
    exact Relation.ReflTransGen.single (multiply_zero_step typed)
  · intro left right ih leftTyped rightTyped
    have inner := successor_argument_typed leftTyped
    have first := multiply_succ_step inner rightTyped
    have rest := ih inner rightTyped
    have resultTyped := (rest.equivalent (multiplication_typed inner rightTyped)).sorted.2
    have placed := rest.inArgument (additionRightFrame rightTyped)
    simp only [additionRightFrame_plug] at placed
    have finished := add_path context right (multiply left right) rightTyped resultTyped
    rw [multiply_succ]
    exact (Relation.ReflTransGen.single first).trans (placed.trans finished)
  · intro left right notZero notSuccessor _ _
    rw [multiply.eq_3 left right notZero notSuccessor]

theorem reduce_path (context : VariableContext) (term : Term)
    (typed : HasSort Examples.peano.signature context term "Nat") :
    EquationPath Examples.peano context "Nat" term (reduce term) := by
  revert typed
  refine Term.rec
    (motive_1 := fun term => HasSort Examples.peano.signature context term "Nat" →
      EquationPath Examples.peano context "Nat" term (reduce term))
    (motive_2 := fun terms => ∀ term ∈ terms, HasSort Examples.peano.signature context term "Nat" →
      EquationPath Examples.peano context "Nat" term (reduce term))
    ?_ ?_ ?_ ?_ term
  · intro name _
    rw [reduce]
  · intro id arguments children typed
    obtain ⟨declaration, member, label, _, argumentsTyped⟩ := HasSort.operator_arguments typed rfl
    rcases operators member with rfl | rfl | rfl | rfl
    · subst id
      cases argumentsTyped
      dsimp only [zeroOperator]
      rw [reduce_zero]
    · subst id
      cases argumentsTyped with
      | cons first rest =>
          cases rest
          have path := (children _ (by simp) first).inArgument (successorFrame context)
          simpa only [successorOperator, successorFrame_plug, reduce_succ] using path
    · subst id
      cases argumentsTyped with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              have firstPath := children _ (by simp) first
              have secondPath := children _ (by simp) second
              have firstTyped := (firstPath.equivalent first).sorted.2
              have secondTyped := (secondPath.equivalent second).sorted.2
              have firstPlaced := firstPath.inArgument (additionLeftFrame second)
              have secondPlaced := secondPath.inArgument (additionRightFrame firstTyped)
              have finished := add_path context _ _ firstTyped secondTyped
              simpa only [additionOperator, additionLeftFrame_plug, additionRightFrame_plug, reduce_add] using
                firstPlaced.trans (secondPlaced.trans finished)
    · subst id
      cases argumentsTyped with
      | cons first rest =>
          cases rest with
          | cons second tail =>
              cases tail
              have firstPath := children _ (by simp) first
              have secondPath := children _ (by simp) second
              have firstTyped := (firstPath.equivalent first).sorted.2
              have secondTyped := (secondPath.equivalent second).sorted.2
              have firstPlaced := firstPath.inArgument (multiplicationLeftFrame second)
              have secondPlaced := secondPath.inArgument (multiplicationRightFrame firstTyped)
              have finished := multiply_path context _ _ firstTyped secondTyped
              simpa only [multiplicationOperator, multiplicationLeftFrame_plug, multiplicationRightFrame_plug, reduce_multiply] using
                firstPlaced.trans (secondPlaced.trans finished)
  · intro term member
    cases member
  · intro first rest firstIH restIH term member typed
    rcases List.mem_cons.mp member with rfl | member
    · exact firstIH typed
    · exact restIH term member typed

theorem reduce_sound {context : VariableContext} {term : Term}
    (typed : HasSort Examples.peano.signature context term "Nat") :
    Equivalent Examples.peano context "Nat" term (reduce term) :=
  (reduce_path context term typed).equivalent typed

theorem reduce_typed {context : VariableContext} {term : Term}
    (typed : HasSort Examples.peano.signature context term "Nat") :
    HasSort Examples.peano.signature context (reduce term) "Nat" := (reduce_sound typed).sorted.2

theorem equivalent_iff_reduce_eq {context : VariableContext} {source target : Term}
    (sourceTyped : HasSort Examples.peano.signature context source "Nat")
    (targetTyped : HasSort Examples.peano.signature context target "Nat") :
    Equivalent Examples.peano context "Nat" source target ↔ reduce source = reduce target := by
  constructor
  · exact equivalent_same_reduce
  · intro same
    have before := reduce_sound sourceTyped
    have after := (reduce_sound targetTyped).symm
    rw [same] at before
    exact .trans before after

theorem reduce_idempotent {context : VariableContext} {term : Term}
    (typed : HasSort Examples.peano.signature context term "Nat") : reduce (reduce term) = reduce term :=
  (equivalent_same_reduce (reduce_sound typed)).symm

theorem path_same_reduce {context : VariableContext} {source target : Term}
    (typed : HasSort Examples.peano.signature context source "Nat")
    (path : EquationPath Examples.peano context "Nat" source target) : reduce source = reduce target :=
  equivalent_same_reduce (path.equivalent typed)

theorem paths_join {context : VariableContext} {source left right : Term}
    (typed : HasSort Examples.peano.signature context source "Nat")
    (first : EquationPath Examples.peano context "Nat" source left)
    (second : EquationPath Examples.peano context "Nat" source right) :
    ∃ joined, EquationPath Examples.peano context "Nat" left joined ∧
      EquationPath Examples.peano context "Nat" right joined := by
  have leftTyped := (first.equivalent typed).sorted.2
  have rightTyped := (second.equivalent typed).sorted.2
  have leftForm := path_same_reduce typed first
  have rightForm := path_same_reduce typed second
  refine ⟨reduce source, ?_, ?_⟩
  · simpa only [leftForm] using reduce_path context left leftTyped
  · simpa only [rightForm] using reduce_path context right rightTyped

theorem steps_join {context : VariableContext} {source left right : Term}
    (typed : HasSort Examples.peano.signature context source "Nat")
    (first : EquationReduction Examples.peano context "Nat" source left)
    (second : EquationReduction Examples.peano context "Nat" source right) :
    ∃ joined, EquationPath Examples.peano context "Nat" left joined ∧
      EquationPath Examples.peano context "Nat" right joined :=
  paths_join typed (Relation.ReflTransGen.single first) (Relation.ReflTransGen.single second)

theorem zero_not_successor {context : VariableContext} :
    ¬ Equivalent Examples.peano context "Nat" (.app "peano.zero" [])
      (.app "peano.succ" [.app "peano.zero" []]) := by
  intro equivalent
  have same := equivalent_same_reduce equivalent
  simp only [reduce_zero, reduce_succ] at same
  cases (Term.app.inj same).2

end Mettapedia.Languages.Maude.PeanoNormalization
