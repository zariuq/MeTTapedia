import Mettapedia.GSLT.Parsing.ParserActionSlotTransport

/-!
# Substitution of prepared parser-slot actions

A prepared parser can replace a source child by a lexical token. In that case
renumbering the source action's slot is insufficient: the source child denotes
an interpreted value, while the prepared slot still contains token text.
This generic substitution composes the source action with an action for each
physical source slot. An omitted or uninterpreted slot has no substitution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserActionSubstitution

open GrammarConstructorActions (Action)

mutual
  def substitute? {Constant Primitive : Type}
      (replacement : Nat → Option (Action Constant Primitive)) :
      Action Constant Primitive → Option (Action Constant Primitive)
    | .slot index => replacement index
    | .constant value => some (.constant value)
    | .apply head arguments =>
        (substituteArguments? replacement arguments).map (Action.apply head)
    | .primitive operation arguments =>
        (substituteArguments? replacement arguments).map (Action.primitive operation)

  def substituteArguments? {Constant Primitive : Type}
      (replacement : Nat → Option (Action Constant Primitive)) :
      List (Action Constant Primitive) →
        Option (List (Action Constant Primitive))
    | [] => some []
    | head :: tail => do
        let head' ← substitute? replacement head
        let tail' ← substituteArguments? replacement tail
        some (head' :: tail')
end

mutual
  theorem substitute_executes {Constant Primitive Value : Type}
      (constant : Constant → Option Value)
      (constructor : String → List Value → Option Value)
      (primitive : Primitive → List Value → Option Value)
      (replacement : Nat → Option (Action Constant Primitive))
      (source target : List Value)
      (matching : ∀ index action, replacement index = some action →
        source[index]? = action.executeWith constant constructor primitive target)
      (action substituted : Action Constant Primitive)
      (substitutedEq : substitute? replacement action = some substituted) :
      substituted.executeWith constant constructor primitive target =
        action.executeWith constant constructor primitive source := by
    cases action with
    | slot index =>
        simp only [substitute?] at substitutedEq
        exact (matching index substituted substitutedEq).symm
    | constant value =>
        simp only [substitute?, Option.some.injEq] at substitutedEq
        subst substituted
        rfl
    | apply head arguments =>
        simp only [substitute?, Option.map_eq_some_iff] at substitutedEq
        obtain ⟨other, otherEq, rfl⟩ := substitutedEq
        simp only [Action.executeWith]
        rw [substituteArguments_execute constant constructor primitive replacement
          source target matching arguments other otherEq]
    | primitive operation arguments =>
        simp only [substitute?, Option.map_eq_some_iff] at substitutedEq
        obtain ⟨other, otherEq, rfl⟩ := substitutedEq
        simp only [Action.executeWith]
        rw [substituteArguments_execute constant constructor primitive replacement
          source target matching arguments other otherEq]

  theorem substituteArguments_execute {Constant Primitive Value : Type}
      (constant : Constant → Option Value)
      (constructor : String → List Value → Option Value)
      (primitive : Primitive → List Value → Option Value)
      (replacement : Nat → Option (Action Constant Primitive))
      (source target : List Value)
      (matching : ∀ index action, replacement index = some action →
        source[index]? = action.executeWith constant constructor primitive target)
      (arguments substituted : List (Action Constant Primitive))
      (substitutedEq : substituteArguments? replacement arguments = some substituted) :
      GrammarConstructorActions.executeArgumentsWith constant constructor primitive
          target substituted =
        GrammarConstructorActions.executeArgumentsWith constant constructor primitive
          source arguments := by
    cases arguments with
    | nil =>
        simp only [substituteArguments?, Option.some.injEq] at substitutedEq
        subst substituted
        rfl
    | cons head tail =>
        cases headEq : substitute? replacement head with
        | none => simp [substituteArguments?, headEq] at substitutedEq
        | some head' =>
            cases tailEq : substituteArguments? replacement tail with
            | none => simp [substituteArguments?, headEq, tailEq] at substitutedEq
            | some tail' =>
                simp [substituteArguments?, headEq, tailEq] at substitutedEq
                subst substituted
                simp only [GrammarConstructorActions.executeArgumentsWith]
                rw [substitute_executes constant constructor primitive replacement
                  source target matching head head' headEq]
                rw [substituteArguments_execute constant constructor primitive replacement
                  source target matching tail tail' tailEq]
end

theorem missing_slot_rejected {Constant Primitive : Type}
    (replacement : Nat → Option (Action Constant Primitive))
    (index : Nat) (missing : replacement index = none) :
    substitute? replacement (Action.slot index) = none := by
  simp [substitute?, missing]

#print axioms substitute_executes
#print axioms missing_slot_rejected

end Mettapedia.GSLT.Parsing.ParserActionSubstitution
