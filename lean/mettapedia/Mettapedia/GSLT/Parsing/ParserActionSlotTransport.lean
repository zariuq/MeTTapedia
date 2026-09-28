import Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-!
# Transport compiled construction actions across parser slot layouts

A grammar specialization may omit physical parser slots, such as layout.
Transport is partial: an action that reads an omitted slot has no transported
action. The generic law below relates successful transport to the original
action without assuming a particular grammar or value representation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ParserActionSlotTransport

open GrammarConstructorActions (Action)

mutual
  def transport? {Constant Primitive : Type} (slot : Nat → Option Nat) :
      Action Constant Primitive → Option (Action Constant Primitive)
    | .slot index => (slot index).map Action.slot
    | .constant value => some (.constant value)
    | .apply head arguments =>
        (transportArguments? slot arguments).map (Action.apply head)
    | .primitive operation arguments =>
        (transportArguments? slot arguments).map (Action.primitive operation)

  def transportArguments? {Constant Primitive : Type} (slot : Nat → Option Nat) :
      List (Action Constant Primitive) → Option (List (Action Constant Primitive))
    | [] => some []
    | head :: tail => do
        let head' ← transport? slot head
        let tail' ← transportArguments? slot tail
        some (head' :: tail')
end

mutual
  theorem transport_executes {Constant Primitive Value : Type}
      (constant : Constant → Option Value)
      (constructor : String → List Value → Option Value)
      (primitive : Primitive → List Value → Option Value)
      (slot : Nat → Option Nat) (source target : List Value)
      (matching : ∀ index mapped, slot index = some mapped →
        source[index]? = target[mapped]?)
      (action transported : Action Constant Primitive)
      (transportedEq : transport? slot action = some transported) :
      transported.executeWith constant constructor primitive target =
        action.executeWith constant constructor primitive source := by
    cases action with
    | slot index =>
        simp only [transport?, Option.map_eq_some_iff] at transportedEq
        obtain ⟨mapped, mappedEq, rfl⟩ := transportedEq
        exact (matching index mapped mappedEq).symm
    | constant value =>
        simp only [transport?, Option.some.injEq] at transportedEq
        subst transported
        rfl
    | apply head arguments =>
        simp only [transport?, Option.map_eq_some_iff] at transportedEq
        obtain ⟨other, otherEq, rfl⟩ := transportedEq
        simp only [Action.executeWith]
        rw [transportArguments_execute constant constructor primitive slot source target
          matching arguments other otherEq]
    | primitive operation arguments =>
        simp only [transport?, Option.map_eq_some_iff] at transportedEq
        obtain ⟨other, otherEq, rfl⟩ := transportedEq
        simp only [Action.executeWith]
        rw [transportArguments_execute constant constructor primitive slot source target
          matching arguments other otherEq]

  theorem transportArguments_execute {Constant Primitive Value : Type}
      (constant : Constant → Option Value)
      (constructor : String → List Value → Option Value)
      (primitive : Primitive → List Value → Option Value)
      (slot : Nat → Option Nat) (source target : List Value)
      (matching : ∀ index mapped, slot index = some mapped →
        source[index]? = target[mapped]?)
      (arguments transported : List (Action Constant Primitive))
      (transportedEq : transportArguments? slot arguments = some transported) :
      GrammarConstructorActions.executeArgumentsWith constant constructor primitive
          target transported =
        GrammarConstructorActions.executeArgumentsWith constant constructor primitive
          source arguments := by
    cases arguments with
    | nil =>
        simp only [transportArguments?, Option.some.injEq] at transportedEq
        subst transported
        rfl
    | cons head tail =>
        cases headEq : transport? slot head with
        | none => simp [transportArguments?, headEq] at transportedEq
        | some head' =>
            cases tailEq : transportArguments? slot tail with
            | none => simp [transportArguments?, headEq, tailEq] at transportedEq
            | some tail' =>
                simp [transportArguments?, headEq, tailEq] at transportedEq
                subst transported
                simp only [GrammarConstructorActions.executeArgumentsWith]
                rw [transport_executes constant constructor primitive slot source target
                  matching head head' headEq]
                rw [transportArguments_execute constant constructor primitive slot source target
                  matching tail tail' tailEq]
end

theorem removed_slot_rejected {Constant Primitive : Type} (slot : Nat → Option Nat)
    (index : Nat) (missing : slot index = none) :
    transport? slot (Action.slot index : Action Constant Primitive) = none := by
  simp [transport?, missing]

theorem retained_slot {Constant Primitive : Type} (slot : Nat → Option Nat)
    (index mapped : Nat) (present : slot index = some mapped) :
    transport? slot (Action.slot index : Action Constant Primitive) =
      some (.slot mapped) := by
  simp [transport?, present]

#print axioms transport_executes
#print axioms removed_slot_rejected

end Mettapedia.GSLT.Parsing.ParserActionSlotTransport
