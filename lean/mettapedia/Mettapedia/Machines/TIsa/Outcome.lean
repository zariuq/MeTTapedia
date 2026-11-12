import Mettapedia.Machines.TIsa.CellEffects

/-!
# Distinct exit outcomes at the resource boundary

These are status words written into ordinary result cells. Compilation
declines, semantic refusals, invalid inputs and exhausted runs retain their
different codes. Returning only prepares a result; external publication uses
the existing admission and commit protocol.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa

inductive ExitStatus where
  | completed | refused | unsupported | invalidInput | exhausted
  deriving DecidableEq, Repr

def ExitStatus.word : ExitStatus → Word
  | .completed => 1
  | .refused => 0
  | .unsupported => 2
  | .invalidInput => 3
  | .exhausted => 4

theorem ExitStatus.word_injective : Function.Injective ExitStatus.word := by
  intro left right same
  cases left <;> cases right <;> simp_all [word]

theorem ExitStatus.encoding :
    ([.refused, .completed, .unsupported, .invalidInput, .exhausted] : List ExitStatus).map word =
      [0, 1, 2, 3, 4] := by decide

namespace Control

open Cells CellEffects

universe u
variable {Key : Type u} [DecidableEq Key]

structure Return (Key : Type u) where
  point : Key
  atPoint : Word
  terminal : Word
  source : Key
  status : Key
  value : Key
  outcome : ExitStatus
  deriving DecidableEq, Repr

def Return.check (ret : Return Key) : Bool :=
  decide ([ret.point, ret.status, ret.value].Nodup)

def Return.recipe (ret : Return Key) : Recipe Key where
  inputs := [ret.point, ret.source]
  outputs := [ret.point, ret.status, ret.value]
  guard := fun inputs outputs => match inputs, outputs with
    | [point, value], [terminal, status, result] =>
        ret.check && point == ret.atPoint && terminal == ret.terminal &&
          status == ret.outcome.word && result == value
    | _, _ => false

theorem Return.guard_iff (ret : Return Key) (before after : Key → Word) :
    ret.recipe.guard (ret.recipe.inputs.map before) (ret.recipe.outputs.map after) = true ↔
      ret.check = true ∧ before ret.point = ret.atPoint ∧ after ret.point = ret.terminal ∧
      after ret.status = ret.outcome.word ∧ after ret.value = before ret.source := by
  simp [recipe, Bool.and_eq_true, and_assoc]

theorem Return.preserves_outside (ret : Return Key) (before after : Key → Word)
    (key : Key) (outside : key ≠ ret.point ∧ key ≠ ret.status ∧ key ≠ ret.value) :
    overwrite ret.recipe.writes before after key = before key := by
  simp [overwrite, Recipe.writes, recipe, outside.1, outside.2.1, outside.2.2]

namespace OutcomeControls

private def ret : Return Nat := ⟨0, 10, 11, 1, 2, 3, .completed⟩

theorem independent_payload (outcome : ExitStatus) (payload : Word) :
    ({ret with outcome := outcome}).recipe.guard [10, payload] [11, outcome.word, payload] = true := by
  simp [ret, Return.recipe, Return.check]

theorem conflated_status_rejected (outcome : ExitStatus) (payload : Word) (different : payload ≠ outcome.word) :
    ({ret with outcome := outcome}).recipe.guard [10, payload] [11, payload, payload] = false := by
  simp [ret, Return.recipe, Return.check, different]

theorem completed_payload_42 : ret.recipe.guard [10, 42] [11, 1, 42] = true ∧
    ret.recipe.guard [10, 42] [11, 42, 42] = false := by decide

example : ret.recipe.guard [10, 7] [11, 1, 7] = true := by decide
example : ret.recipe.guard [10, 7] [11, 0, 7] = false := by decide
example : ret.recipe.guard [10, 7] [11, 1, 8] = false := by decide
example : ({ ret with status := 0 }).check = false := by decide
example : ExitStatus.unsupported.word ≠ ExitStatus.exhausted.word := by decide

end OutcomeControls

end Control
end Mettapedia.Machines.TIsa
