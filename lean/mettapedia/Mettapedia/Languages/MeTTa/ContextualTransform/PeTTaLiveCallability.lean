import Mettapedia.Machines.CallabilityTranslation
import Mettapedia.Machines.RegisteredArity
import Mettapedia.Languages.MeTTa.PeTTa.LibTransform

/-!
# Live callability in PeTTa continuations

P-DEF-4 decides each reached executable occurrence in the current program.
A translated fragment prepared earlier is suitable for that occurrence if its
observed decisions still validate. The occurrence's execution can then
select candidates from the current world. A running choice retains the
candidate occurrences it selected at entry.

The two entry functions below compare fresh translation with revalidation
in the existing ordered, state-threading PeTTa search semantics. Each
source is the executable fragment reached at that boundary. If another
effect can precede a nested occurrence, that occurrence has its own entry
boundary. Values in the fragment are opaque to translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability

open Mettapedia.Machines.CallabilityTranslation
open Mettapedia.Languages.MeTTa.PeTTa.LibTransform (Search Trace)

variable {World Name Value A B : Type}

/-- Translate the reached source in the world where it is about to run. -/
def enterLive (available : World → Name → Bool) (source : Source Name Value)
    (execute : Plan Name Value → Search World A) : Search World A :=
  fun world => execute (compile (available world) source) world

/-- Revalidate the translated source at the same entry boundary. -/
def enterRevalidated (available : World → Name → Bool) (saved : Capture Name Value)
    (execute : Plan Name Value → Search World A) : Search World A :=
  fun world => execute (refresh (available world) saved) world

theorem enterRevalidated_eq_live (available : World → Name → Bool)
    (translatedIn : World) (source : Source Name Value)
    (execute : Plan Name Value → Search World A) :
    enterRevalidated available (capture (available translatedIn) source) execute =
      enterLive available source execute := by
  funext world
  unfold enterRevalidated enterLive
  rw [refresh_capture]

/-- Each answer of an effectful prefix reaches the next occurrence in the world
it produced. Equality of traces includes their resume continuations. -/
theorem bind_revalidated_eq_live (prior : Search World A)
    (available : World → Name → Bool) (translatedIn : A → World)
    (source : A → Source Name Value)
    (execute : A → Plan Name Value → Search World B) :
    prior.bind (fun answer => enterRevalidated available
          (capture (available (translatedIn answer)) (source answer)) (execute answer)) =
      prior.bind (fun answer => enterLive available (source answer) (execute answer)) := by
  apply congrArg (Search.bind prior)
  funext answer
  exact enterRevalidated_eq_live available (translatedIn answer) (source answer) (execute answer)

/-- Select ordered alternatives once, in the world in which the call starts. -/
def candidatesAtEntry (select : World → List A) : Search World A :=
  fun world => Search.superpose (select world) world

/-- The first alternative may change the world. The subsequent alternatives
come from the selected tail and run in the world the first leaves. -/
theorem candidatesAtEntry_bind (select : World → List A) (body : A → Search World B)
    {entry : World} {first : A} {rest : List A}
    (selected : select entry = first :: rest) :
    ((candidatesAtEntry select).bind body) entry =
      (body first entry).append (fun world => (Search.superpose rest).bind body world) := by
  simp only [Search.bind, candidatesAtEntry, selected, Search.superpose, Trace.bind]

namespace Controls

private def rows (entries : List Nat) (head : Nat) : List Nat :=
  if head = 7 then entries else []

private def available (world : Nat → List Nat) (head : Nat) : Bool :=
  !(world head).isEmpty

private def occurrence : Source Nat Nat :=
  .apply 7 (.cons (.value 1) .nil)

private def execute : Plan Nat Nat → Search (Nat → List Nat) (Sum Nat Nat)
  | .value value => Search.superpose [.inl value]
  | .apply (false, head) _ => Search.superpose [.inl head]
  | .apply (true, head) _ => candidatesAtEntry fun world => (world head).map Sum.inr

/-- A public installation before the occurrence is reached changes its meaning
under P-DEF-4. Keeping the unit-entry translation gives the DIFF-22 result. -/
theorem installation_before_occurrence :
    let before := rows []
    let after := rows [11, 11]
    let prior : Search (Nat → List Nat) Nat := fun _ => .answer 0 after .done
    let saved := capture (available before) occurrence
    ((prior.bind fun _ => enterRevalidated available saved execute) before).drain.1 =
        [.inr 11, .inr 11] ∧
      ((prior.bind fun _ => execute saved.plan) before).drain.1 = [.inl 7] := by
  decide +kernel

/-- A value constructed before an installation can be used after it. -/
theorem carried_value_after_installation :
    let before := rows []
    let after := rows [11]
    let saved := capture (available before) (.value 7)
    (enterRevalidated available saved execute after).drain.1 = [.inl 7] := by
  decide +kernel

/-- The plan can remain valid even though an already entered call and a newly
entered call have different alternatives. -/
theorem replacement_preserves_entered_alternatives :
    let before := rows [2, 2, 3]
    let after := rows [9]
    let saved := capture (available before) occurrence
    let body : Sum Nat Nat → Search (Nat → List Nat) (Sum Nat Nat) :=
      fun answer _ => .answer answer after .done
    Mettapedia.Machines.ReadOnlyQuery.checkReads (available after) saved.reads = true ∧
      ((enterRevalidated available saved execute).bind body before).drain.1 =
        [Sum.inr 2, Sum.inr 2, Sum.inr 3] ∧
      (enterRevalidated available saved execute after).drain.1 = [Sum.inr 9] := by
  decide +kernel

/-- A callability decision alone carries no exact-arity authority. -/
theorem adding_an_arity_changes_invocation_kind :
    let before := [2]
    let after := [2, 1]
    (!before.isEmpty) = (!after.isEmpty) ∧
      Mettapedia.Machines.RegisteredArity.reference true before 1 = .partialApp ∧
      Mettapedia.Machines.RegisteredArity.reference true after 1 = .call := by
  decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaLiveCallability
