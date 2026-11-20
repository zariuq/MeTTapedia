import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplates
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# Repeated matching against immutable private equations

This executable experiment uses the existing total first-order unifier on
both routes. Each prepared batch includes its initial principal solve and
normalization. Ground queries vary across uses and batches. The shared-variable
control rejects a preparation that erases the equations without normalizing
the entire payload. Timings are measurements of this Lean prototype, not C
refinement, general cost bounds or a language-default recommendation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplateExperiment

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax (app symbol)

def aliases (length : Nat) : EquationStore Tm :=
  (List.range length).map fun index => (.var index, .var (index + 1))

def payload (length : Nat) : Tm := app (.var 0) (.var length)

def target (nonce : Nat) : Tm := app (symbol nonce) (symbol nonce)

def ordinary (length uses offset : Nat) : Nat :=
  let knowledge := aliases length
  let pattern := payload length
  (List.range uses).foldl (fun checksum index =>
    let query := target (offset + index)
    match unifyTotal (knowledge ++ [(pattern, query)]) with
    | none => checksum
    | some answer => if answer.applyTerm pattern = query then checksum + 1 else checksum) 0

def prepared (length uses offset : Nat) : Nat :=
  match unifyTotal (aliases length) with
  | none => 0
  | some principal =>
      let pattern := principal.applyTerm (payload length)
      (List.range uses).foldl (fun checksum index =>
        let query := target (offset + index)
        match unifyTotal [(pattern, query)] with
        | none => checksum
        | some answer => if answer.applyTerm pattern = query then checksum + 1 else checksum) 0

def sharingControl : Bool :=
  let badQuery := app (symbol 0) (symbol 1)
  let ordinaryAccepts := (unifyTotal (aliases 1 ++ [(payload 1, badQuery)])).isSome
  let erasedAccepts := (unifyTotal [(payload 1, badQuery)]).isSome
  let preparedAccepts := match unifyTotal (aliases 1) with
    | none => false
    | some principal => (unifyTotal [(principal.applyTerm (payload 1), badQuery)]).isSome
  !ordinaryAccepts && erasedAccepts && !preparedAccepts

def contradictoryControl : Bool :=
  (unifyTotal [(symbol 0, symbol 1)]).isNone

def stalePreparationControl : Bool :=
  let query := target 1
  let changed := aliases 1 ++ [(.var 0, symbol 0)]
  let changedAccepts := (unifyTotal (changed ++ [(payload 1, query)])).isSome
  let staleAccepts := match unifyTotal (aliases 1) with
    | none => false
    | some principal => (unifyTotal [(principal.applyTerm (payload 1), query)]).isSome
  !changedAccepts && staleAccepts

def measure (label : String) (uses batches : Nat) (work : Nat → Nat)
    (expected : Nat := uses) : IO Nat := do
  let start ← IO.monoNanosNow
  let mut checksum := 0
  for batch in [:batches] do
    checksum := checksum + work (batch * uses)
  let finish ← IO.monoNanosNow
  unless checksum = expected * batches do
    throw (IO.userError s!"{label}: checksum {checksum}, expected {expected * batches}")
  pure (finish - start)

def experiment (baseBatches : Nat) (preparedFirst : Bool) : IO Unit := do
  unless sharingControl && contradictoryControl && stalePreparationControl do
    throw (IO.userError "principal-template negative control failed")
  unless ordinary 4 2 123 == 2 && prepared 4 2 123 == 2 do
    throw (IO.userError "principal-template positive control failed")
  for length in List.range 12 do
    for uses in [1, 2, 7] do
      for offset in [0, 13] do
        let direct := ordinary length uses offset
        let cached := prepared length uses offset
        unless direct == uses && cached == direct do
          throw (IO.userError s!"differential control failed at {length}/{uses}/{offset}")
  IO.println s!"controls=pass; differential_cases=72; preparation=included; queries=ground-and-varying; prepared_first={preparedFirst}"
  for length in [4, 16, 32, 64] do
    for uses in [1, 16, 64] do
      let batches := max 1 (baseBatches * (64 / uses))
      let (ordinaryTime, preparedTime) ← if preparedFirst then do
        let preparedTime ← measure "prepared" uses batches (prepared length uses)
        let ordinaryTime ← measure "ordinary" uses batches (ordinary length uses)
        pure (ordinaryTime, preparedTime)
      else do
        let ordinaryTime ← measure "ordinary" uses batches (ordinary length uses)
        let preparedTime ← measure "prepared" uses batches (prepared length uses)
        pure (ordinaryTime, preparedTime)
      IO.println s!"length={length} uses={uses} batches={batches} ordinary_ns={ordinaryTime} prepared_ns={preparedTime} speedup_milli={1000 * ordinaryTime / max 1 preparedTime}"

/-- Solving these equations expands the root into a full binary constructor tree. -/
def constructorChain (length : Nat) : EquationStore Tm :=
  (List.range length).map fun index =>
    (.var index, app (.var (index + 1)) (.var (index + 1)))

def constructorDirect (length uses offset : Nat) : Nat :=
  (List.range uses).foldl (fun checksum index =>
    let problem := ((.var 0, symbol (offset + index)) :: constructorChain length)
    if (unifyTotal problem).isSome then checksum + 1 else checksum) 0

def constructorPrepared (length uses offset : Nat) : Nat :=
  match unifyTotal (constructorChain length) with
  | none => 0
  | some principal =>
      let pattern := principal.applyTerm (.var 0)
      (List.range uses).foldl (fun checksum index =>
        if (unifyTotal [(pattern, symbol (offset + index))]).isSome
          then checksum + 1 else checksum) 0

def constructorSizeControl (length : Nat) : Bool :=
  match unifyTotal (constructorChain length) with
  | none => false
  | some principal => (principal.applyTerm (.var 0)).size == 2 ^ (length + 1) - 1

/-- Rejection can avoid expanding irrelevant private structure. Both routes
use the same solver; the query-first baseline has the same equation models.
Preparation remains included in every timed prepared batch. -/
def adversarial (baseBatches : Nat) (preparedFirst : Bool) : IO Unit := do
  unless sharingControl && contradictoryControl && stalePreparationControl do
    throw (IO.userError "principal-template negative control failed")
  for length in List.range 9 do
    unless constructorSizeControl length do
      throw (IO.userError s!"constructor size control failed at {length}")
    for uses in [1, 2, 7] do
      for offset in [0, 13] do
        let expected := if length = 0 then uses else 0
        unless constructorDirect length uses offset == expected &&
            constructorPrepared length uses offset == expected do
          throw (IO.userError s!"constructor differential control failed at {length}/{uses}/{offset}")
  IO.println s!"controls=pass; differential_cases=54; constructor_sizes=9; preparation=included; baseline=query-first; prepared_first={preparedFirst}"
  for length in [2, 4, 6, 8, 10, 12] do
    for uses in [1, 8] do
      let batches := max 1 baseBatches
      let (ordinaryTime, preparedTime) ← if preparedFirst then do
        let preparedTime ← measure "constructor-prepared" uses batches (constructorPrepared length uses) 0
        let ordinaryTime ← measure "constructor-direct" uses batches (constructorDirect length uses) 0
        pure (ordinaryTime, preparedTime)
      else do
        let ordinaryTime ← measure "constructor-direct" uses batches (constructorDirect length uses) 0
        let preparedTime ← measure "constructor-prepared" uses batches (constructorPrepared length uses) 0
        pure (ordinaryTime, preparedTime)
      IO.println s!"length={length} uses={uses} batches={batches} expanded_nodes={2 ^ (length + 1) - 1} ordinary_ns={ordinaryTime} prepared_ns={preparedTime} speedup_milli={1000 * ordinaryTime / max 1 preparedTime}"

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplateExperiment

def main (arguments : List String) : IO Unit :=
  let batches := ((arguments.headD "2").toNat?.getD 2)
  let preparedFirst := arguments.contains "prepared-first"
  if arguments.contains "adversarial" then
    Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplateExperiment.adversarial
      batches preparedFirst
  else
    Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.PrincipalTemplateExperiment.experiment
      batches preparedFirst
