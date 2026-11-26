import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicFiringCode
import Mettapedia.Machines.TIsa.Derivation.Examples

/-! # Symbolic p1 runs with and without the knowledge needed by a count -/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicFiringCode.Examples

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (Terms)
open Derivation.SymbolicFiring (LiveWorld Rules Attempt attemptAt portChoices)
open SymbolicExecution (Frame Work enter)

private abbrev atoms : LPSignature where
  vars := ℕ
  constants := Bool
  relationSymbols := Empty
  relationArity := fun _ => 0
  functionSymbols := Empty
  functionArity := fun _ => 0

private instance : DecidableEq atoms.vars := inferInstanceAs (DecidableEq ℕ)
private instance : DecidableEq atoms.constants := inferInstanceAs (DecidableEq Bool)
private instance : DecidableEq atoms.functionSymbols := inferInstanceAs (DecidableEq Empty)

private def label (identity : ℕ) : Term atoms := if identity = 0 then .var 0 else .const true

private def start : LiveWorld atoms :=
  LiveWorld.initial ⟨PUnit.unit, [], {0, 1}, label⟩ [0, 1] (by decide +kernel) (by decide +kernel)

private def rule (tell : Bool) : RuleSyntax.Rule (Terms (Term atoms)) :=
  ⟨PUnit.unit, ⟨[.var 0], [], if tell then [(.var 0, .const true)] else [],
    [.count (.const true) (if tell then 2 else 1)], [.var 1]⟩, [.const true]⟩

private def program (tell : Bool) : Rules atoms := [rule tell]

private def trial (tell : Bool) : Attempt (program tell) start :=
  attemptAt (Equiv.refl ℕ) (program tell) start ⟨rule tell, List.mem_cons_self⟩
    ⟨([0], []), by change ([0], []) ∈ portChoices [0, 1] 1 0; decide +kernel⟩

private def outcome (tell : Bool) (budget : Word) : Flow (Term atoms) (Work atoms) :=
  let machine := { Derivation.Examples.machine₀ with budget := budget }
  SymbolicExecution.execute start.state.knowledge (enter machine start) (compile (trial tell))

private def status : Flow (Term atoms) (Work atoms) → Option ExitStatus
  | .returned ended _ _ => some ended
  | .continuing _ => none

private def identifiers (tell : Bool) (budget : Word) : List ℕ :=
  (outcome tell budget).after.store.occurrences.map Prod.fst

private def variableLabel : Term atoms → Bool
  | .var _ => true
  | _ => false

theorem tell_licenses_count_and_keeps_an_open_output :
    status (outcome true 1) = some .completed ∧ identifiers true 1 = [1, 2] ∧
      ((outcome true 1).after.store.occurrences.map (fun atom => variableLabel atom.2)) = [false, true] := by
  decide +kernel

theorem possible_match_is_not_exactly_one :
    status (outcome false 1) = some .refused ∧ identifiers false 1 = [0, 1] ∧
      (outcome false 1).after.machine.spent = 0 := by
  decide +kernel

theorem insufficient_fuel_preserves_the_symbolic_store :
    status (outcome true 0) = some .exhausted ∧ identifiers true 0 = [0, 1] := by
  decide +kernel

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicFiringCode.Examples
