import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyRegionExecution

/-!
# Executable extraction of read-only nested query source

The input is the current PeTTa Program, caller substitution, source Atom and
captured effect state. Extraction follows actual query matching, argument
demand and authored clause selection. It records every consulted snapshot
and preserves all ordered answers. Named wrappers are followed through
their selected bodies, not recognized by a wrapper-name whitelist.

This is bounded, call-specific source preparation. It may enumerate a large
answer space; no preparation-work or native-speed advantage is asserted.
Algebraic join compilation must separately relate its IR to this source
certificate. Exact source pages retain reference execution.
The standalone executor starts at an expression entrance. A caller that has
already evaluated effectful operands must use the captured-entry accounting
interface instead of restarting the original expression.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics ReadOnlyQuerySource

def prepare : (fuel : Nat) → (program : Program) → (caller : Subst) →
    (state : Effects.State) → (source : Atom) → Option (Certified program caller source)
  | 0, _, _, _, _ => none
  | fuel + 1, program, caller, state, source =>
      match OptionalCallExtraction.prepare (fuel + 1) program caller source with
      | some compiled => some (fromOptional compiled)
      | none => match source with
        | .expression [.symbol "match", space, pattern, body] => do
            let location ← (prepare fuel program caller state space).bind single
            let rows ← Effects.readHandle location.value >>= state.read
            let bodies ← alternatives program (fun bindings => prepare fuel program bindings state)
              (queryBodies caller rows pattern body)
            return query location rows bodies
        | .expression [.symbol "collapse", inner] =>
            (prepare fuel program caller state inner).map collapse
        | .expression [.symbol "size-atom", inner] => do
            let argument ← (prepare fuel program caller state inner).bind single
            match shape : argument.value with
            | .expression values => some (size argument values shape)
            | _ => none
        | .expression [.symbol "if", test, yes, no] => do
            let condition ← (prepare fuel program caller state test).bind single
            match boolean : condition.value with
            | .grounded (.bool flag) =>
                let chosen ← prepare fuel program caller state (if flag then yes else no)
                return branch condition flag boolean chosen
            | _ => none
        | .expression [.symbol "let", pattern, value, body] => do
            let argument ← (prepare fuel program caller state value).bind single
            match matched : matchBinding caller pattern argument.value with
            | none => none
            | some bound =>
                let compiled ← prepare fuel program bound state body
                return ReadOnlyQuerySource.bind argument matched compiled
        | .expression [.symbol "let*", .expression pairs, body] => do
            match expanded : Eval.nestedLets pairs body with
            | none => none
            | some nested =>
                let compiled ← prepare fuel program caller state nested
                return ReadOnlyQuerySource.nestedLets expanded compiled
        | .expression [.symbol "quote", value] => some (quoted program caller value)
        | .expression [.symbol "superpose", .expression sources] => do
            let bodies ← alternatives program (fun bindings => prepare fuel program bindings state)
              (sources.map (.evaluate caller))
            return superpose bodies
        | .expression [.symbol head, left, right] => do
            let first ← (prepare fuel program caller state left).bind single
            let second ← (prepare fuel program caller state right).bind single
            match binary head first second with
            | some compiled => some compiled
            | none => ordinary program caller head [left, right] (fun bindings => prepare fuel program bindings state)
        | .expression (.symbol head :: sources) =>
            ordinary program caller head sources (fun bindings => prepare fuel program bindings state)
        | _ => none
where
  alternatives (program : Program)
      (compile : (caller : Subst) → (source : Atom) → Option (Certified program caller source)) :
      (controls : List Control) → Option (Alternatives program controls)
    | [] => some (Alternatives.nil program)
    | .evaluate caller source :: rest => do
        let first ← compile caller source
        let later ← alternatives program compile rest
        return Alternatives.cons first later
    | _ => none

  arguments (program : Program) (caller : Subst)
      (compile : (source : Atom) → Option (Certified program caller source)) :
      (sources : List Atom) → Option (Arguments program caller sources)
    | [] => some (Arguments.nil program caller)
    | source :: sources => do
        let first ← (compile source).bind single
        let rest ← arguments program caller compile sources
        return Arguments.cons first rest

  ordinary (program : Program) (caller : Subst) (head : String) (sources : List Atom)
      (compile : (bindings : Subst) → (source : Atom) → Option (Certified program bindings source)) :
      Option (Certified program caller (.expression (.symbol head :: sources))) := do
    let args ← arguments program caller (compile caller) sources
    if inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false then
      if ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"] then
        return data inert ordinary args
      else none
    else
      let admitted ← PureCallExtraction.callable program head sources.length
      match selected : application program head args.values with
      | .sequence controls [] => do
          let bodies ← alternatives program compile controls
          return call admitted.down args selected bodies
      | _ => none

def classify (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program caller source) Nat) :=
  match observation with
  | .exactPage => none
  | .completedResult => (prepare fuel program caller state source).map (fun compiled => compiled.normalize.region)

def execute (observation : PureCallExtraction.Observation) (prepareFuel sourceFuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) : Outcome :=
  match observation with
  | .exactPage => run program sourceFuel {state, control := .evaluate caller source}
  | .completedResult => ReadOnlyRegionExecution.execute .completedResult sourceFuel program caller state source
      (prepare prepareFuel program caller state source)

theorem zero_budget_refuses (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) :
    prepare 0 program caller state source = none := rfl

theorem exact_page_uses_reference (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst)
    (state : Effects.State) (source : Atom) :
    execute .exactPage prepareFuel sourceFuel program caller state source =
      run program sourceFuel {state, control := .evaluate caller source} := by simp [execute]

theorem unsupported_uses_reference (observation : PureCallExtraction.Observation)
    (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (unsupported : prepare prepareFuel program caller state source = none) :
    execute observation prepareFuel sourceFuel program caller state source =
      run program sourceFuel {state, control := .evaluate caller source} := by
  cases observation <;> simp [execute, unsupported, ReadOnlyRegionExecution.no_certificate_uses_reference]

theorem completion_has_source_run (observation : PureCallExtraction.Observation)
    (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (after : Effects.State) (answers input output : List Atom)
    (completed : execute observation prepareFuel sourceFuel program caller state source =
      .complete after answers input output) :
    ∃ fuel, run program fuel {state, control := .evaluate caller source} = .complete after answers input output := by
  cases observation with
  | exactPage => exact ⟨sourceFuel, completed⟩
  | completedResult =>
      exact ReadOnlyRegionExecution.completion_has_source_run .completedResult sourceFuel program caller state source
        (prepare prepareFuel program caller state source) after answers input output completed

theorem preserves_completed_source (observation : PureCallExtraction.Observation)
    (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (after : Effects.State) (answers input output : List Atom)
    (completed : run program sourceFuel {state, control := .evaluate caller source} =
      .complete after answers input output) :
    execute observation prepareFuel sourceFuel program caller state source = .complete after answers input output := by
  cases observation with
  | exactPage => exact completed
  | completedResult =>
      exact ReadOnlyRegionExecution.preserves_completed_source .completedResult sourceFuel program caller state source
        (prepare prepareFuel program caller state source) after answers input output completed

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction
