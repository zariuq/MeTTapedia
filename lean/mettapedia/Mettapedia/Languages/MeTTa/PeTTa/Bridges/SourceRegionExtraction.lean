import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQueryExtraction

/-!
# Composing source-certified regions through ordinary source contexts

A leaf compiler supplies a certificate indexed by the actual program, caller
and source expression. This driver follows argument demand and authored clause
selection to compose those leaves through wrappers, lets, branches and scalar
consumers. There is no function-name whitelist and no raw-query enumeration
fallback in this driver. A leaf compiler may implement its own qualified query
algorithm; failure to cover a productive alternative refuses the wrapper.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.SourceRegionExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics ReadOnlyQuerySource

abbrev LeafCompiler := (program : Program) → (caller : Subst) → (state : Effects.State) →
  (source : Atom) → Option (Certified program caller source)

def prepare (leaf : LeafCompiler) : (fuel : Nat) → (program : Program) → (caller : Subst) →
    (state : Effects.State) → (source : Atom) → Option (Certified program caller source)
  | 0, _, _, _, _ => none
  | fuel + 1, program, caller, state, source =>
      match leaf program caller state source with
      | some compiled => some compiled
      | none => match OptionalCallExtraction.prepare (fuel + 1) program caller source with
        | some compiled => some (fromOptional compiled)
        | none => match source with
          | .expression [.symbol "collapse", inner] =>
              (prepare leaf fuel program caller state inner).map collapse
          | .expression [.symbol "size-atom", inner] => do
              let argument ← (prepare leaf fuel program caller state inner).bind single
              match shape : argument.value with
              | .expression values => some (size argument values shape)
              | _ => none
          | .expression [.symbol "if", test, yes, no] => do
              let condition ← (prepare leaf fuel program caller state test).bind single
              match boolean : condition.value with
              | .grounded (.bool flag) =>
                  let chosen ← prepare leaf fuel program caller state (if flag then yes else no)
                  return branch condition flag boolean chosen
              | _ => none
          | .expression [.symbol "let", pattern, value, body] => do
              let argument ← (prepare leaf fuel program caller state value).bind single
              match matched : matchBinding caller pattern argument.value with
              | none => none
              | some bound =>
                  let compiled ← prepare leaf fuel program bound state body
                  return ReadOnlyQuerySource.bind argument matched compiled
          | .expression [.symbol "let*", .expression pairs, body] => do
              match expanded : Eval.nestedLets pairs body with
              | none => none
              | some nested =>
                  let compiled ← prepare leaf fuel program caller state nested
                  return ReadOnlyQuerySource.nestedLets expanded compiled
          | .expression [.symbol "quote", value] => some (quoted program caller value)
          | .expression [.symbol "superpose", .expression sources] => do
              let bodies ← ReadOnlyQueryExtraction.prepare.alternatives program
                (fun bindings => prepare leaf fuel program bindings state) (sources.map (.evaluate caller))
              return superpose bodies
          | .expression [.symbol head, left, right] => do
              let first ← (prepare leaf fuel program caller state left).bind single
              let second ← (prepare leaf fuel program caller state right).bind single
              match binary head first second with
              | some compiled => some compiled
              | none =>
                  ReadOnlyQueryExtraction.prepare.ordinary program caller head [left, right]
                    (fun bindings => prepare leaf fuel program bindings state)
          | .expression (.symbol head :: sources) =>
              ReadOnlyQueryExtraction.prepare.ordinary program caller head sources
                (fun bindings => prepare leaf fuel program bindings state)
          | _ => none

def classify (leaf : LeafCompiler) (observation : PureCallExtraction.Observation) (fuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program caller source) Nat) :=
  match observation with
  | .exactPage => none
  | .completedResult => (prepare leaf fuel program caller state source).map (fun compiled => compiled.normalize.region)

def execute (leaf : LeafCompiler) (observation : PureCallExtraction.Observation) (prepareFuel sourceFuel : Nat)
    (program : Program) (caller : Subst) (state : Effects.State) (source : Atom) : Outcome :=
  match observation with
  | .exactPage => run program sourceFuel {state, control := .evaluate caller source}
  | .completedResult => ReadOnlyRegionExecution.execute .completedResult sourceFuel program caller state source
      (prepare leaf prepareFuel program caller state source)

theorem unsupported_uses_reference (leaf : LeafCompiler) (observation : PureCallExtraction.Observation)
    (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (unsupported : prepare leaf prepareFuel program caller state source = none) :
    execute leaf observation prepareFuel sourceFuel program caller state source =
      run program sourceFuel {state, control := .evaluate caller source} := by
  cases observation <;> simp [execute, unsupported, ReadOnlyRegionExecution.no_certificate_uses_reference]

theorem completion_has_source_run (leaf : LeafCompiler) (observation : PureCallExtraction.Observation)
    (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (after : Effects.State) (answers input output : List Atom)
    (completed : execute leaf observation prepareFuel sourceFuel program caller state source =
      .complete after answers input output) :
    ∃ fuel, run program fuel {state, control := .evaluate caller source} = .complete after answers input output := by
  cases observation with
  | exactPage => exact ⟨sourceFuel, completed⟩
  | completedResult =>
      exact ReadOnlyRegionExecution.completion_has_source_run .completedResult sourceFuel program caller state source
        (prepare leaf prepareFuel program caller state source) after answers input output completed

theorem preserves_completed_source (leaf : LeafCompiler) (observation : PureCallExtraction.Observation)
    (prepareFuel sourceFuel : Nat) (program : Program) (caller : Subst) (state : Effects.State) (source : Atom)
    (after : Effects.State) (answers input output : List Atom)
    (completed : run program sourceFuel {state, control := .evaluate caller source} = .complete after answers input output) :
    execute leaf observation prepareFuel sourceFuel program caller state source = .complete after answers input output := by
  cases observation with
  | exactPage => exact completed
  | completedResult =>
      exact ReadOnlyRegionExecution.preserves_completed_source .completedResult sourceFuel program caller state source
        (prepare leaf prepareFuel program caller state source) after answers input output completed

theorem zero_budget_refuses (leaf : LeafCompiler) (program : Program) (caller : Subst)
    (state : Effects.State) (source : Atom) : prepare leaf 0 program caller state source = none := rfl

theorem exact_page_refuses (leaf : LeafCompiler) (fuel : Nat) (program : Program) (caller : Subst)
    (state : Effects.State) (source : Atom) : classify leaf .exactPage fuel program caller state source = none := rfl

theorem certificates_agree {program : Program} {caller : Subst} {source : Atom}
    (first second : Certified program caller source) (state : Effects.State)
    (firstValid : Valid first.reads state) (secondValid : Valid second.reads state) :
    first.values = second.values := by
  have observations := (completed_source_exact first state firstValid).symm.trans
    (completed_source_exact second state secondValid)
  have same := Set.singleton_injective observations
  exact congrArg PureCallPortfolio.Completed.answers same

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.SourceRegionExtraction
