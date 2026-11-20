import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanProgramFormation
import Mettapedia.Languages.MeTTa.PeTTa.StreamingBindingReachability
import Mettapedia.Languages.MeTTa.PeTTa.StreamingScopeReachability
import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionReachability

/-!
Consume output plans using the existing streaming controller. The exact source
fixtures calibrate this static compiler component; unsupported compiler regions
are distinguished from source failure and are not assigned empty answers.
-/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

def fixture (label source : String) (policy : OutputPlan.BranchPolicy := .swiAliases) : IO Unit := do
  let program ← match SpaceSemantics.readProgram source with
    | .ok program => pure program
    | .error reason => throw (IO.userError reason)
  let compiled ← match OutputPlan.compileWithFormation program policy with
    | some formed => pure formed.val
    | none => throw (IO.userError s!"{label}: outside the current compiler component")
  let mut world : {value : Streaming.World //
      Streaming.ScopeInvariant.worldSupported (Mettapedia.ScopedString.Before value.uses) value} :=
    ⟨{state := Effects.loaded program,privateCode := compiled.code},
      Streaming.ScopeInvariant.loaded_world_ready program compiled.code 0⟩
  for query in compiled.queries do
    let registry := LiveEquations.atState program world.val.state
    let entry := Streaming.BindingInvariant.enterRefined world.val query
    let reachedPrefix := Streaming.BindingInvariant.advanceRefined registry 5000 entry
    have scopedEntry := Streaming.ScopeInvariant.enter_wellScoped world.val query world.property
    have scopedPrefix := Streaming.ScopeInvariant.advance_wellScoped registry 5000 entry.val scopedEntry
    have linkedPrefix := Streaming.Regions.every_request_prefix_wellFormed registry 5000 world.val query
    let carried : {value : Streaming.State //
        Streaming.BindingInvariant.stateRefines [] value ∧
        Streaming.ScopeInvariant.WellScoped value ∧ Streaming.Regions.WellFormed value} :=
      ⟨reachedPrefix.val,reachedPrefix.property,scopedPrefix,linkedPrefix⟩
    match Streaming.observe carried.val with
    | .complete reached =>
        world := ⟨carried.val.world,carried.property.2.1.1⟩
        unless world.val.output.isEmpty do throw (IO.userError "unexpected printed effect")
        IO.println s!"{label}: {String.intercalate " " ((Streaming.values reached).map Atom.toString)}"
    | .suspended _ => throw (IO.userError s!"{label}: suspended")
    | .fault reason _ => throw (IO.userError s!"{label}: {reprStr reason}")

def main : IO Unit := do
  fixture "initializer" (include_str "source-initializer-constraint.metta")
  fixture "native" (include_str "source-native-output-constraint.metta")
  fixture "alias" (include_str "source-branch-output-alias.metta")
  fixture "inert" (include_str "source-inert-branch-binding.metta")
  fixture "recursive" (include_str "source-recursive-output.metta")
  fixture "frontier" (include_str "constructor-streaming-frontier.metta")
  fixture "operands" (include_str "constructor-operands.metta")
  fixture "contextual-inert" (include_str "source-inert-branch-binding.metta") .runtimeConstraints
  fixture "contextual-alias" (include_str "source-branch-output-alias.metta") .runtimeConstraints
  fixture "sharing" (include_str "source-collection-sharing.metta")
