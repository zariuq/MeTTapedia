import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCollectionReadoutControls

/-! Actual source and runtime solvers choose different representatives. Their
independent collectors agree jointly, while two corrupt strategies do not. -/

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaCollectionReadoutControls

def showTerms (terms : List Atom) : String := Atom.toString (.expression terms)

def main : IO Unit := do
  let sourceValues := Streaming.CollectionReadout.sourceValues rows bank
  let nativeValues := bank.map fun answer => Unifying.resolve answer.bindings answer.value
  IO.println s!"raw-different: {decide (sourceValues ≠ nativeValues)}"
  let source := (EagerDFS.Collection.copyAnswers ∅ (sourceValues.map fun value => (value,[]))).map Prod.fst
  let native : {value : List Atom // VariantReadout.joint source = VariantReadout.joint value} :=
    ⟨Unifying.copies 1 bank,actual_joint_readout⟩
  IO.println s!"source: {showTerms (VariantReadout.joint source)}"
  IO.println s!"runtime: {showTerms (VariantReadout.joint native.val)}"
  IO.println s!"each-bad-agrees: {VariantReadout.each sharedScope == VariantReadout.each native.val}"
  IO.println s!"joint-bad-agrees: {VariantReadout.joint sharedScope == VariantReadout.joint native.val}"
  IO.println s!"bad-caller-captures: {decide (Unifying.resolve badCaller (.expression native.val) ≠ .expression native.val)}"
  let paused := Streaming.Regions.advanceLinked program 0 ⟨closing,bank_state_regions⟩
  match Streaming.observe paused.val with
  | .suspended state => IO.println s!"paused: markers={(Streaming.Regions.markers state.agenda).length} uses={state.world.uses}"
  | _ => throw (IO.userError "zero budget did not retain the collection")
  let reached := Streaming.Regions.advanceLinked program 2 paused
  have refined := Streaming.BindingInvariant.advance_refines program 2 [] closing bank_state_refines
  have supported := Streaming.ScopeInvariant.advance_wellScoped program 2 closing bank_state_wellScoped
  let carried : {value : Streaming.State //
      Streaming.BindingInvariant.stateRefines [] value ∧ Streaming.ScopeInvariant.WellScoped value ∧
      Streaming.Regions.WellFormed value} := ⟨reached.val,refined,supported,reached.property⟩
  match Streaming.observe carried.val with
  | .complete state =>
      IO.println s!"resumed: {showTerms (VariantReadout.joint (Streaming.values state))}"
      IO.println s!"uses: {state.world.uses}"
  | _ => throw (IO.userError "collection return did not complete")
