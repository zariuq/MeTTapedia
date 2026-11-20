import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionSelectionExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.GeneralScopedMatchExecution
import Mettapedia.OSLF.MeTTaIL.ScopedCollectionCanonical

/-!
# Collection batches in MeTTa

The collection allocator supplies ordinary argument and rest-capture tasks to
the existing scoped engine. Allocation decisions and nested match histories
remain in the wire. The direct residual construction requires arranged input;
its comparison with the semantic batch is proved in ScopedCollectionCanonical.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionSelection
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Effects (State)
open Eval BridgeKit WireKit
open RuleInstantiationExecution.GeneralExecution
open CollectionSelectionExecution (booleanTerm allocationTerm)
open scoped ProgramQuotation

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_machine.metta"
    sha256 "34addb0bd7d4b78a6883cc7238a0c4741358085b9b22bdf490398a4cbd0e2b46"

def library : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

theorem checked : library.check = true := RetainedMatchingWire.interpreted_checked

def requestTerm (request : ScopedCollectionMachine.Request) : Term :=
  .application "CollectionRequest" [matcherRequestTerm request.machine, .natural request.index]

def jobTerm (job : ScopedCollectionMachine.Job) : Term :=
  .application "CollectionJob"
    [allocationTerm InferenceCettaWire.encodePattern job.allocation, matcherStateTerm job.state]

def stateTerm (state : ScopedCollectionMachine.State) : Term := encodeList jobTerm state

def receiptTerm (receipt : ScopedCollectionMachine.Receipt) : Term :=
  .application "CollectionReceipt"
    [allocationTerm InferenceCettaWire.encodePattern receipt.allocation, matcherAnswerTerm receipt.matching]

def firingTerm (firing : ScopedCollectionMachine.FiringReceipt) : Term :=
  .application "CollectionFiring" [receiptTerm firing.source,
    InferenceCettaWire.encodePattern firing.target]


section CollectionmachineProofMetadata

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

private def collectionMachineProofSource : Program := (RuleExecutionProgram.interpretedPremiseSupportSources[6]'(by decide +kernel)).program

theorem collectionMachineProof_source_quote : collectionMachineProofSource = source.program := by rfl

private def collectionMachineObservedInheritedHeads : List String :=
  ((collectionMachineProofSource.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(collectionMachineProofSource.equations.map (·.head)).contains head)).eraseDups

/-- Direct outward calls derived from the actual family bodies. -/
def collectionMachineProofInheritedHeads : List String := ["gslt:automata:length", "gslt:automata:append", "gslt:collection:allocate", "gslt:rule:scope-matcher-run", "gslt:rule:scope-matcher-complete", "gslt:rule:scope-reduct"]

theorem collectionMachineProofInheritedHeads_derived :
    collectionMachineObservedInheritedHeads = collectionMachineProofInheritedHeads := by decide +kernel

theorem collectionMachineProof_source_count : collectionMachineProofSource.equations.length = 14 := by decide +kernel

theorem collectionMachineProof_inherited_count : collectionMachineObservedInheritedHeads.length = 6 := by
  rw [collectionMachineProofInheritedHeads_derived]
  decide +kernel

private def collectionMachineScopedMetadataEquations : List SpaceSemantics.Equation :=
  [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[174]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[180]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[207]'(by decide +kernel)]

private def collectionMachinePriorMetadataEquations : List SpaceSemantics.Equation :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.equations[4]'(by decide +kernel)]

private def collectionMachineScopedMetadataDeclarations : List Atom :=
  [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[174]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[180]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[207]'(by decide +kernel)]

private def collectionMachinePriorMetadataDeclarations : List Atom :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[5]'(by decide +kernel)).program.declarations[4]'(by decide +kernel)]

private def collectionMachineMetadataBase : Program where
  equations := collectionMachineScopedMetadataEquations ++ collectionMachinePriorMetadataEquations
  declarations := collectionMachineScopedMetadataDeclarations ++ collectionMachinePriorMetadataDeclarations

/-- Bounded call and constructor metadata; execution remains in the shared Raw program. -/
def collectionMachineProofLibrary : Library := ⟨collectionMachineMetadataBase, collectionMachineProofSource, ["gslt:collection-machine:", "gslt:collection-plan:"]⟩

def collectionMachineProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || collectionMachineProofLibrary.owns head || collectionMachineProofInheritedHeads.contains head

theorem collectionMachineProof_checked : collectionMachineProofLibrary.check = true := by decide +kernel

theorem collectionMachineProof_equation_count : collectionMachineProofLibrary.runtime.equations.length = 20 := by decide +kernel

private def collectionMachinePriorSources := RuleExecutionProgram.interpretedPremiseSupportSources.take 6
private def collectionMachineLaterSources := RuleExecutionProgram.interpretedPremiseSupportSources.drop 7

private theorem collectionMachineScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => collectionMachineProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨174, by decide +kernel⟩, ⟨180, by decide +kernel⟩, ⟨207, by decide +kernel⟩] := by decide +kernel

private theorem collectionMachineScoped_equations : RuleExecutionProgram.scopedProgram.equations.filter (fun row => collectionMachineProofHeads row.head) = collectionMachineScopedMetadataEquations := by
  rw [CompleteExecution.source_filter_indices, collectionMachineScoped_equations_indices]
  rfl

private theorem collectionMachinePrior_equations_indices :
    (List.finRange (collectionMachinePriorSources.flatMap (fun source => source.program.equations)).length).filter (fun index => (fun row => collectionMachineProofHeads row.head) ((collectionMachinePriorSources.flatMap (fun source => source.program.equations)).get index)) =
      [⟨164, by decide +kernel⟩] := by decide +kernel

private theorem collectionMachinePrior_equations : (collectionMachinePriorSources.flatMap (fun source => source.program.equations)).filter (fun row => collectionMachineProofHeads row.head) = collectionMachinePriorMetadataEquations := by
  rw [CompleteExecution.source_filter_indices, collectionMachinePrior_equations_indices]
  rfl

private theorem collectionMachineOwned_equations : collectionMachineProofSource.equations.filter (fun row => collectionMachineProofHeads row.head) = collectionMachineProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem collectionMachineLater_equations : (collectionMachineLaterSources.flatMap (fun source => source.program.equations)).filter (fun row => collectionMachineProofHeads row.head) = [] := by
  have checked : (collectionMachineLaterSources.flatMap (fun source => source.program.equations)).all (fun row => !((fun row => collectionMachineProofHeads row.head) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem collectionMachineSupport_equations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations) =
      (collectionMachinePriorSources.flatMap (fun source => source.program.equations)) ++ collectionMachineProofSource.equations ++ (collectionMachineLaterSources.flatMap (fun source => source.program.equations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      collectionMachinePriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[6]'(by decide +kernel)) :: collectionMachineLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem collectionMachineProof_physical_equations : collectionMachineProofLibrary.runtime.equations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter (fun row => collectionMachineProofHeads row.head) := by
  rw [CompleteExecution.PhysicalSourceAgreement.fold_equations, collectionMachineSupport_equations]
  simp only [List.filter_append, collectionMachineScoped_equations, collectionMachinePrior_equations,
    collectionMachineOwned_equations, collectionMachineLater_equations, List.append_nil]
  change (collectionMachineScopedMetadataEquations ++ collectionMachinePriorMetadataEquations) ++ collectionMachineProofSource.equations = _
  simp only [List.append_assoc]

private theorem collectionMachineScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration collectionMachineProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨174, by decide +kernel⟩, ⟨180, by decide +kernel⟩, ⟨207, by decide +kernel⟩] := by decide +kernel

private theorem collectionMachineScoped_declarations : RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration collectionMachineProofHeads) = collectionMachineScopedMetadataDeclarations := by
  rw [CompleteExecution.source_filter_indices, collectionMachineScoped_declarations_indices]
  rfl

private theorem collectionMachinePrior_declarations_indices :
    (List.finRange (collectionMachinePriorSources.flatMap (fun source => source.program.declarations)).length).filter (fun index => (retainedCallDeclaration collectionMachineProofHeads) ((collectionMachinePriorSources.flatMap (fun source => source.program.declarations)).get index)) =
      [⟨164, by decide +kernel⟩] := by decide +kernel

private theorem collectionMachinePrior_declarations : (collectionMachinePriorSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration collectionMachineProofHeads) = collectionMachinePriorMetadataDeclarations := by
  rw [CompleteExecution.source_filter_indices, collectionMachinePrior_declarations_indices]
  rfl

private theorem collectionMachineOwned_declarations : collectionMachineProofSource.declarations.filter (retainedCallDeclaration collectionMachineProofHeads) = collectionMachineProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem collectionMachineLater_declarations : (collectionMachineLaterSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration collectionMachineProofHeads) = [] := by
  have checked : (collectionMachineLaterSources.flatMap (fun source => source.program.declarations)).all (fun row => !((retainedCallDeclaration collectionMachineProofHeads) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem collectionMachineSupport_declarations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations) =
      (collectionMachinePriorSources.flatMap (fun source => source.program.declarations)) ++ collectionMachineProofSource.declarations ++ (collectionMachineLaterSources.flatMap (fun source => source.program.declarations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      collectionMachinePriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[6]'(by decide +kernel)) :: collectionMachineLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem collectionMachineProof_physical_declarations : collectionMachineProofLibrary.runtime.declarations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter (retainedCallDeclaration collectionMachineProofHeads) := by
  rw [CompleteExecution.PhysicalSourceAgreement.fold_declarations, collectionMachineSupport_declarations]
  simp only [List.filter_append, collectionMachineScoped_declarations, collectionMachinePrior_declarations,
    collectionMachineOwned_declarations, collectionMachineLater_declarations, List.append_nil]
  change (collectionMachineScopedMetadataDeclarations ++ collectionMachinePriorMetadataDeclarations) ++ collectionMachineProofSource.declarations = _
  simp only [List.append_assoc]

theorem collectionMachineProof_agreement :
    ProgramAgreementOn collectionMachineProofHeads collectionMachineProofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram := by
  have physical : ProgramAgreementOn collectionMachineProofHeads collectionMachineProofLibrary.runtime
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram) :=
    fragment_agreement _ _ collectionMachineProof_physical_equations collectionMachineProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) CompleteExecution.PhysicalSourceAgreement.physical_interpreted_agreement)

/-- The metadata does not assert closure of inherited primitive bodies. -/
theorem collectionMachineProof_not_closed : ¬ ProgramClosed collectionMachineProofHeads collectionMachineProofLibrary.runtime := by
  intro closed
  let row := collectionMachineMetadataBase.equations[5]'(by decide +kernel)
  have member : row ∈ collectionMachineProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : collectionMachineProofHeads row.head = true := by decide +kernel
  have outside : codeWithin collectionMachineProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms collectionMachineProof_source_quote
#print axioms collectionMachineProofInheritedHeads_derived
#print axioms collectionMachineProof_source_count
#print axioms collectionMachineProof_inherited_count
#print axioms collectionMachineProof_checked
#print axioms collectionMachineProof_equation_count
#print axioms collectionMachineProof_agreement
#print axioms collectionMachineProof_not_closed

end CollectionmachineProofMetadata

syntax "collection_machine_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| collection_machine_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in collectionMachineProof_checked using collectionMachineProof_agreement; metta_eval [$facts,*] with collectionMachineProof_checked in collectionMachineProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        requestTerm, jobTerm, stateTerm, receiptTerm, allocationTerm, booleanTerm,
        matcherStateTerm, matcherWorkTerm, matcherTaskTerm,
        InferenceCettaWire.encodePatterns_eq_encodeList,
        encodeList, encodeOption, $extra,*]))

@[metta_head "gslt:automata:append"]
theorem append_returns {α : Type} (element : α → Term) (state : State) (left right : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:append" [encoded (encodeList element left), encoded (encodeList element right)])
      state (encoded (encodeList element (left ++ right))) := by
  exact CollectionSelectionExecution.append_returns element state left right

@[metta_head "gslt:automata:length"]
theorem length_returns {α : Type} (element : α → Term) (state : State) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:automata:length" [encoded (encodeList element items)])
      state (number items.length) := by
  exact CollectionSelectionExecution.scoped_length_returns element state items

@[metta_head "gslt:collection:allocate"]
theorem allocate_returns {α : Type} (element : α → Term) (state : State)
    (idempotent : Bool) (count : Nat) (items : List α) :
    PureReturns library.runtime [] state
      (apply "gslt:collection:allocate"
        [encoded (booleanTerm idempotent), number count, encoded (encodeList element items)])
      state (encoded (encodeList (allocationTerm element) (tracedAllocations idempotent count items))) := by
  exact CollectionSelectionExecution.allocate_returns element state idempotent count items

private theorem machine_primitive {head : String}
    (supported : MachineTransport.executionHeads head = true) :
    RetainedMatchingWire.scopedPrimitiveHeads head = true := by
  have checked : MachineTransport.executionHeadNames.all
      RetainedMatchingWire.scopedPrimitiveHeads = true := by decide +kernel
  exact List.all_eq_true.mp checked head (List.contains_iff_mem.mp supported)

theorem machine_agreement :
    ProgramAgreementOn MachineTransport.executionHeads GeneralScopedMatchExecution.program
      CollectionSelectionExecution.scopedLibrary.runtime :=
  agreement_trans Mechanical.matcher_agreement
    (agreement_mono (fun _ supported => machine_primitive supported)
      RetainedMatchingWire.scopedPrimitive_agreement)

@[metta_head "gslt:rule:scope-matcher-run"]
theorem run_returns (state : State) (request : GeneralScopedMatchMachine.Request)
    (fuel : Nat) (machine : GeneralScopedMatchMachine.State) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-matcher-run"
        [encoded (matcherRequestTerm request), number fuel, encoded (matcherStateTerm machine)])
      state (encoded (matcherStateTerm (GeneralScopedMatchMachine.run request fuel machine))) := by
  exact transport_call MachineTransport.program_closed machine_agreement
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["request", "fuel", "state"] (by decide) rfl (by decide +kernel)
    (matcher_run_returns state request fuel machine)

@[metta_head "gslt:rule:scope-matcher-complete"]
theorem machine_complete_returns (state : State) (machine : GeneralScopedMatchMachine.State) :
    PureReturns library.runtime [] state
      (apply "gslt:rule:scope-matcher-complete" [encoded (matcherStateTerm machine)])
      state (Effects.boolean (GeneralScopedMatchMachine.complete machine)) := by
  exact transport_call MachineTransport.program_closed machine_agreement
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
    ["state"] (by decide) rfl (by decide +kernel)
    (matcher_complete_returns state machine)

@[metta_head "gslt:collection-machine:allocation-state"]
theorem allocation_state_returns (state : State) (request : ScopedCollectionMachine.Request)
    (allocation : Allocation Pattern) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:allocation-state"
        [encoded (requestTerm request), encoded (allocationTerm InferenceCettaWire.encodePattern allocation)])
      state (encoded (matcherStateTerm (ScopedCollectionMachine.rawAllocationState request allocation))) := by
  cases rest : request.rest with
  | none =>
      cases residual : allocation.residual with
      | nil =>
          collection_machine_eval unfolding [ScopedCollectionMachine.rawAllocationState, rest, residual,
            matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeRest, traceTerm]
      | cons first tail =>
          collection_machine_eval unfolding [ScopedCollectionMachine.rawAllocationState, rest, residual,
            matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
            InferenceCettaWire.encodeRest, traceTerm]
  | some name =>
      have count := length_returns InferenceCettaWire.encodePattern state request.schemas
      have path := append_returns Term.natural state request.path [request.index + request.schemas.length]
      collection_machine_eval [count, path] unfolding [ScopedCollectionMachine.rawAllocationState, rest,
        matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
        InferenceCettaWire.encodePatterns_eq_encodeList, InferenceCettaWire.encodeRest, traceTerm]

@[metta_head "gslt:collection-machine:jobs"]
theorem jobs_returns (state : State) (request : ScopedCollectionMachine.Request) :
    ∀ allocations : List (Allocation Pattern),
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:jobs"
        [encoded (requestTerm request), encoded (encodeList (allocationTerm InferenceCettaWire.encodePattern) allocations)])
      state (encoded (stateTerm (allocations.map fun allocation =>
        ⟨allocation, ScopedCollectionMachine.rawAllocationState request allocation⟩)))
  | [] => by collection_machine_eval
  | allocation :: tail => by
      have first := allocation_state_returns state request allocation
      have later := jobs_returns state request tail
      collection_machine_eval [first, later] unfolding [List.map_cons]

@[metta_head "gslt:collection-machine:start"]
theorem raw_start_returns (state : State) (request : ScopedCollectionMachine.Request) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:start" [encoded (requestTerm request)])
      state (encoded (stateTerm (ScopedCollectionMachine.rawStart request))) := by
  have count := length_returns InferenceCettaWire.encodePattern state request.schemas
  have allocated := allocate_returns InferenceCettaWire.encodePattern state
    (request.kind == .hashSet) request.schemas.length request.targets
  have jobs := jobs_returns state request request.allocations
  cases kind : request.kind <;>
    collection_machine_eval [count, allocated, jobs] unfolding [
      ScopedCollectionMachine.rawStart, ScopedCollectionMachine.Request.allocations,
      matcherRequestTerm, ScopedCollectionMachine.Request.machine, InferenceCettaWire.encodePattern,
      InferenceCettaWire.encodePatterns_eq_encodeList, InferenceCettaWire.encodeRest,
      InferenceCettaWire.encodeCollectionType, kind]

/-- The emitted start builds exactly the semantic job list when the carrier
has already been arranged according to its declared collection algebra. -/
theorem start_returns (state : State) (request : ScopedCollectionMachine.Request)
    (fixed : CanonicalBags.arrange request.kind request.targets = request.targets) :
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:start" [encoded (requestTerm request)])
      state (encoded (stateTerm (ScopedCollectionMachine.start request))) := by
  rw [← ScopedCollectionMachine.rawStart_eq request fixed]
  exact raw_start_returns state request

@[metta_head "gslt:collection-machine:resume"]
theorem resume_returns (state : State) (request : ScopedCollectionMachine.Request) (fuel : Nat) :
    ∀ jobs : ScopedCollectionMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:resume"
        [encoded (requestTerm request), number fuel, encoded (stateTerm jobs)])
      state (encoded (stateTerm (ScopedCollectionMachine.resume request fuel jobs)))
  | [] => by collection_machine_eval unfolding [ScopedCollectionMachine.resume]
  | job :: tail => by
      have first := run_returns state request.machine fuel job.state
      have later := resume_returns state request fuel tail
      cases job
      collection_machine_eval [first, later] unfolding [ScopedCollectionMachine.resume, List.map_cons]

@[metta_head "gslt:collection-machine:complete"]
theorem complete_returns (state : State) : ∀ jobs : ScopedCollectionMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:complete" [encoded (stateTerm jobs)])
      state (encoded (booleanTerm (ScopedCollectionMachine.complete jobs)))
  | [] => by collection_machine_eval unfolding [ScopedCollectionMachine.complete]
  | job :: tail => by
      have first := machine_complete_returns state job.state
      have later := complete_returns state tail
      cases done : GeneralScopedMatchMachine.complete job.state <;>
        rw [done] at first <;>
        collection_machine_eval [first, later] unfolding [ScopedCollectionMachine.complete, List.all_cons, done]

@[metta_head "gslt:collection-machine:receipts"]
theorem receipts_returns (state : State) (allocation : Allocation Pattern) :
    ∀ answers : List GeneralScopedMatchMachine.Answer,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:receipts"
        [encoded (allocationTerm InferenceCettaWire.encodePattern allocation), encoded (encodeList matcherAnswerTerm answers)])
      state (encoded (encodeList receiptTerm (answers.map fun answer => ⟨allocation, answer⟩)))
  | [] => by collection_machine_eval
  | answer :: tail => by
      collection_machine_eval [receipts_returns state allocation tail] unfolding [List.map_cons]

@[metta_head "gslt:collection-machine:publication"]
theorem publication_returns (state : State) : ∀ jobs : ScopedCollectionMachine.State,
    PureReturns library.runtime [] state
      (apply "gslt:collection-machine:publication" [encoded (stateTerm jobs)])
      state (encoded (encodeList receiptTerm (ScopedCollectionMachine.publication jobs)))
  | [] => by collection_machine_eval unfolding [ScopedCollectionMachine.publication]
  | job :: tail => by
      have first := receipts_returns state job.allocation job.state.answers
      have later := publication_returns state tail
      have joined := append_returns receiptTerm state
        (job.state.answers.map fun answer => ⟨job.allocation, answer⟩)
        (ScopedCollectionMachine.publication tail)
      cases job
      collection_machine_eval [first, later, joined] unfolding [
        ScopedCollectionMachine.publication, List.flatMap_cons]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.checked
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_source_quote
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProofInheritedHeads_derived
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_source_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_inherited_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_checked
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_equation_count
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.collectionMachineProof_not_closed
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.append_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.length_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.allocate_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.machine_agreement
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.run_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.machine_complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.allocation_state_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.jobs_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.raw_start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.start_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.resume_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.complete_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.receipts_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ScopedCollectionExecution.publication_returns
