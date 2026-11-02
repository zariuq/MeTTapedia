import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedSource

/-! Existing mailbox machine proofs run in the concrete sequential-library
stack with the same emitted module. Retained rows preserve actual dispatch,
argument demand and clause order; extra namespaces are excluded explicitly. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedTransport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit SpaceSemantics
open ErlangMailboxKernelSource (emitted)

private def extraPrefixes : List String :=
  ["gslt:snapshot:", "gslt:provider-cache:", "gslt:integer:", "gslt:word16:", "gslt:er:"]

def inherited (head : String) : Bool := !(extraPrefixes.any fun start => head.startsWith start)

def minimal : Program := CompleteEmission.runtime.append emitted

private theorem filtered_empty {α : Type} (items : List α) (keep : α → Bool)
    (checked : items.all (fun item => !keep item) = true) : items.filter keep = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro item member
  have rejected := List.all_eq_true.mp checked item member
  intro kept
  simp [kept] at rejected

theorem equations_retained : minimal.equations.filter (fun row => inherited row.head) =
    ErlangActorLinkedSource.emittedLibrary.runtime.equations.filter (fun row => inherited row.head) := by
  have hidden0 : SnapshotClosureExecution.source.program.equations.filter (fun row => inherited row.head) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden1 : ProviderCacheExecution.source.program.equations.filter (fun row => inherited row.head) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden2 : IntegerWordLibrarySource.integerSource.program.equations.filter (fun row => inherited row.head) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden3 : IntegerWordLibrarySource.wordSource.program.equations.filter (fun row => inherited row.head) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden4 : ErlangControllerSource.source.program.equations.filter (fun row => inherited row.head) = [] :=
    filtered_empty _ _ (by decide +kernel)
  change (CompleteEmission.runtime.equations ++ emitted.equations).filter (fun row => inherited row.head) =
    ((((((CompleteEmission.runtime.equations ++ SnapshotClosureExecution.source.program.equations) ++ ProviderCacheExecution.source.program.equations) ++ IntegerWordLibrarySource.integerSource.program.equations) ++ IntegerWordLibrarySource.wordSource.program.equations) ++ ErlangControllerSource.source.program.equations) ++ emitted.equations).filter (fun row => inherited row.head)
  simp only [List.filter_append, hidden0, hidden1, hidden2, hidden3, hidden4, List.append_nil]

theorem declarations_retained : minimal.declarations.filter (retainedCallDeclaration inherited) =
    ErlangActorLinkedSource.emittedLibrary.runtime.declarations.filter (retainedCallDeclaration inherited) := by
  have hidden0 : SnapshotClosureExecution.source.program.declarations.filter (retainedCallDeclaration inherited) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden1 : ProviderCacheExecution.source.program.declarations.filter (retainedCallDeclaration inherited) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden2 : IntegerWordLibrarySource.integerSource.program.declarations.filter (retainedCallDeclaration inherited) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden3 : IntegerWordLibrarySource.wordSource.program.declarations.filter (retainedCallDeclaration inherited) = [] :=
    filtered_empty _ _ (by decide +kernel)
  have hidden4 : ErlangControllerSource.source.program.declarations.filter (retainedCallDeclaration inherited) = [] :=
    filtered_empty _ _ (by decide +kernel)
  change (CompleteEmission.runtime.declarations ++ emitted.declarations).filter (retainedCallDeclaration inherited) =
    ((((((CompleteEmission.runtime.declarations ++ SnapshotClosureExecution.source.program.declarations) ++ ProviderCacheExecution.source.program.declarations) ++ IntegerWordLibrarySource.integerSource.program.declarations) ++ IntegerWordLibrarySource.wordSource.program.declarations) ++ ErlangControllerSource.source.program.declarations) ++ emitted.declarations).filter (retainedCallDeclaration inherited)
  simp only [List.filter_append, hidden0, hidden1, hidden2, hidden3, hidden4, List.append_nil]

theorem agreement : ProgramAgreementOn inherited minimal ErlangActorLinkedSource.emittedLibrary.runtime :=
  programAgreementOn_of_retained_rows inherited _ _ equations_retained declarations_retained

theorem closed : ProgramClosed inherited minimal := by
  have base : CompleteEmission.runtime.equations.all
      (fun row => inherited row.head && codeWithin inherited row.body) = true := by decide +kernel
  have body := CompleteEmissionCodeSupport.entry_bodies_supported ErlangMailboxKernelSource.spec
    ErlangMailboxKernelSource.name inherited
    (by intro tag member; exact List.all_eq_true.mp (by decide +kernel : WirePlanSupport.tags.all inherited = true) tag member)
    rfl (by decide +kernel)
  refine ⟨by decide +kernel, ?_⟩
  intro row member _
  rcases List.mem_append.mp member with first | later
  · exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp base row first)).2
  · exact List.all_eq_true.mp body row later

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedTransport
