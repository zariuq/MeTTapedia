import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessBoundary
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEInvocationFrontier

/-!
# Ordered collection of earned first-success regions

The existing scoped source/worker relation retains the returned atom together
with its logical binding theory. The existing three-class output frontier
normalizer preserves that relation, including order and duplicate occurrences.
It is applied only to completed region outputs, not to operand/control prefixes.

The source-side output observation here explicitly uses the same native
success/error/Empty policy. This does not identify that policy with the older
binary selector on mixed Empty batches. A structural source derivation earns
both the worker run and the collected public result; a whole-run equality is
not an admission premise. Re-normalizing already binary-selected results does
not recover information discarded earlier; a control below witnesses that
failure. Native call-node correspondence must therefore connect the correct
pre-selection frontier, or prove that the admitted result excludes that case.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessCollectedRegions

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy.ScopedRetainedRelation
open Mettapedia.Languages.MeTTa.HE.FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication
open Mettapedia.Machines.HEFrontierNormalization

def sourceClassify (reply : Completed.Result) : Kind :=
  if isEmptyAtom reply.1.erase then .empty
  else if isErrorAtom reply.1.erase then .error else .success

def sourceNormalize (rows : List Completed.Result) : List Completed.Result :=
  reference sourceClassify rows

theorem classify_related {worker : ResultPair} {source : Completed.Result}
    (related : ScopedResultRel worker source) :
    HEInvocationFrontier.classify worker = sourceClassify source := by
  simp only [HEInvocationFrontier.classify, sourceClassify, related.1]

theorem filter_related (predicate : Kind → Bool) {workers : ResultSet} {sources : List Completed.Result}
    (related : List.Forall₂ ScopedResultRel workers sources) :
    List.Forall₂ ScopedResultRel
      (workers.filter fun row => predicate (HEInvocationFrontier.classify row))
      (sources.filter fun row => predicate (sourceClassify row)) := by
  induction related with
  | nil => exact .nil
  | @cons worker source workers sources here rest ih =>
      simp only [List.filter_cons, classify_related here]
      cases predicate (sourceClassify source) <;> simp only [Bool.false_eq_true, if_false, if_true]
      · exact ih
      · exact .cons here ih

theorem any_related (predicate : Kind → Bool) {workers : ResultSet} {sources : List Completed.Result}
    (related : List.Forall₂ ScopedResultRel workers sources) :
    workers.any (fun row => predicate (HEInvocationFrontier.classify row)) =
      sources.any (fun row => predicate (sourceClassify row)) := by
  induction related with
  | nil => rfl
  | cons here rest ih => simp only [List.any_cons, classify_related here, ih]

/-- The normalizer transports complete results, never merely their payloads
or an unordered set of successful values. -/
theorem normalize_related {workers : ResultSet} {sources : List Completed.Result}
    (related : List.Forall₂ ScopedResultRel workers sources) :
    List.Forall₂ ScopedResultRel (HEInvocationFrontier.normalize workers) (sourceNormalize sources) := by
  rw [HEInvocationFrontier.normalize_eq_frontier, ← HEInvocationFrontier.reference_eq_frontier]
  unfold sourceNormalize
  rw [reference_priority, reference_priority]
  have successes := any_related (fun kind => kind == .success) related
  have errors := any_related (fun kind => kind == .error) related
  change workers.any (isSuccess HEInvocationFrontier.classify) =
    sources.any (isSuccess sourceClassify) at successes
  change workers.any (isError HEInvocationFrontier.classify) =
    sources.any (isError sourceClassify) at errors
  rw [successes, errors]
  split
  · exact filter_related (fun kind => kind == .success) related
  · split
    · exact filter_related (fun kind => kind == .error) related
    · exact filter_related (fun kind => kind == .empty) related

theorem collected_public_theory {workers : ResultSet} {sources : List Completed.Result}
    (related : List.Forall₂ ScopedResultRel workers sources) (callerScope : List String) :
    (HEInvocationFrontier.normalize workers).map (workerResultTheory callerScope) =
      (sourceNormalize sources).map (RecursiveExecution.Contextual.Protocol.resultTheory callerScope) :=
  ScopedResultRel.forall2_resultTheory_eq (normalize_related related) callerScope

/-- Ordered argument alternatives contribute their entire result blocks.
Selection is applied after concatenating the blocks, not at each argument
alternative. The incoming index can include its retained binding record. -/
theorem ordered_blocks_related {Input : Type} (inputs : List Input)
    (workers : Input → ResultSet) (sources : Input → List Completed.Result)
    (related : ∀ input ∈ inputs, List.Forall₂ ScopedResultRel (workers input) (sources input)) :
    List.Forall₂ ScopedResultRel
      (HEInvocationFrontier.normalize (inputs.flatMap workers))
      (sourceNormalize (inputs.flatMap sources)) := by
  apply normalize_related
  induction inputs with
  | nil => exact .nil
  | cons input inputs ih =>
      simpa only [List.flatMap_cons] using
        List.rel_append (related input (by simp)) (ih (fun i member => related i (by simp [member])))

section Earned

variable {space : Space} {dispatch : Mettapedia.Languages.MeTTa.HE.GroundedDispatch}
  {hostDispatch : Spec.Eval.GroundedDispatch} {policy : Completed.Policy}
  {wEmitted : ResultSet} {cEmitted : List Completed.Result}
  {fuel steps : Nat} {wLive cLive : List Atom} {scope : List String}
  {value : Atom} {ctxVal : Entry.Value} {expected : Atom}
  {wB : Bindings} {cFrame : Completed.Frame}
  {wStack : List RecursiveTasks.Frame}
  {cStack : List RecursiveTasks.Contextual.Continuation}
  {wResults : ResultSet} {cResults : List Completed.Result}

/-- The admission family derives the actual retained worker region and its
independent source execution. Collection then transports their complete
ordered output observation. An unchanged caller stack and emitted prefix
remain part of the worker endpoint. -/
theorem earned_collected_region
    (derivation : ScopedAtomDerivation space dispatch hostDispatch policy
      wEmitted cEmitted fuel wLive cLive scope value ctxVal expected wB cFrame
      wStack cStack steps wResults cResults) (callerScope : List String) :
    (∀ budget,
      (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        (steps + budget) ⟨space, .work (.atom value expected wB fuel wLive), wStack, wEmitted⟩ =
      (FirstSuccessRecursiveExecution.Checked.machine dispatch FirstSuccessRecursiveExecution.scopedTypes).run
        budget ⟨space, .returning wResults, wStack, wEmitted⟩) ∧
    Completed.AtomRel space hostDispatch Completed.scopedLookup cLive scope
      ctxVal expected cFrame cResults (policy := policy) ∧
    (HEInvocationFrontier.normalize wResults).map (workerResultTheory callerScope) =
      (sourceNormalize cResults).map (RecursiveExecution.Contextual.Protocol.resultTheory callerScope) := by
  obtain ⟨workerRun, sourceRun, _, related⟩ := FirstSuccessBoundary.earned_region derivation
  exact ⟨workerRun, sourceRun, collected_public_theory related callerScope⟩

end Earned

namespace Controls

def workerReply (value : Atom) : ResultPair := (value, Bindings.empty)
def sourceReply (value : Atom) : Completed.Result := (Entry.Value.ofAtom value, Completed.Frame.empty)

theorem replies_related (value : Atom) : ScopedResultRel (workerReply value) (sourceReply value) := by
  refine ⟨by simp [workerReply, sourceReply], ?_⟩
  exact SourceBindingComparison.FrameRelated.of_principal PrincipalBindingFrame.empty (.refl _)

def good : Atom := .grounded (.int 4)
def error : Atom := Atom.error (.symbol "call") (.symbol "BadType")

theorem duplicates_survive_source_and_worker :
    HEInvocationFrontier.normalize [workerReply good, workerReply error, workerReply good] =
        [workerReply good, workerReply good] ∧
      sourceNormalize [sourceReply good, sourceReply error, sourceReply good] =
        [sourceReply good, sourceReply good] := by
  constructor
  · rfl
  · simp [sourceNormalize, reference, removeEmpty, isSuccess, isEmpty, isError,
      sourceClassify, sourceReply, good, error, isEmptyAtom, isErrorAtom, Atom.empty, Atom.error]

theorem mixed_empty_uses_declared_output_policy :
    HEInvocationFrontier.normalize [workerReply Atom.empty, workerReply error] = [workerReply error] ∧
      sourceNormalize [sourceReply Atom.empty, sourceReply error] = [sourceReply error] := by
  constructor
  · rfl
  · simp [sourceNormalize, reference, removeEmpty, isSuccess, isEmpty,
      sourceClassify, sourceReply, error, isEmptyAtom, isErrorAtom, Atom.empty, Atom.error]

theorem output_deduplication_changes_occurrences :
    HEInvocationFrontier.normalize [workerReply good, workerReply good] ≠ [workerReply good] := by
  decide +kernel

/-- The output adapter cannot repair an earlier use of the wrong selector.
The binary model discards the error before the native normalizer can see it. -/
theorem binary_preselection_loses_native_fallback :
    HEInvocationFrontier.normalize
        (HEReturns.keep [workerReply Atom.empty, workerReply error]) = [workerReply Atom.empty] ∧
      HEInvocationFrontier.normalize [workerReply Atom.empty, workerReply error] = [workerReply error] ∧
      HEInvocationFrontier.normalize
        (HEReturns.keep [workerReply Atom.empty, workerReply error]) ≠
          HEInvocationFrontier.normalize [workerReply Atom.empty, workerReply error] := by
  decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.FirstSuccessCollectedRegions
