import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorProgram

/-!
# The consuming equation captures the completed constructor value

The fresh source variable stores the whole annotated value. Its actual
contextual unifier supplies a finite model, from which the ordinary source
match and logical merge are obtained. The complete physical equation scan
retains this one consuming clause and excludes the producer's other head.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConsumerFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.SolutionTheory Spec.Bindings.ScopeObservation.ModelTransport
open HEDemandedConstructorEdge (space heldResult producer)
open HEDemandedConstructorInferred (environment rangeDemand)

def query : Entry.Value := .expression .active [.symbol "use-demand", heldResult]
def pattern : Atom := .expression [.symbol "use-demand", .var "value"]
def body : Atom := .var "value"

theorem value_closed : TypeSubst.typeVars heldResult.erase = [] := by
  simp [heldResult, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem query_closed : TypeSubst.typeVars query.erase = [] := by
  simp [query, heldResult, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem capture (before : Frame) (name : String) (fresh : name ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      Entry.Value.UnifyRel Policy.ready.rebuilding before.environment query
        (Entry.Value.ofAtom (.expression [.symbol "use-demand", .var name])) after.environment ∧
      after.read Policy.ready (.var name) = heldResult := by
  let after := HEFreshSyntaxBinding.bindFrame Policy.ready before name heldResult fresh (by simp [value_closed])
  have bound := HEFreshSyntaxBinding.source_binding Policy.ready before name heldResult fresh value_closed
  have stable := HEFreshSyntaxBinding.ground_substitution Entry.RebuildPolicy.preserve
    (Entry.Value.resolve before.environment) heldResult value_closed
  refine ⟨after, ?_, HEFreshSyntaxBinding.bound_read Policy.ready before name heldResult fresh value_closed Policy.ready⟩
  apply Entry.Value.UnifyRel.ordinary
  simp only [query, Entry.Value.ofAtom, List.map_cons, List.map_nil, Entry.Value.substitute,
    HEFreshSyntaxBinding.resolve_fresh before name fresh,
    Policy.ready, stable, Entry.Value.rebuildStatus]
  exact .expression (.cons (.ordinary (.identical (by simp [Entry.Value.substitute]))) (.cons bound (.nil _)))

/-- The source frontier and the contextual result frame are constructed
together. No result-frame identity or successful equation run is assumed. -/
theorem complete_frame (live : List Atom) (before : Frame) :
    ∃ (work : EquationWork) (after : Frame),
      EquationFrontierRel space live query.erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel Policy.ready.rebuilding before.environment query (Entry.Value.ofAtom work.pattern)
        after.environment ∧
      after.read Policy.ready (Entry.Value.ofAtom work.body) = heldResult := by
  let chosen := EquationFreshening.freshRule (EquationScope.visibleNames live query.erase before.bindings)
    5 pattern body
  have alpha := EquationFreshening.freshRule_alphaVariant live query.erase pattern body before.bindings 5
  change AlphaVariantRel live query.erase before.bindings pattern body chosen.1 chosen.2 at alpha
  obtain ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ := alpha
  have absent : rename "value" ∉ specBindingVars before.bindings := by
    intro present
    exact fresh "value" (Or.inr (.var "value"))
      ((EquationScope.mem_visibleNames_iff live query.erase before.bindings (rename "value")).mp
        ((EquationScope.visible_closed_iff query_closed (rename "value")).mpr (Or.inr present)))
  obtain ⟨captured, unified, read⟩ := capture before (rename "value") absent
  have sourceUnified : Entry.Value.UnifyRel Policy.ready.rebuilding before.environment query
      (Entry.Value.ofAtom chosen.1) captured.environment := by
    simpa only [EquationFreshening.alphaRename_eq renamedPattern, pattern, renameTypeVars, List.map_cons, List.map_nil] using unified
  let valuation := Theory.presentedValuation (Entry.Value.eraseEnvironment captured.environment)
  have model := Theory.normal_presentedValuation_satisfied captured.certified.normal
  have reached := (sourceUnified.solutions before.certified.normal valuation).mp model
  have incoming : TypeBindingSatisfied valuation before.bindings := (before.certified.theory valuation).mp reached.1
  have equation : applyTypeValuation valuation query.erase = applyTypeValuation valuation chosen.1 := by
    simpa only [Entry.Value.erase_ofAtom] using reached.2
  have modelEquation : HEAtomEquationSatisfied (fun name => encodeModelAtom (valuation name)) query.erase chosen.1 := by
    unfold HEAtomEquationSatisfied
    rw [← encodeModelAtom_applyTypeValuation, ← encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom equation
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨valuation, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel, incoming⟩
  let output : Bindings :=
    ⟨matched.assignments ++ before.bindings.assignments, matched.equalities ++ before.bindings.equalities⟩
  have candidate : UnifyCandidateRel query.erase (Entry.Value.ofAtom chosen.1).erase before.bindings output := by
    simpa only [Entry.Value.erase_ofAtom] using (show UnifyCandidateRel query.erase chosen.1 before.bindings output from
      ⟨matched, matching, merged⟩)
  let after : Frame := ⟨output, captured.environment, sourceUnified.certifies before.certified candidate⟩
  let work : EquationWork := ⟨5, pattern, body, chosen.1, chosen.2, output⟩
  have hit : EquationRowResultsRel live query.erase before.bindings 5 (.expression [.symbol "=", pattern, body]) [work] :=
    .hit 5 pattern body chosen.1 chosen.2 matched output
      ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ matching merged
  have miss : EquationRowResultsRel live query.erase before.bindings 3
      (.expression [.symbol "=", producer, HERepeatedFormalSource.call]) [] := by
    simpa [query, Entry.Value.erase, producer] using
      HERangeEquationFrontiers.different_head_miss live before.bindings 3
        "use-demand" "other-demand-result" [heldResult.erase] [] HERepeatedFormalSource.call (by decide)
  have scanned : EquationFrontierRel space live query.erase before.bindings
      ([[], [], [], [], [], [work]] : List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [space, Space.ofList, List.zipIdx_cons, List.zipIdx_nil]
    exact .cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
      (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
        (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
          (.cons miss
            (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _) (.cons hit .nil)))))
  refine ⟨work, after, by simpa using scanned, rfl, sourceUnified, ?_⟩
  change captured.read Policy.ready (Entry.Value.ofAtom chosen.2) = heldResult
  rw [EquationFreshening.alphaRename_eq renamedBody]
  simpa only [body, renameTypeVars, Entry.Value.ofAtom] using read

/-- The actual consuming equation returns its captured held value at the
retained demand without restarting the producer or inserting a new cast. -/
theorem consumer_call_with_marking_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy) (before : Frame) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.CallRel (HEDemandedReadInterface.environment reads minimal) space () live scope query rangeDemand before
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
  obtain ⟨work, after, frontier, bindings, unified, read⟩ := complete_frame (rangeDemand :: live) before
  have produced : Stateful.BoundaryRel (HEDemandedReadInterface.environment reads minimal) space () (rangeDemand :: live) scope
      (some query.erase) .producer (after.read (HEDemandedPublication.policy marking) (Entry.Value.ofAtom work.body)) after
      [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
    rw [HEDemandedPublication.read, read]
    apply Stateful.BoundaryRel.producerRaw
    simp [FunctionPending, Minimal.IsFunction, heldResult, Entry.Value.erase]
  have returned : Stateful.BoundaryBatchRel (HEDemandedReadInterface.environment reads minimal) space () live scope none
      (.returned query rangeDemand) [(heldResult, after)] [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .returned (.evaluate (by simp [heldResult, Entry.Value.erase, Atom.notReducible])
      (by simp [heldResult, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (HEDemandedConstructorInferred.demanded_reentry_with_marking_of_reads reads minimal marking after live scope))
  refine ⟨after, ?_⟩
  apply Stateful.CallRel.equations (works := [work])
  · simp [query, Entry.Value.erase, IsErrorRel]
  · simp [HEDemandedReadInterface.environment, WorldEnvironment.readOnly,
      NonGroundedCallRel, Minimal.HostCall, Completed.Controls.typedDispatch, query, Entry.Value.erase,
      Minimal.embeddedInstruction]
  · simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, id_eq] using frontier
  · simp
  · simpa only [List.append_nil] using
      (Stateful.EquationBodiesRel.cons (policy := HEDemandedPublication.policy marking)
        bindings unified produced returned Stateful.EquationBodiesRel.nil)

theorem consumer_call_with_marking (minimal : Minimal.Services) (marking : Entry.MarkPolicy) (before : Frame) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.CallRel (environment minimal) space () live scope query rangeDemand before
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) :=
  consumer_call_with_marking_of_reads HEDemandedConstructorInferred.historicalReads minimal marking before live scope

theorem consumer_call (minimal : Minimal.Services) (before : Frame) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.CallRel (environment minimal) space () live scope query rangeDemand before
        [(heldResult, after)] () (policy := Policy.ready) :=
  consumer_call_with_marking minimal .successes before live scope

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConsumerFrame
