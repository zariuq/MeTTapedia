import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredAdequacy

/-!
# Inferred range controls and a real source-equation mutation

The negative program changes physical equation row three to a ground early
return for the same call. Its typing declarations are unchanged. The source
and worker derive the mutant result rather than merely comparing two lists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredControls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Bindings.ScopeObservation
open Spec.Match.Merge
open RetainedTypePayloads (ExternalView)
open HERangeSourceProgram (space)
open HERangeSuperposeSource (NumericOrEmpty)

def query : Atom := .expression [.symbol "range", .grounded (.int 0), .grounded (.int 2)]
def queryValue : Entry.Value := Entry.Value.ofAtom query
def mutantRule : Atom := .expression [.symbol "=", query, .symbol "Empty"]
def mutantSpace : Space := Space.ofList (space.atoms.set 3 mutantRule)
def mutantWork (before : Frame) : EquationWork := ⟨3, query, .symbol "Empty", query, .symbol "Empty", before.bindings⟩

def mutantEnvironment (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom) :
    WorldEnvironment Space Unit :=
  { (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment with
    view := fun _ _ => mutantSpace }

theorem declarations_unchanged (subject : Atom) :
    mutantSpace.atoms.filterMap (annotationType? subject) = space.atoms.filterMap (annotationType? subject) := rfl

theorem query_value : queryValue = HERangeUntypedEntry.rangeCall 0 2 := by
  simp [queryValue, query, Entry.Value.ofAtom, HERangeUntypedEntry.rangeCall]

theorem mutant_alpha (live : List Atom) (before : Bindings) :
    AlphaVariantRel live query before query (.symbol "Empty") query (.symbol "Empty") := by
  refine ⟨id, Function.injective_id, ?_, .symbol "Empty", ?_⟩
  · exact .expression (.cons (.symbol "range") (.cons (.grounded (.int 0)) (.cons (.grounded (.int 2)) .nil)))
  · intro name occurs
    rcases occurs with first | second
    · have present := atomOccurs_mem_typeVars first
      simp [query, TypeSubst.typeVars, TypeSubst.typeVarsList] at present
    · have present := atomOccurs_mem_typeVars second
      simp [TypeSubst.typeVars] at present

theorem mutant_frontier (live : List Atom) (before : Frame) :
    EquationFrontierRel mutantSpace live query before.bindings [mutantWork before] := by
  have merge : MergeRel equalityGroundedSemantic Bindings.empty Bindings.empty Bindings.empty :=
    .mk (by simp [constraints, Bindings.empty]) .nil
  have scalar (value : Int) : MatchRel equalityGroundedSemantic (.grounded (.int value)) (.grounded (.int value)) Bindings.empty :=
    .groundedLeftCustom (by simp [isVariableB]) (by simp [equalityGroundedSemantic]) ⟨rfl, rfl⟩ semanticLoopFree_empty
  have matched : MatchRel equalityGroundedSemantic query query Bindings.empty :=
    .expression (.cons (.symSym "range" semanticLoopFree_empty) merge
      (.cons (scalar 0) merge (.cons (scalar 2) merge .nil))) semanticLoopFree_empty
  have hit : EquationRowResultsRel live query before.bindings 3 mutantRule [mutantWork before] :=
    .hit 3 query (.symbol "Empty") query (.symbol "Empty") Bindings.empty before.bindings
      (mutant_alpha live before.bindings) matched ⟨BindingSourceAgreement.refl _, before.certified.satisfiable⟩
  have scanned : EquationFrontierRel mutantSpace live query before.bindings
      ([[], [], [], [mutantWork before], [], [], [], []] : List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [mutantSpace, HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace,
      HEIfSourceSelection.Range.space, Space.ofList, List.cons_append, List.nil_append,
      List.set, List.zipIdx_cons, List.zipIdx_nil]
    exact .cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
      (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
        (.cons (HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _)
          (.cons hit
            (.cons (HERangeEquationFrontiers.different_head_miss live before.bindings 4 "range" "if" _ _ _ (by decide))
              (.cons (HERangeEquationFrontiers.different_head_miss live before.bindings 5 "range" "if" _ _ _ (by decide))
                (.cons (HERangeSourceProgram.declaration_irrelevant _ _ _ _)
                  (.cons (HERangeEquationFrontiers.different_head_miss live before.bindings 7 "range" "empty" _ _ _ (by decide)) .nil)))))))
  simpa using scanned

theorem mutant_call (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (expected : Atom) :
    Stateful.CallRel (mutantEnvironment minimal world active primitive unobservedClosure) space () live scope queryValue expected before
      [(.symbol "Empty", before)] () (policy := policy) := by
  let current := mutantEnvironment minimal world active primitive unobservedClosure
  have read : before.read policy (.symbol "Empty") = .symbol "Empty" := by simp [Frame.read, Entry.Value.substitute]
  have unified : Entry.Value.UnifyRel policy.rebuilding before.environment queryValue
      (Entry.Value.ofAtom (mutantWork before).pattern) before.environment := .ordinary (.identical rfl)
  have producer : Stateful.BoundaryRel current space () (expected :: live) scope (some queryValue.erase) .producer
      (before.read policy (Entry.Value.ofAtom (mutantWork before).body)) before [(.symbol "Empty", before)] () (policy := policy) := by
    simpa [mutantWork, Entry.Value.ofAtom, read] using
      (Stateful.BoundaryRel.producerRaw (environment := current) (value := Entry.Value.symbol "Empty") (frame := before)
        (by simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase]))
  have returned : Stateful.BoundaryBatchRel current space () live scope none (.returned queryValue expected)
      [(.symbol "Empty", before)] [(.symbol "Empty", before)] () (policy := policy) := by
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .returned (.stopped (by simp [Entry.Value.erase, IsEmptyOrErrorRel, Atom.empty]))
  apply Stateful.CallRel.equations (works := [mutantWork before])
  · simp [queryValue, query, Entry.Value.erase_ofAtom, IsErrorRel]
  · simp [NonGroundedCallRel, Minimal.HostCall, mutantEnvironment, HERangeInferredProtocol.ports,
      HERangeAdmissionBoundary.environment, HERangeSourceProgram.environment, HERangeSourceProgram.dispatch,
      queryValue, query, Entry.Value.erase_ofAtom, Minimal.embeddedInstruction]
  · simpa only [mutantEnvironment, queryValue, Entry.Value.erase_ofAtom] using mutant_frontier (expected :: live) before
  · simp
  · simpa only [List.append_nil] using Stateful.EquationBodiesRel.cons (work := mutantWork before)
      rfl unified producer returned Stateful.EquationBodiesRel.nil

theorem mutant_source (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) :
    Stateful.AtomRel (mutantEnvironment minimal world active primitive unobservedClosure) space () live scope
      (HERangeUntypedEntry.rangeCall 0 2) Atom.undefinedType before [(.symbol "Empty", before)] () (policy := policy) := by
  let current := mutantEnvironment minimal world active primitive unobservedClosure
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  have numberSource (childLive : List Atom) (value : Int) :
      Stateful.AtomRel current space () childLive scope (.grounded (.int value)) Atom.undefinedType before
        [(.grounded (.int value), before)] () (policy := policy) :=
    HERangeSuperposeSource.number_undefined_of_query current policy before childLive scope value
      (HERangeAdmissionBoundary.number_query currentOps world _ before value _)
  have headSource (childLive : List Atom) :
      Stateful.AtomRel current space () childLive scope (.symbol "range") Atom.undefinedType before
        [(.symbol "range", before)] () (policy := policy) :=
    HERangeUntypedEntry.symbol_undefined_of_query current space () policy before childLive scope "range" (by decide)
      (HERangeInferredProtocol.undefined_head world active primitive unobservedClosure _ before "range" (Or.inl rfl))
  have finish (childLive : List Atom) : Stateful.TupleRel current space () childLive scope [.grounded (.int 2)] before
      [(.expression .active [.grounded (.int 2)], before)] () (policy := policy) := by
    simpa [Completed.tupleSingleton, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      Stateful.TupleRel.singleton (numberSource childLive 2)
  have tail (childLive : List Atom) : Stateful.TupleRel current space () childLive scope
      [.grounded (.int 0), .grounded (.int 2)] before
      [(.expression .active [.grounded (.int 0), .grounded (.int 2)], before)] () (policy := policy) := by
    apply Stateful.TupleRel.cons (numberSource _ 0)
    simpa [tuplePrepend, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      Stateful.TupleBranchesRel.continuing (head := (Entry.Value.grounded (.int 0), before))
        (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (finish ((Entry.Value.grounded (.int 0)).erase :: childLive)) Stateful.TupleBranchesRel.nil
  have tuple : Stateful.TupleRel current space () (Atom.undefinedType :: live) scope
      [.symbol "range", .grounded (.int 0), .grounded (.int 2)] before [(queryValue, before)] () (policy := policy) := by
    apply Stateful.TupleRel.cons (headSource _)
    simpa [tuplePrepend, queryValue, query, Entry.Value.ofAtom, Entry.Value.erase,
      isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      Stateful.TupleBranchesRel.continuing (head := (Entry.Value.symbol "range", before))
        (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (tail ((Entry.Value.symbol "range").erase :: Atom.undefinedType :: live)) Stateful.TupleBranchesRel.nil
  exact HERangeUntypedEntry.atom_of_call_in current space () policy before live scope "range"
    [.grounded (.int 0), .grounded (.int 2)] queryValue Atom.undefinedType [(.symbol "Empty", before)]
    (by decide) (by decide) (by decide)
    (by simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])
    (HERangeInferredProtocol.undefined_head world active primitive unobservedClosure _ before "range" (Or.inl rfl)) tuple
    (mutant_call minimal world active primitive unobservedClosure policy before live scope Atom.undefinedType)
    (by intro row member; cases List.mem_singleton.mp member; exact .empty)

/-- The mutated source equation runs to a completed publication and fails
the original interval observation and its exact answer counter. -/
theorem mutant_finished_rejects_interval (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) :
    let current := mutantEnvironment minimal world active primitive unobservedClosure
    RecursiveMachine.Contextual.WorldSteps current.view current.services current.dispatch current.lookup policy
      ⟨(), space, .work (.atom live scope (HERangeUntypedEntry.rangeCall 0 2) Atom.undefinedType before), [], []⟩
      ⟨(), space, .returning [], [], [(.symbol "Empty", before)]⟩ (admission := current.arguments) ∧
    [Entry.Value.symbol "Empty"] ≠ HERangeSourceAdequacy.values 0 2 ++ [.symbol "Empty"] ∧
    ([((Entry.Value.symbol "Empty"), before)] : List Result).length ≠ 3 := by
  let current := mutantEnvironment minimal world active primitive unobservedClosure
  have loaded : (RecursiveTasks.Contextual.WorldConfiguration.mk () space
      (.work (.atom live scope (HERangeUntypedEntry.rangeCall 0 2) Atom.undefinedType before)) [] []).SourceRel
      current policy [(.symbol "Empty", before)] () :=
    ⟨_, _, (), .work (mutant_source minimal world active primitive unobservedClosure policy before live scope), .nil _, rfl⟩
  refine ⟨RecursiveExecution.Contextual.Stateful.source_to_finished loaded, ?_, by simp⟩
  intro same
  have lengths := congrArg List.length same
  simp [HERangeSourceAdequacy.values] at lengths

theorem crosses_zero_with_saved_alias (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom) (policy : Policy) :
    let current := (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment
    ∃ rows : List Result,
      Stateful.AtomRel current space () [.var "x", .var "y"] ["x", "y"]
        (HERangeUntypedEntry.rangeCall (-2) 2) Atom.undefinedType Completed.Controls.argumentAliasFrame rows () (policy := policy) ∧
      rows.map Prod.fst = [.grounded (.int (-2)), .grounded (.int (-1)), .grounded (.int 0), .grounded (.int 1), .symbol "Empty"] := by
  obtain ⟨rows, source, _, observed⟩ := HERangeInferredAdequacy.source minimal world active primitive unobservedClosure
    policy Completed.Controls.argumentAliasFrame [.var "x", .var "y"] ["x", "y"] (-2) 2 Atom.undefinedType (Or.inr rfl)
  exact ⟨rows, source, by simpa [HERangeSourceAdequacy.values, List.range_succ] using observed⟩

theorem descending_still_publishes_empty (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) :
    let current := (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment
    ∃ rows : List Result,
      Stateful.AtomRel current space () live scope (HERangeUntypedEntry.rangeCall 3 (-2)) (.symbol "Number") before rows () (policy := policy) ∧
      rows.map Prod.fst = [.symbol "Empty"] := by
  obtain ⟨rows, source, _, observed⟩ := HERangeInferredAdequacy.source minimal world active primitive unobservedClosure
    policy before live scope 3 (-2) (.symbol "Number") (Or.inl rfl)
  exact ⟨rows, source, by simpa [HERangeSourceAdequacy.values] using observed⟩

theorem duplicate_occurrences_retained (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (value : Int) :
    let current := (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment
    Stateful.AtomRel current space () live scope
      (HERangeSuperposeSource.call [.grounded (.int value), .grounded (.int value)]) Atom.undefinedType before
      [(.grounded (.int value), before), (.grounded (.int value), before)] () (policy := policy) := by
  let ports := HERangeInferredProtocol.ports minimal world active primitive unobservedClosure
  have child : ¬FunctionPending policy (.grounded (.int value)) ∧
      (Entry.Value.grounded (.int value)).erase ≠ Atom.notReducible ∧
      ¬IsEmptyOrErrorRel (Entry.Value.grounded (.int value)).erase ∧
      Stateful.AtomRel ports.environment space () live scope (.grounded (.int value)) Atom.undefinedType before
        [(.grounded (.int value), before)] () (policy := policy) := by
    refine ⟨?_, ?_, ?_, ports.number policy before live scope value⟩ <;>
      simp [FunctionPending, Minimal.IsFunction, Entry.Value.erase, Atom.notReducible, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append] using
    ports.superpose policy before live scope [.grounded (.int value), .grounded (.int value)]
      [[(.grounded (.int value), before)], [(.grounded (.int value), before)]] Atom.undefinedType
      (by decide) (by decide) (by simp [Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList])
      (by simp) (.cons child (.cons child .nil))
      (by
        intro row member
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append,
          List.mem_cons, List.not_mem_nil, or_false, or_self] at member
        cases member
        exact .number value)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredControls
