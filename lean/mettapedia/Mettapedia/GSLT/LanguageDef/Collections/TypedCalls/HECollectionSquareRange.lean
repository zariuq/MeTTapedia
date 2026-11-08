import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareBatches

/-! The actual typed square call evaluates its authored range operand.
Static admission sees the raw producer's Undefined type; dynamic argument
delivery executes range at Number and retains each resulting frame. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareRange

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Mettapedia.Machines.OrderedProtocol.Completion
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HERangeSuperposeSource (NumericOrEmpty)

def signature : SelectedTypePolicy :=
  ⟨CollectionStdlibSource.squareType, [.symbol "Number"], .symbol "Number", rfl⟩

def call (lower upper : Int) : Entry.Value :=
  .expression .active [.symbol "sq", HERangeUntypedEntry.rangeCall lower upper]

def squares (lower : Int) (count : Nat) : List Entry.Value :=
  (List.range count).map (fun (index : Nat) => .grounded (.int ((lower + index) * (lower + index))))

theorem call_closed (lower upper : Int) : TypeSubst.typeVars (call lower upper).erase = [] := by
  simp [call, HERangeUntypedEntry.rangeCall, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem call_read (policy : Policy) (before : Frame) (lower upper : Int) :
    before.read policy (call lower upper) = call lower upper :=
  HECollectionClosedAppend.closed_read policy before _ (call_closed lower upper)

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem argument_admission (scope : List String) (policy : Policy) (before : Frame) (lower upper : Int) :
    KindArgumentAdmissionRel sourceSpace ((current).lookup scope sourceSpace) policy (call lower upper).erase
      (HERangeUntypedEntry.rangeCall lower upper).erase (.symbol "Number") 1 before [before] [] := by
  apply HEArgumentMetatypeRole.singleton_inferred
  · intro kind _ cut
    have success := HEArgumentMetatypeRole.native_cut cut
    have absent : TypeScopeMatcher.metaCheckAtom (.symbol "Number") kind = none := rfl
    rw [absent] at success
    cases success
  · simpa only [HERangeUntypedEntry.rangeCall, Entry.Value.erase, List.map_cons, List.map_nil, environment] using
      HECollectionInferredQueries.range_query ops external scope before lower upper (.symbol "Number")
  · exact .unchanged (before.preserved_type_match policy (.undefinedRight _ _))

theorem selection (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom)
    (matched : TypeMatchRel expected (.symbol "Number") before.bindings before.bindings) :
    (current).arguments.selection sourceSpace (current).lookup policy live scope (call lower upper).erase
      (.symbol "sq") expected before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (call lower upper).erase expected before.bindings
  refine ⟨[signature.functionType], HECollectionInferredQueries.closed_head ops external names before "sq" _ _ rfl rfl,
    .selected (errors := []) ?_ (by simp)⟩
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (call lower upper).erase 1 [(HERangeUntypedEntry.rangeCall lower upper).erase] [.symbol "Number"] [before] [before] [] :=
    .cons (AdmissionFramesRel.single (argument_admission minimal nativePolicy external active primitive subtypes names policy before lower upper)) .nil
  simpa [signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := (call lower upper).erase)
      (expected := expected) (selected := signature) (before := before) (operator := .symbol "sq")
      (arguments := [(HERangeUntypedEntry.rangeCall lower upper).erase]) (by simp [call, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy matched))) .nil)

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ output : List Result,
      Stateful.AtomRel current sourceSpace world live scope (call lower upper) expected before output world (policy := policy) ∧
      (∀ row ∈ output, NumericOrEmpty row.1) ∧
      output.map Prod.fst = squares lower (upper - lower).toNat ++ [.symbol "Empty"] := by
  let argumentLive := Atom.symbol "sq" :: invocationReturnType signature :: live
  obtain ⟨rows, rangeRun, numeric, seen⟩ := HECollectionRange.source minimal nativePolicy external active primitive subtypes
    world policy before argumentLive scope lower upper (.symbol "Number") (Or.inl rfl)
  have argumentsRun : Stateful.ArgumentsRel current sourceSpace world argumentLive scope
      [(HERangeUntypedEntry.rangeCall lower upper, .symbol "Number")] before (rows.map HECollectionSquareBatches.packet) world (policy := policy) := by
    apply Stateful.ArgumentsRel.cons
    · simpa only [argumentScope, List.flatMap_nil, List.nil_append] using rangeRun
    · exact HECollectionSquareBatches.argument_branches minimal nativePolicy external active primitive subtypes
        world policy argumentLive scope lower upper rows numeric
  obtain ⟨output, callsRun, outputNumeric, values⟩ := HECollectionSquareBatches.calls minimal nativePolicy external active primitive subtypes
    world policy live scope rows numeric
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      (output.map (readResult policy)) output := by
    rw [HERangeSuperposeSource.numeric_reads policy output outputNumeric]
    exact HERangeSuperposeSource.numeric_priority output outputNumeric
  have matched : TypeMatchRel expected (.symbol "Number") before.bindings before.bindings := by
    rcases demand with same | same
    · rw [same]; exact same_symbol_type_match "Number" before.bindings (by decide) (by decide)
    · rw [same]; exact .undefinedLeft _ _
  have entry : Entry.Rel policy.reentry (before.read policy (call lower upper)).status
      (before.read policy (call lower upper)).erase expected .interpret := by
    rw [call_read]
    simp only [call, Entry.Value.erase, Entry.Value.status, List.map_cons, List.map_nil]
    apply Entry.Rel.expression
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · rcases demand with rfl | rfl <;> decide
    · exact Or.inr rfl
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy sourceSpace world world world world
    live scope (call lower upper) expected before before before .active (.symbol "sq") (.symbol "sq")
    [HERangeUntypedEntry.rangeCall lower upper] signature (rows.map HECollectionSquareBatches.packet) output output
    entry (by rw [call_read]; rfl)
    (by simpa only [call_read, Entry.Value.erase, environment, id_eq] using
      selection minimal nativePolicy external active primitive subtypes policy before live scope lower upper expected matched)
    rfl (HECollectionArithmetic.closed_operator minimal nativePolicy external active primitive subtypes world policy _ _ before
      "sq" signature.functionType (by decide) (by decide) (by decide) rfl rfl)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (by simpa only [signature, invocationReturnType, argumentLive, List.zip_cons_cons, List.zip_nil_left,
        Entry.Value.erase] using argumentsRun)
    (by simpa [signature, invocationReturnType, Atom.expressionType] using callsRun) priority
  refine ⟨output, ?_, outputNumeric, ?_⟩
  · simpa only [HERangeSuperposeSource.numeric_publishes policy _ output outputNumeric] using complete
  · rw [values]
    have mapped := congrArg (List.map HECollectionSquareBatches.squared) seen
    simpa [List.map_map, Function.comp_def, List.map_append, HERangeSourceAdequacy.values, squares,
      HECollectionSquareBatches.squared] using mapped

theorem retained_run (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ output : List Result,
      RecursiveMachine.Contextual.WorldSteps (current).view (current).services (current).dispatch (current).lookup policy
        ⟨world, sourceSpace, .work (.atom live scope (call lower upper) expected before), stack, emitted⟩
        ⟨world, sourceSpace, .returning output, stack, emitted⟩ (admission := (current).arguments) ∧
      output.map Prod.fst = squares lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      output.length = (upper - lower).toNat + 1 := by
  obtain ⟨output, executed, _, seen⟩ := source minimal nativePolicy external active primitive subtypes world policy before live scope lower upper expected demand
  refine ⟨output, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.atom_complete executed stack) emitted, seen, ?_⟩
  have length := congrArg List.length seen
  simpa [squares] using length

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareRange
