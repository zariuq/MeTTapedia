import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshRangeAlias
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEAssignedRangeReturn
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectedConstructorSource

/-!
# A constructor whose two formals share one private type variable

The two argument positions share a selected type frame. Fresh operator
lookup introduces another name, and both middle occurrences are matched.
The raw match records both equalities; the enclosing source merge sees the
deduplicated constraint packet. No suffix-only arrow lemma is applied here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERepeatedFormalSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation
open Spec.Match.Merge Spec.Eval Spec.Eval.Completed

def signature (name : String) : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [.var name, .var name] (.symbol "DemandRange"),
    [.var name, .var name], .symbol "DemandRange", rfl⟩

def aliases (left right : String) : Bindings := Bindings.empty.addEquality left right
def twiceAliases (left right : String) : Bindings := (aliases left right).addEquality left right

theorem repeat_empty_alias (left right : String) :
    MergeRel equalityGroundedSemantic (aliases left right) (aliases left right) (twiceAliases left right) := by
  apply MergeRel.mk (order := [.equality left right])
  · simp [aliases, constraints, Bindings.empty, Bindings.addEquality, List.eraseDups_cons]
  · apply MergeConstraintsRel.equality (next := twiceAliases left right)
    · apply AddVarEqualityRel.consistent (values := [])
      · simp [aliases, Bindings.classValues, Bindings.empty, Bindings.addEquality, Bindings.lookup]
      · trivial
    · exact .nil

theorem arrow_match (left right : String) :
    MatchRel equalityGroundedSemantic (signature left).functionType (signature right).functionType
      (twiceAliases left right) := by
  apply MatchRel.expression
  · exact .cons (.symSym "->" semanticLoopFree_empty)
      (.mk (by simp [constraints, Bindings.empty]) .nil)
      (.cons (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
        (HEFreshRangeAlias.empty_alias_merge left right)
        (.cons (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
          (repeat_empty_alias left right)
          (.cons (.symSym "DemandRange" semanticLoopFree_empty)
            (.mk (by simp [constraints, Bindings.empty]) .nil) .nil)))
  · exact semanticLoopFree_of_assignments_nil rfl

theorem repeated_constraint_packet (left right : String) :
    constraints (twiceAliases left right) = constraints (aliases left right) := by
  simp [constraints, twiceAliases, aliases, Bindings.addEquality, Bindings.empty, List.eraseDups_cons]

theorem arrow_source_match (before : Frame) (left right : String)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number"))
    (fresh : right ∉ specBindingVars before.bindings) :
    TypeMatchRel (signature left).functionType (signature right).functionType before.bindings
      (before.bindings.addEquality left right) := by
  apply TypeMatchRel.structural
    (by simp [signature, CompletedDelivery.arrowType, Atom.undefinedType])
    (by simp [signature, CompletedDelivery.arrowType, Atom.atomType])
    (by simp [signature, CompletedDelivery.arrowType, Atom.undefinedType])
    (by simp [signature, CompletedDelivery.arrowType, Atom.atomType])
    (arrow_match left right)
  apply (mergeRel_iff_of_constraints_perm
    (p := equalityGroundedSemantic) (left := before.bindings)
    (show (constraints (twiceAliases left right)).Perm (constraints (aliases left right)) by
      rw [repeated_constraint_packet])).mpr
  exact HEFreshRangeAlias.alias_merge before.bindings left right (.symbol "Number") isolated assigned fresh

theorem first_number_frame (policy : Policy) (name : String) :
    ∃ after : Frame,
      after.bindings = Bindings.empty.assign name (.symbol "Number") ∧
      Frame.TypeRenewRel policy (.var name) (.symbol "Number") Frame.empty after ∧
      after.bindings.classValues name = [.symbol "Number"] := by
  have source := TypeMatchRel.expected_variable_symbol name "Number" Bindings.empty
    (by decide) (by decide) (by simp [Bindings.classValues, Bindings.empty, Bindings.lookup])
  have model : ∃ valuation, TypeBindingSatisfied valuation (Bindings.empty.assign name (.symbol "Number")) := by
    simpa only [Frame.empty, HEFreshRangeFrame.assign_eq_extend Bindings.empty name (.symbol "Number")
      (by simp [specBindingVars, Bindings.empty])] using
      HEFreshRangeFrame.extended_model Frame.empty name (.symbol "Number") rfl
        (by simp [Frame.empty, specBindingVars, Bindings.empty])
  have policyMatch : policy.matching.Rel (.var name) (.symbol "Number") Frame.empty.bindings
      (Bindings.empty.assign name (.symbol "Number")) := by
    cases policy.matching with
    | raw => exact source
    | finite => exact ⟨source, model⟩
  obtain ⟨after, bindings, renewed⟩ := Frame.TypeRenewRel.of_modelled_match Frame.empty policyMatch model
  refine ⟨after, bindings, renewed, ?_⟩
  rw [bindings]
  simp [Bindings.classValues, Bindings.empty, Bindings.assign, Bindings.lookup, Bindings.isBound,
    Bindings.eqClassOrdered, Bindings.eqVarsInOrder]

theorem signature_variant (names : List String) (name : String) (fresh : name ∉ names) :
    Exact.TypeCandidateAlphaVariantRel names (signature "t").functionType (signature name).functionType := by
  refine ⟨Equiv.swap "t" name, (Equiv.swap "t" name).injective, ?_, ?_⟩
  · simp [signature, CompletedDelivery.arrowType]
  · intro key present
    have same : key = "t" := by
      simpa [signature, CompletedDelivery.arrowType, TypeSubst.typeVars, TypeSubst.typeVarsList] using present
    simpa [same] using fresh

theorem signature_lookup (space : Space) (names : List String) (before : Frame)
    (expected : Atom) (name : String)
    (declared : getAtomTypes space (.symbol "OtherDemandPair") = [(signature "t").functionType])
    (fresh : name ∉ invocationTypeScope names [] (.symbol "OtherDemandPair") expected before.bindings) :
    scopedLookup names space before.bindings (.symbol "OtherDemandPair") expected [(signature name).functionType] :=
  ⟨[(signature "t").functionType], by
      simpa only [declared] using FirstSuccessSourceReplies.source_types space (.symbol "OtherDemandPair"),
    .cons (signature_variant _ name fresh) (.nil _)⟩

def call : Atom := .expression [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.int 2)]

theorem selection (space : Space) (policy : Policy) (live : List Atom) (scope : List String)
    (name : String)
    (declared : getAtomTypes space (.symbol "OtherDemandPair") = [(signature "t").functionType])
    (fresh : name ∉ invocationTypeScope
      (invocationTypeScope scope live call (.symbol "DemandRange") Frame.empty.bindings)
      [] (.symbol "OtherDemandPair") (.symbol "DemandRange") Frame.empty.bindings) :
    ∃ after : Frame,
      InvocationSelectionRel space scopedLookup policy live scope call (.symbol "OtherDemandPair")
        (.symbol "DemandRange") Frame.empty (.selected (signature name) [after]) ∧
      after.bindings = Bindings.empty.assign name (.symbol "Number") ∧
      after.bindings.classValues name = [.symbol "Number"] := by
  let names := invocationTypeScope scope live call (.symbol "DemandRange") Frame.empty.bindings
  obtain ⟨after, bindings, firstRenew, classValues⟩ := first_number_frame policy name
  have first : ArgumentChecksRel space (scopedLookup names space) policy call (.grounded (.int 1))
      (.var name) 1 [Frame.empty] [after] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ArgumentChecksRel.cons (expression := call) (position := 1)
        (HEContextualArithmeticSource.scalar_lookup space names Frame.empty (.int 1) "Number" (.var name) rfl (by decide))
        (.cons (TypeCheckRel.accepted firstRenew) .nil) .nil)
  have second : ArgumentChecksRel space (scopedLookup names space) policy call (.grounded (.int 2))
      (.var name) 2 [after] [after] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ArgumentChecksRel.cons (expression := call) (position := 2)
        (HEContextualArithmeticSource.scalar_lookup space names after (.int 2) "Number" (.var name) rfl (by decide))
        (.cons (TypeCheckRel.accepted (HEAssignedRangeReturn.number_class_renewal policy after name classValues)) .nil) .nil)
  have rangeMatch : TypeMatchRel (.symbol "DemandRange") (.symbol "DemandRange") after.bindings after.bindings :=
    .structural (by decide) (by decide) (by decide) (by decide)
      (.symSym "DemandRange" semanticLoopFree_empty) (.mk (by simp [constraints, Bindings.empty]) .nil)
  have checked : ApplicationChecksRel space (scopedLookup names space) policy call (.symbol "DemandRange")
      (signature name) Frame.empty [after] [] := by
    simpa [signature, call, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := call) (expected := .symbol "DemandRange")
        (selected := signature name) (before := Frame.empty) (operator := .symbol "OtherDemandPair")
        (arguments := [.grounded (.int 1), .grounded (.int 2)]) rfl
        (.cons first (.cons second .nil))
        (.cons (TypeCheckRel.accepted (.unchanged (after.preserved_type_match policy rangeMatch))) .nil))
  exact ⟨after, ⟨[(signature name).functionType], signature_lookup space names Frame.empty _ name declared fresh,
    .selected checked (by simp)⟩, bindings, classValues⟩

def castScope (scope : List String) (live : List Atom) (before : Frame) (left : String) : List String :=
  invocationTypeScope
    (invocationTypeScope scope live (.symbol "OtherDemandPair") (signature left).functionType before.bindings)
    [] (.symbol "OtherDemandPair") (signature left).functionType before.bindings

theorem operator_source {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (left right : String)
    (declared : getAtomTypes (environment.view world label) (.symbol "OtherDemandPair") = [(signature "t").functionType])
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some (.symbol "Number"))
    (fresh : right ∉ castScope scope live before left) :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope (.symbol "OtherDemandPair") (signature left).functionType before
        [(.symbol "OtherDemandPair", after)] world (policy := policy) ∧
      after.bindings = before.bindings.addEquality left right ∧
      after.bindings.classValues left = [.symbol "Number"] ∧
      after.bindings.classValues right = [.symbol "Number"] := by
  have bindingFresh : right ∉ specBindingVars before.bindings := by
    intro present
    exact fresh (by simp [castScope, invocationTypeScope, present])
  have queried : environment.lookup
      (invocationTypeScope scope live (.symbol "OtherDemandPair") (signature left).functionType before.bindings)
      (environment.view world label) before.bindings (.symbol "OtherDemandPair") (signature left).functionType
      [(signature right).functionType] := by
    rw [lookup]
    exact signature_lookup _ _ before _ right declared fresh
  have matched := arrow_source_match before left right isolated assigned bindingFresh
  have model := HEFreshRangeAlias.alias_model before left right bindingFresh
  have policyMatch : policy.matching.Rel (signature left).functionType (signature right).functionType before.bindings
      (before.bindings.addEquality left right) := by
    cases policy.matching with
    | raw => exact matched
    | finite => exact ⟨matched, model⟩
  obtain ⟨after, bindings, renewed⟩ := Frame.CastRenewRel.of_modelled_source_match
    (policy := policy) before (earlier := []) (later := []) queried rfl (by simp) policyMatch model
  have afterMatch : policy.matching.Rel (signature left).functionType (signature right).functionType before.bindings
      after.bindings := by rw [bindings]; exact policyMatch
  have readSymbol : before.read policy (.symbol "OtherDemandPair") = .symbol "OtherDemandPair" := by
    simp [Frame.read, Entry.Value.substitute]
  have evaluated : Stateful.AtomRel environment label world live scope (.symbol "OtherDemandPair")
      (signature left).functionType before [(.symbol "OtherDemandPair", after)] world (policy := policy) := by
    apply Stateful.AtomRel.cast (raw := [(.symbol "OtherDemandPair", after.bindings)])
    · rw [readSymbol]
      apply Entry.Rel.cast (metaType := Atom.symbolType)
      · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · simpa only [Entry.Value.erase] using MetaTypeRel.symbol "OtherDemandPair"
      · simp [signature, CompletedDelivery.arrowType, Atom.atomType, Atom.symbolType, Atom.variableType]
      · exact Or.inl ⟨"OtherDemandPair", by simp [Entry.Value.erase]⟩
      · simp [Entry.Value.erase, Atom.unit]
    · rw [readSymbol]
      simp only [Entry.Value.erase]
      exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) afterMatch
    · rw [readSymbol]
      exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase],
        by simpa only [Entry.Value.erase] using renewed, by simp [Entry.Value.erase]⟩ .nil
  have classes := HEAssignedRangeReturn.alias_both_classes before.bindings left right (.symbol "Number")
    isolated assigned bindingFresh
  exact ⟨after, evaluated, bindings, by rw [bindings]; exact classes.1,
    by rw [bindings]; exact classes.2⟩

theorem arguments_source {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (frame : Frame) (name : String)
    (classValues : frame.bindings.classValues name = [.symbol "Number"]) :
    Stateful.ArgumentsRel environment label world live scope
      [(.grounded (.int 1), .var name), (.grounded (.int 2), .var name)] frame
      [(Entry.Value.argumentPacket [.grounded (.int 1), .grounded (.int 2)], frame)] world (policy := policy) := by
  have all : ∀ (values : List Int) (retained : List Atom),
      Stateful.ArgumentsRel environment label world retained scope
        (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name)) frame
        [(Entry.Value.argumentPacket (values.map fun value => Entry.Value.grounded (.int value)), frame)] world
        (policy := policy) := by
    intro values
    induction values with
    | nil => intro retained; exact .nil
    | cons value values ih =>
        intro retained
        have child := HEAssignedRangeReturn.number_at_range environment lookup policy label world
          (argumentScope (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name)) ++ retained)
          scope frame name value classValues
        have rest : Stateful.ArgumentBranchesRel environment label world retained scope
            (.grounded (.int value)) (values.map fun value => (Entry.Value.grounded (.int value), Atom.var name))
            [] [] world (policy := policy) := .nil
        have branches := Stateful.ArgumentBranchesRel.continuing
          (head := (Entry.Value.grounded (.int value), frame)) (by simp [ArgumentStopped])
          (ih ((Entry.Value.grounded (.int value)).erase :: retained)) rest
        apply Stateful.ArgumentsRel.cons child
        simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using branches
  exact all [1, 2] live

def contextualCall : Entry.Value :=
  .expression .active [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.int 2)]

/-- The concrete shared-formal constructor is earned from actual selection,
fresh operator recasting, both Number deliveries, and its absent equation
frontier. Whole-expression annotations play no role in that applicability. -/
theorem constructor_source {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (historical : environment.arguments = .historical)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (declared : getAtomTypes (environment.view world label) (.symbol "OtherDemandPair") = [(signature "t").functionType])
    (ordinary : NonGroundedCallRel environment.dispatch call)
    (absent : HEConstructorAdmission.headAbsent (environment.view world label) "OtherDemandPair" = true) :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope contextualCall (.symbol "DemandRange") Frame.empty
        [HESelectedConstructorSource.published policy call "OtherDemandPair"
          [.grounded (.int 1), .grounded (.int 2)] after] world (policy := policy) := by
  let avoid := invocationTypeScope
    (invocationTypeScope scope live call (.symbol "DemandRange") Frame.empty.bindings)
    [] (.symbol "OtherDemandPair") (.symbol "DemandRange") Frame.empty.bindings
  let name := instanceName avoid ["t"] 0 "t"
  have fresh : name ∉ avoid := instanceName_not_mem avoid ["t"] 0 "t"
  obtain ⟨selected, selectedRun, bindings, _⟩ :=
    selection (environment.view world label) policy live scope name declared fresh
  have isolated : name ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    simp [Bindings.assign, Bindings.empty, Bindings.eqVarsInOrder]
  have assigned : selected.bindings.lookup name = some (.symbol "Number") := by
    rw [bindings]
    simp [Bindings.assign, Bindings.empty, Bindings.lookup, Bindings.isBound]
  let headLive := (signature name).functionType ::
    [.grounded (.int 1), .grounded (.int 2)] ++ invocationReturnType (signature name) :: live
  let headScope := scope ++ expectedApplicationScope call (.symbol "DemandRange")
  let moreAvoid := castScope headScope headLive selected name
  let other := instanceName moreAvoid ["t"] 0 "t"
  have otherFresh : other ∉ moreAvoid := instanceName_not_mem moreAvoid ["t"] 0 "t"
  obtain ⟨after, operatorRun, _, classes, _⟩ := operator_source environment lookup policy label world
    headLive headScope selected name other declared isolated assigned otherFresh
  have delivered := arguments_source environment lookup policy label world
    (.symbol "OtherDemandPair" :: invocationReturnType (signature name) :: live) scope after name classes
  refine ⟨after, ?_⟩
  have erased : (Frame.empty.read policy contextualCall).erase = call := by
    simp [Frame.read_empty, contextualCall, call, Entry.Value.erase]
  rw [← erased]
  apply HESelectedConstructorSource.source_from_parts environment policy label world world world live scope
    contextualCall (.symbol "DemandRange") Frame.empty selected after after .active
    (.symbol "OtherDemandPair") "OtherDemandPair"
    [.grounded (.int 1), .grounded (.int 2)] [.grounded (.int 1), .grounded (.int 2)] (signature name)
  · simp only [Frame.read_empty, contextualCall, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
    exact Entry.Rel.expression
      (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by simp [Atom.atomType, Atom.expressionType, Atom.variableType])
      (Or.inr rfl)
  · rw [Frame.read_empty]; rfl
  · simpa only [historical, ArgumentService.selection, lookup, Frame.read_empty, contextualCall,
      Entry.Value.erase, List.map_cons, List.map_nil, call] using selectedRun
  · rfl
  · simpa only [headLive, headScope, contextualCall, call, Entry.Value.erase, List.map_cons, List.map_nil] using operatorRun
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact delivered
  · decide
  · simpa [HESelectedConstructorSource.assembled, Entry.Value.erase, call] using ordinary
  · exact absent

/-- Constructor completion earns its held publication in the ready profile;
this is not inferred merely from the type attached to the final expression. -/
theorem constructor_ready {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (historical : environment.arguments = .historical)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (declared : getAtomTypes (environment.view world label) (.symbol "OtherDemandPair") = [(signature "t").functionType])
    (ordinary : NonGroundedCallRel environment.dispatch call)
    (absent : HEConstructorAdmission.headAbsent (environment.view world label) "OtherDemandPair" = true) :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope contextualCall (.symbol "DemandRange") Frame.empty
        [(.expression .held [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.int 2)], after)] world
        (policy := Policy.ready) := by
  obtain ⟨after, produced⟩ := constructor_source environment lookup historical Policy.ready label world live scope
    declared ordinary absent
  have publication := HESelectedConstructorSource.published_successes Policy.ready rfl call "OtherDemandPair"
    [.grounded (.int 1), .grounded (.int 2)] after (by decide)
  have pair : HESelectedConstructorSource.published Policy.ready call "OtherDemandPair"
      [.grounded (.int 1), .grounded (.int 2)] after =
      (.expression .held [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.int 2)], after) := by
    apply Prod.ext
    · simpa [Frame.read, Entry.Value.substitute] using publication
    · rfl
  exact ⟨after, by simpa only [pair] using produced⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERepeatedFormalSource
