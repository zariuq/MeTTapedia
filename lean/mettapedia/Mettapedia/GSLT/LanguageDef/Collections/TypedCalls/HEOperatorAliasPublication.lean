import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPrivateTypePublication
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERepeatedFormalSource

/-!
# Exact annotated operator-alias frames

The actual arrow shapes `T -> T` and `T,T -> R` both compare the same
private names twice. Raw matching records both occurrences; the source
merge consumes their deduplicated constraint packet. Contextual matching
instead binds the fresh operator name once and reads that value at the
second occurrence. The resulting annotated table is derived independently
and then certified against the source equality record.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOperatorAliasPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Type.Presentation.BindingTheory Spec.Bindings.ScopeObservation Spec.Match.Merge
open Spec.Match.SolutionTheory
open Spec.Eval.Steps
open HEFreshSyntaxBinding

def arrow (front suffix : List String) (name : String) : Atom :=
  .expression (front.map Atom.symbol ++ .var name :: .var name :: suffix.map Atom.symbol)

theorem symbol_match_tail (symbols : List String) (seed : Bindings) :
    MatchListAccRel equalityGroundedSemantic (symbols.map Atom.symbol) (symbols.map Atom.symbol) seed seed := by
  induction symbols with
  | nil => exact .nil
  | cons symbol symbols ih =>
      exact .cons (.symSym symbol semanticLoopFree_empty)
        (.mk (by simp [constraints, Bindings.empty]) .nil) ih

theorem symbol_match_prefix (symbols : List String) (left right : List Atom) (seed output : Bindings)
    (tail : MatchListAccRel equalityGroundedSemantic left right seed output) :
    MatchListAccRel equalityGroundedSemantic (symbols.map Atom.symbol ++ left)
      (symbols.map Atom.symbol ++ right) seed output := by
  induction symbols with
  | nil => exact tail
  | cons symbol symbols ih =>
      exact .cons (.symSym symbol semanticLoopFree_empty)
        (.mk (by simp [constraints, Bindings.empty]) .nil) ih

theorem arrow_match (front suffix : List String) (left right : String) :
    MatchRel equalityGroundedSemantic (arrow front suffix left) (arrow front suffix right)
      (HERepeatedFormalSource.twiceAliases left right) := by
  apply MatchRel.expression
  · apply symbol_match_prefix
    exact .cons (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
      (HEFreshRangeAlias.empty_alias_merge left right)
      (.cons (.varVar left right (semanticLoopFree_of_assignments_nil rfl))
        (HERepeatedFormalSource.repeat_empty_alias left right) (symbol_match_tail suffix _))
  · exact semanticLoopFree_of_assignments_nil rfl

theorem arrow_source_match (front suffix : List String) (before : Frame)
    (left right : String) (value : Atom)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some value)
    (fresh : right ∉ specBindingVars before.bindings) :
    TypeMatchRel (arrow front suffix left) (arrow front suffix right)
      before.bindings (before.bindings.addEquality left right) := by
  apply TypeMatchRel.structural
    (by simp [arrow, Atom.undefinedType]) (by simp [arrow, Atom.atomType])
    (by simp [arrow, Atom.undefinedType]) (by simp [arrow, Atom.atomType])
    (arrow_match front suffix left right)
  apply (mergeRel_iff_of_constraints_perm
    (p := equalityGroundedSemantic) (left := before.bindings)
    (show (constraints (HERepeatedFormalSource.twiceAliases left right)).Perm
      (constraints (HERepeatedFormalSource.aliases left right)) by
      rw [HERepeatedFormalSource.repeated_constraint_packet])).mpr
  exact HEFreshRangeAlias.alias_merge before.bindings left right value isolated assigned fresh

theorem symbol_unify_tail (policy : Policy) (symbols : List String) (environment : Entry.Value.Environment) :
    Entry.Value.UnifyListRel policy.rebuilding environment
      (symbols.map Entry.Value.symbol) (symbols.map Entry.Value.symbol) environment := by
  induction symbols with
  | nil => exact .nil _
  | cons symbol symbols ih =>
      exact .cons (.ordinary (.identical (by simp [Entry.Value.substitute]))) ih

theorem symbol_unify_prefix (policy : Policy) (symbols : List String)
    (left right : List Entry.Value) (before after : Entry.Value.Environment)
    (tail : Entry.Value.UnifyListRel policy.rebuilding before left right after) :
    Entry.Value.UnifyListRel policy.rebuilding before
      (symbols.map Entry.Value.symbol ++ left) (symbols.map Entry.Value.symbol ++ right) after := by
  induction symbols with
  | nil => exact tail
  | cons symbol symbols ih =>
      exact .cons (.ordinary (.identical (by simp [Entry.Value.substitute]))) ih

theorem materialized_arrow (policy : Policy) (before : Frame) (front suffix : List String)
    (name : String) :
    Entry.Value.substitute policy.rebuilding (Entry.Value.resolve before.environment)
      (Entry.Value.ofAtom (arrow front suffix name)) =
      .expression .active (front.map Entry.Value.symbol ++ before.read policy (.var name) ::
        before.read policy (.var name) :: suffix.map Entry.Value.symbol) := by
  simp [arrow, Entry.Value.ofAtom, Entry.Value.substitute, List.map_append, List.map_map,
    Function.comp_def, Frame.read, HEFreshEquationFrames.Range.active_rebuild]

/-- This is the actual annotated whole-arrow comparison, including its
second occurrence. The output table is earned by the existing binder. -/
theorem arrow_contextual_match (policy : Policy) (before : Frame) (front suffix : List String)
    (left right : String) (value : Entry.Value)
    (closed : TypeSubst.typeVars value.erase = [])
    (read : before.read policy (.var left) = value)
    (fresh : right ∉ specBindingVars before.bindings) :
    Entry.Value.UnifyRel policy.rebuilding before.environment
      (Entry.Value.ofAtom (arrow front suffix left)) (Entry.Value.ofAtom (arrow front suffix right))
      (bindFrame policy before right value fresh (by simp [closed])).environment := by
  let after := bindFrame policy before right value fresh (by simp [closed])
  have first := source_binding policy before right value fresh closed
  have second : Entry.Value.UnifyRel policy.rebuilding after.environment value (.var right) after.environment := by
    apply Entry.Value.UnifyRel.ordinary
    rw [ground_substitution policy.rebuilding _ value closed]
    have resolved : Entry.Value.resolve after.environment right = value := by
      simpa only [Frame.read, Entry.Value.substitute] using bound_read policy before right value fresh closed policy
    simpa only [Entry.Value.substitute, resolved] using
      (Entry.Value.AppliedUnifyRel.identical (policy := policy.rebuilding) (environment := after.environment)
        (left := value) (right := value) rfl)
  apply Entry.Value.UnifyRel.ordinary
  rw [materialized_arrow, materialized_arrow, read]
  have rightRead : before.read policy (.var right) = .var right := by
    simpa only [Frame.read, Entry.Value.substitute] using resolve_fresh before right fresh
  rw [rightRead]
  exact .expression (symbol_unify_prefix policy front _ _ _ _
    (.cons first (.cons second (symbol_unify_tail policy suffix after.environment))))

/-- Raw equality authority and the annotated table come from separate
source and contextual derivations. No desired output frame is assumed. -/
theorem alias_frame (policy : Policy) (before : Frame) (front suffix : List String)
    (left right : String) (value : Entry.Value)
    (closed : TypeSubst.typeVars value.erase = [])
    (read : before.read policy (.var left) = value)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some value.erase)
    (fresh : right ∉ specBindingVars before.bindings) :
    ∃ after : Frame,
      after.bindings = before.bindings.addEquality left right ∧
      after.environment = (right, value) :: before.environment ∧
      policy.matching.Rel (arrow front suffix left) (arrow front suffix right)
        before.bindings after.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment
        (Entry.Value.ofAtom (arrow front suffix left)) (Entry.Value.ofAtom (arrow front suffix right))
        after.environment := by
  have source := arrow_source_match front suffix before left right value.erase isolated assigned fresh
  have model := HEFreshRangeAlias.alias_model before left right fresh
  have policyMatch : policy.matching.Rel (arrow front suffix left) (arrow front suffix right)
      before.bindings (before.bindings.addEquality left right) := by
    cases policy.matching with
    | raw => exact source
    | finite => exact ⟨source, model⟩
  have merged : MergeRel equalityGroundedSemantic before.bindings
      (HERepeatedFormalSource.twiceAliases left right) (before.bindings.addEquality left right) := by
    apply (mergeRel_iff_of_constraints_perm
      (p := equalityGroundedSemantic) (left := before.bindings)
      (show (constraints (HERepeatedFormalSource.twiceAliases left right)).Perm
        (constraints (HERepeatedFormalSource.aliases left right)) by
        rw [HERepeatedFormalSource.repeated_constraint_packet])).mpr
    exact HEFreshRangeAlias.alias_merge before.bindings left right value.erase isolated assigned fresh
  have candidate : UnifyCandidateRel (Entry.Value.ofAtom (arrow front suffix left)).erase
      (Entry.Value.ofAtom (arrow front suffix right)).erase before.bindings (before.bindings.addEquality left right) := by
    simpa only [Entry.Value.erase_ofAtom] using
      (show UnifyCandidateRel (arrow front suffix left) (arrow front suffix right)
        before.bindings (before.bindings.addEquality left right) from
        ⟨_, arrow_match front suffix left right, LogicalMergeRel.comm (merged.logicalMerge model)⟩)
  have contextual := arrow_contextual_match policy before front suffix left right value closed read fresh
  let after : Frame := ⟨before.bindings.addEquality left right,
    (bindFrame policy before right value fresh (by simp [closed])).environment,
    contextual.certifies before.certified candidate⟩
  exact ⟨after, rfl, HEPrivateTypePublication.fresh_environment policy before right value fresh closed,
    policyMatch, contextual⟩

/-- The local cast uses its actual selected query reply, not a new typing
oracle. The two named rows are exposed for subsequent scoped publication. -/
theorem cast_from_query (policy : Policy) (lookup : TypeLookupRel) (before : Frame)
    (subject : Atom) (front suffix : List String) (left right : String) (value : Entry.Value)
    (closed : TypeSubst.typeVars value.erase = [])
    (read : before.read policy (.var left) = value)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some value.erase)
    (fresh : right ∉ specBindingVars before.bindings)
    (queried : lookup before.bindings subject (arrow front suffix left) [arrow front suffix right]) :
    ∃ after : Frame,
      Frame.CastRenewRel policy lookup subject (arrow front suffix left) before after ∧
      after.bindings = before.bindings.addEquality left right ∧
      after.environment = (right, value) :: before.environment := by
  obtain ⟨after, bindings, environment, matched, contextual⟩ :=
    alias_frame policy before front suffix left right value closed read isolated assigned fresh
  exact ⟨after, .matched (earlier := []) (later := []) queried rfl (by simp) matched contextual,
    bindings, environment⟩

theorem signature_variant (front suffix : List String) (names : List String)
    (original chosen : String) (fresh : chosen ∉ names) :
    Exact.TypeCandidateAlphaVariantRel names (arrow front suffix original) (arrow front suffix chosen) := by
  refine ⟨Equiv.swap original chosen, (Equiv.swap original chosen).injective, ?_, ?_⟩
  · simp [arrow, List.map_map, Function.comp_def]
  · intro name member
    have symbols (values : List String) : TypeSubst.typeVarsList (values.map Atom.symbol) = [] := by
      induction values with
      | nil => rfl
      | cons value values ih => simpa [TypeSubst.typeVarsList, TypeSubst.typeVars] using ih
    have same : name = original := by
      simpa [arrow, TypeSubst.typeVars, TypeSubst.typeVarsList_append,
        TypeSubst.typeVarsList, symbols] using member
    simpa [same] using fresh

/-- A physical symbol declaration earns the fresh operator-arrow query.
Both occurrences use one newly allocated name. -/
theorem scoped_query (space : Space) (before : Frame) (names : List String)
    (head original chosen : String) (front suffix : List String) (expected : Atom)
    (declared : getAtomTypes space (.symbol head) = [arrow front suffix original])
    (fresh : chosen ∉ invocationTypeScope names [] (.symbol head) expected before.bindings) :
    scopedLookup names space before.bindings (.symbol head) expected [arrow front suffix chosen] :=
  ⟨[arrow front suffix original], by
      simpa only [declared] using FirstSuccessSourceReplies.source_types space (.symbol head),
    .cons (signature_variant front suffix _ original chosen fresh) (.nil _)⟩

theorem source_operator {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (head left right : String) (front suffix : List String) (value : Entry.Value)
    (notEmpty : head ≠ "Empty")
    (closed : TypeSubst.typeVars value.erase = [])
    (read : before.read policy (.var left) = value)
    (isolated : left ∉ before.bindings.eqVarsInOrder)
    (assigned : before.bindings.lookup left = some value.erase)
    (fresh : right ∉ specBindingVars before.bindings)
    (queried : environment.lookup
      (invocationTypeScope scope live (.symbol head) (arrow front suffix left) before.bindings)
      (environment.view world label) before.bindings (.symbol head) (arrow front suffix left)
      [arrow front suffix right]) :
    ∃ after : Frame,
      Stateful.AtomRel environment label world live scope (.symbol head) (arrow front suffix left) before
        [(.symbol head, after)] world (policy := policy) ∧
      after.bindings = before.bindings.addEquality left right ∧
      after.environment = (right, value) :: before.environment := by
  obtain ⟨after, bindings, annotated, matched, contextual⟩ :=
    alias_frame policy before front suffix left right value closed read isolated assigned fresh
  have renewed : Frame.CastRenewRel policy
      (environment.lookup
        (invocationTypeScope scope live (.symbol head) (arrow front suffix left) before.bindings)
        (environment.view world label)) (.symbol head) (arrow front suffix left) before after :=
    .matched (earlier := []) (later := []) queried rfl (by simp) matched contextual
  have readSymbol : before.read policy (.symbol head) = .symbol head := by
    simp [Frame.read, Entry.Value.substitute]
  refine ⟨after, ?_, bindings, annotated⟩
  apply Stateful.AtomRel.cast (raw := [(.symbol head, after.bindings)])
  · rw [readSymbol]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol head
    · simp [arrow, Atom.atomType, Atom.symbolType, Atom.variableType]
    · exact Or.inl ⟨head, by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [readSymbol]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp) matched
  · rw [readSymbol]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase],
      by simpa only [Entry.Value.erase] using renewed, by simp [Entry.Value.erase]⟩ .nil

/-- The fresh first type assignment and subsequent operator alias have
exact ordered annotated rows, even over a caller with existing aliases.
The raw equality record is independently earned by the whole-arrow match. -/
theorem fresh_packet (policy : Policy) (caller : Frame) (front suffix : List String)
    (left right : String) (value : Atom) (closed : TypeSubst.typeVars value = [])
    (notUndefined : value ≠ Atom.undefinedType) (notAtom : value ≠ Atom.atomType)
    (leftFresh : left ∉ specBindingVars caller.bindings)
    (rightFresh : right ∉ specBindingVars caller.bindings) (different : right ≠ left) :
    ∃ selected after : Frame,
      Frame.TypeRenewRel policy value (.var left) caller selected ∧
      selected.bindings = HEFreshRangeFrame.extend caller.bindings left value ∧
      selected.environment = (left, Entry.Value.ofAtom value) :: caller.environment ∧
      after.bindings = (HEFreshRangeFrame.extend caller.bindings left value).addEquality left right ∧
      after.environment = (right, Entry.Value.ofAtom value) :: (left, Entry.Value.ofAtom value) :: caller.environment ∧
      policy.matching.Rel (arrow front suffix left) (arrow front suffix right)
        selected.bindings after.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding selected.environment
        (Entry.Value.ofAtom (arrow front suffix left)) (Entry.Value.ofAtom (arrow front suffix right))
        after.environment := by
  obtain ⟨selected, renewed, bindings, annotated, _, _, _⟩ :=
    HEPrivateTypePublication.fresh_closed_type_publication policy caller left value closed notUndefined notAtom leftFresh
  have closedValue : TypeSubst.typeVars (Entry.Value.ofAtom value).erase = [] := by simpa using closed
  have read : selected.read policy (.var left) = Entry.Value.ofAtom value := by
    simp [Frame.read, Entry.Value.substitute, annotated, Entry.Value.resolve]
  have isolated : left ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).2
  have assigned : selected.bindings.lookup left = some (Entry.Value.ofAtom value).erase := by
    rw [bindings, Entry.Value.erase_ofAtom]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).1
  have fresh : right ∉ specBindingVars selected.bindings := by
    rw [bindings]
    simpa [HEFreshRangeFrame.extend, specBindingVars, closed, and_assoc, and_left_comm, and_comm]
      using And.intro rightFresh different
  obtain ⟨after, afterBindings, afterAnnotated, matched, contextual⟩ :=
    alias_frame policy selected front suffix left right (Entry.Value.ofAtom value)
      closedValue read isolated assigned fresh
  refine ⟨selected, after, renewed, bindings, annotated, ?_, ?_, matched, contextual⟩
  · exact afterBindings.trans (congrArg (fun b => b.addEquality left right) bindings)
  · rw [afterAnnotated, annotated]

/-- Complete local source join: earn the first type frame, allocate the
second name outside the actual operator query scope, query the physical
declaration and execute the source operator cast with its exact table. -/
theorem fresh_scoped_operator {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (caller : Frame) (head original left : String) (front suffix : List String)
    (value : Atom) (closed : TypeSubst.typeVars value = [])
    (notUndefined : value ≠ Atom.undefinedType) (notAtom : value ≠ Atom.atomType)
    (notEmpty : head ≠ "Empty") (leftFresh : left ∉ specBindingVars caller.bindings)
    (declared : getAtomTypes (environment.view world label) (.symbol head) = [arrow front suffix original]) :
    ∃ (right : String) (selected after : Frame),
      Frame.TypeRenewRel policy value (.var left) caller selected ∧
      selected.bindings = HEFreshRangeFrame.extend caller.bindings left value ∧
      Stateful.AtomRel environment label world live scope (.symbol head) (arrow front suffix left) selected
        [(.symbol head, after)] world (policy := policy) ∧
      after.bindings = (HEFreshRangeFrame.extend caller.bindings left value).addEquality left right ∧
      after.environment = (right, Entry.Value.ofAtom value) :: (left, Entry.Value.ofAtom value) :: caller.environment ∧
      right ∉ invocationTypeScope
        (invocationTypeScope scope live (.symbol head) (arrow front suffix left) selected.bindings)
        [] (.symbol head) (arrow front suffix left) selected.bindings := by
  obtain ⟨selected, renewed, bindings, annotated, _, _, _⟩ :=
    HEPrivateTypePublication.fresh_closed_type_publication policy caller left value closed notUndefined notAtom leftFresh
  let names := invocationTypeScope scope live (.symbol head) (arrow front suffix left) selected.bindings
  let avoid := invocationTypeScope names [] (.symbol head) (arrow front suffix left) selected.bindings
  let right := instanceName avoid [original] 0 original
  have fresh : right ∉ avoid := instanceName_not_mem avoid [original] 0 original
  have bindingFresh : right ∉ specBindingVars selected.bindings := by
    intro present
    exact fresh (by simp [avoid, invocationTypeScope, present])
  have queried : environment.lookup names (environment.view world label) selected.bindings
      (.symbol head) (arrow front suffix left) [arrow front suffix right] := by
    rw [lookup]
    exact scoped_query _ selected names head original right front suffix _ declared fresh
  have read : selected.read policy (.var left) = Entry.Value.ofAtom value := by
    simp [Frame.read, Entry.Value.substitute, annotated, Entry.Value.resolve]
  have isolated : left ∉ selected.bindings.eqVarsInOrder := by
    rw [bindings]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).2
  have assigned : selected.bindings.lookup left = some (Entry.Value.ofAtom value).erase := by
    rw [bindings, Entry.Value.erase_ofAtom]
    exact (HEFreshRangeAlias.extended_private_facts caller.bindings left value leftFresh).1
  obtain ⟨after, run, finalBindings, finalEnvironment⟩ := source_operator environment policy label world live scope
    selected head left right front suffix (Entry.Value.ofAtom value) notEmpty (by simpa using closed)
    read isolated assigned bindingFresh queried
  refine ⟨right, selected, after, renewed, bindings, run, ?_, ?_, fresh⟩
  · exact finalBindings.trans (congrArg (fun b => b.addEquality left right) bindings)
  · rw [finalEnvironment, annotated]

namespace Controls

/-- Repeated source occurrences are not silently discarded before merge. -/
theorem two_occurrences_one_merged_constraint :
    (HERepeatedFormalSource.twiceAliases "t" "u").equalities = [("t", "u"), ("t", "u")] ∧
    constraints (HERepeatedFormalSource.twiceAliases "t" "u") = [.equality "t" "u"] := by decide +kernel

def conflicting : Bindings :=
  (Bindings.empty.assign "t" (.symbol "Number")).assign "u" (.symbol "String")

/-- A nonfresh second type name with a conflicting instance is rejected;
an equality edge cannot override its earlier type obligation. -/
theorem conflicting_operator_instance_rejected :
    matchTypes (arrow ["->"] [] "t") (arrow ["->"] [] "u") conflicting 48 = [] := by decide +kernel

theorem exact_expression_packet (policy : Policy) (caller : Frame) (suffix : List String)
    (left right : String) (leftFresh : left ∉ specBindingVars caller.bindings)
    (rightFresh : right ∉ specBindingVars caller.bindings) (different : right ≠ left) :
    ∃ selected after : Frame,
      Frame.TypeRenewRel policy Atom.expressionType (.var left) caller selected ∧
      after.bindings = (HEFreshRangeFrame.extend caller.bindings left Atom.expressionType).addEquality left right ∧
      after.environment = (right, .symbol "Expression") :: (left, .symbol "Expression") :: caller.environment ∧
      Entry.Value.UnifyRel policy.rebuilding selected.environment
        (Entry.Value.ofAtom (arrow ["->"] suffix left))
        (Entry.Value.ofAtom (arrow ["->"] suffix right)) after.environment := by
  obtain ⟨selected, after, renewed, _, _, bindings, annotated, _, contextual⟩ :=
    fresh_packet policy caller ["->"] suffix left right Atom.expressionType rfl (by decide) (by decide)
      leftFresh rightFresh different
  exact ⟨selected, after, renewed, bindings,
    by simpa only [Atom.expressionType, Entry.Value.ofAtom] using annotated, contextual⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOperatorAliasPublication
