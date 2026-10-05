import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlReturn
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-!
# Executing a selected branch of minimal MeTTa

These laws expose matching and binding extension before resuming a function.
They preserve the enclosing stack, queued work and previous answers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution

open Metta Metta.Minimal
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening

private theorem renameAllVars_eq_renBy (rename : VarName → VarName) (atom : Atom) :
    renameAllVars rename atom = renBy rename atom := by
  induction atom with
  | sym | var | gnd => simp only [renameAllVars, renBy]
  | expr items ih =>
    simp only [renameAllVars, renBy, Atom.expr.injEq]
    exact List.map_congr_left (fun item member => ih item member)

/-- Both branches of the actual capture-avoiding freshener use one injective
renaming on the complete rule. The collision fallback obeys the same contract
as ordinary counter suffixes. -/
theorem freshenRuleAvoiding_renaming (counter : Nat) (avoid : List VarName) (lhs rhs : Atom) :
    ∃ rename : VarName → VarName, Function.Injective rename ∧
      (freshenRuleAvoiding counter avoid lhs rhs).1 =
        (renBy rename lhs, renBy rename rhs) := by
  by_cases collision : ∃ name ∈ (freshenRule counter lhs rhs).1.vars ++
      (freshenRule counter lhs rhs).2.vars, name ∈ avoid
  · refine ⟨captureAvoidingName avoid counter, captureAvoidingName_injective avoid counter, ?_⟩
    simp only [freshenRuleAvoiding, if_pos collision, renameAllVars_eq_renBy]
  · refine ⟨counterSuffix counter, counterSuffix_injective counter, ?_⟩
    simpa only [freshenRuleAvoiding, if_neg collision] using freshenRule_eq_renBy counter lhs rhs

/-- The query freshener discharges the incoming-store part of materialization
for every variable of the whole rule, including variables used only in its
body. Existing closed bindings cannot capture a new local control binder. -/
theorem query_fresh_variables_unassigned (counter : Nat) (previous : Stack)
    (query lhs rhs : Atom) (incoming : Metta.Bindings)
    (stored : ClosedValueBindings incoming) :
    ∀ name ∈ (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.1.vars ++
        (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.2.vars,
      Bindings.lookupVal incoming name = none := by
  intro name occurrence
  apply stored.toValueBindings.lookup_none_of_not_key
  intro key
  apply freshenRuleAvoiding_vars_fresh counter (Metta.Minimal.queryOpAvoid previous query incoming)
    lhs rhs name occurrence
  exact List.mem_append_left _ (List.mem_append_left _ (bindingValueKey_mem_vars key))

/-- Code whose variables are unassigned is already materialized in a
closed-value store. -/
theorem instantiate_unassigned (bindings : Metta.Bindings)
    (stored : ClosedValueBindings bindings) (atom : Atom)
    (unassigned : ∀ name ∈ atom.vars, Bindings.lookupVal bindings name = none) :
    instantiate bindings atom = atom := by
  induction atom with
  | sym | gnd => simp only [instantiate, Bindings.resolveAtom]
  | var name =>
    simp only [instantiate, Bindings.resolveAtom, stored.resolve_eq_lookupVal,
      unassigned name (by simp [Atom.vars]), Option.getD_none]
  | expr items ih =>
    simp only [instantiate, Bindings.resolveAtom, Atom.expr.injEq]
    calc
      items.map (Bindings.resolveAtom bindings) = items.map id := by
        apply List.map_congr_left
        intro child member
        apply ih child member
        intro name occurrence
        apply unassigned name
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨child.vars, ⟨child, member, rfl⟩, occurrence⟩
      _ = items := List.map_id items

/-- Every variable still present after closed-value materialization is
unassigned. This turns the actual instantiated program text into its own
freshness evidence for subsequent pattern matching. -/
theorem fixed_closed_bindings_private (bindings : Metta.Bindings)
    (stored : ClosedValueBindings bindings) (atom : Atom)
    (fixed : instantiate bindings atom = atom) :
    ∀ name ∈ atom.vars, name ∉ bindings.vars := by
  induction atom with
  | sym | gnd => simp [Atom.vars]
  | var keyName =>
    intro name occurs mentioned
    have same : name = keyName := by simpa only [Atom.vars, List.mem_singleton] using occurs
    subst name
    obtain ⟨value, lookup⟩ := stored.toValueBindings.lookup_some_of_key_mem
      (stored.key_mem_of_vars_mem mentioned)
    have closed := stored.lookup_closed lookup
    have equal : value = .var keyName := by
      simpa only [instantiate, Bindings.resolveAtom,
        stored.resolve_eq_lookupVal, lookup, Option.getD_some] using fixed
    simp only [equal, Atom.vars, List.cons_ne_self] at closed
  | expr items ih =>
    have each : ∀ item ∈ items, instantiate bindings item = item := by
      have mapped : items.map (Bindings.resolveAtom bindings) = items.map id := by
        simpa only [instantiate, Bindings.resolveAtom, List.map_id, Atom.expr.injEq] using fixed
      exact (List.map_inj_left (g := id)).mp mapped
    intro name occurs
    simp only [Atom.vars] at occurs
    obtain ⟨names, member, mentioned⟩ := List.mem_flatten.mp occurs
    obtain ⟨item, itemMember, rfl⟩ := List.mem_map.mp member
    exact ih item itemMember (each item itemMember) name mentioned

/-- Materializing closed values removes variables and introduces none. -/
theorem instantiate_closed_vars_subset (bindings : Metta.Bindings)
    (stored : ClosedValueBindings bindings) (atom : Atom) :
    ∀ name ∈ (instantiate bindings atom).vars, name ∈ atom.vars := by
  induction atom with
  | sym | gnd => simp [instantiate, Bindings.resolveAtom, Atom.vars]
  | var key =>
    simp only [instantiate, Bindings.resolveAtom, stored.resolve_eq_lookupVal]
    cases found : Bindings.lookupVal bindings key with
    | none => simp
    | some value => simp [stored.lookup_closed found]
  | expr items ih =>
    intro name occurrence
    simp only [instantiate, Bindings.resolveAtom, Atom.vars, List.map_map,
      List.mem_flatten, List.mem_map] at occurrence
    obtain ⟨names, ⟨child, member, rfl⟩, occurs⟩ := occurrence
    simp only [Atom.vars, List.mem_flatten, List.mem_map]
    exact ⟨child.vars, ⟨child, member, rfl⟩, ih child member name occurs⟩

/-- A freshened rule stays disjoint from every live caller variable after
closed-value materialization, including collision-avoiding freshening. -/
theorem materialized_query_excludes_caller (counter : Nat) (previous : Stack)
    (query lhs rhs : Atom) (incoming output : Metta.Bindings)
    (stored : ClosedValueBindings output) (name : String)
    (live : name ∈ liveStackVars previous) :
    name ∉ (instantiate output
      (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming)
        lhs rhs).1.2).vars := by
  intro occurs
  have raw := instantiate_closed_vars_subset output stored _ name occurs
  have excluded := freshenRuleAvoiding_vars_fresh counter
    (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs name
    (List.mem_append_right _ raw)
  apply excluded
  simp only [Metta.Minimal.queryOpAvoid, List.mem_append]
  exact .inr live

/-- Substituting closed data into already materialized code preserves
materialization. The substitution cannot introduce a variable for the store
to resolve later. -/
theorem instantiate_substitute_fixed (bindings : Metta.Bindings)
    (name : String) (payload atom : Atom) (closed : payload.vars = [])
    (fixed : instantiate bindings atom = atom) :
    instantiate bindings (Subst.apply [(name, payload)] atom) =
      Subst.apply [(name, payload)] atom := by
  induction atom with
  | sym | gnd => simp only [Subst.apply, instantiate, Bindings.resolveAtom]
  | var other =>
    by_cases same : other = name
    · simpa [Subst.apply, Subst.lookup, same] using instantiate_of_closed bindings payload closed
    · simpa [Subst.apply, Subst.lookup, same] using fixed
  | expr items ih =>
    have each : ∀ item ∈ items, instantiate bindings item = item := by
      have mapped : items.map (Bindings.resolveAtom bindings) = items.map id := by
        simpa only [instantiate, Bindings.resolveAtom, List.map_id, Atom.expr.injEq] using fixed
      exact (List.map_inj_left (g := id)).mp mapped
    simp only [Subst.apply, instantiate, Bindings.resolveAtom, List.map_map, Atom.expr.injEq]
    exact List.map_congr_left (fun item member => ih item member (each item member))

private theorem flatMap_at_most_one {α β : Type} (items : List α) (f : α → List β)
    (one : items.length ≤ 1) (each : ∀ item ∈ items, (f item).length ≤ 1) :
    (items.flatMap f).length ≤ 1 := by
  cases items with
  | nil => simp
  | cons first rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using one)
    subst rest
    simpa using each first (by simp)

private theorem addEquality_at_most_one (bindings : Metta.Bindings) (left right : VarName) :
    (Bindings.addVarEquality bindings left right).length ≤ 1 := by
  unfold Bindings.addVarEquality
  split <;> dsimp only <;> split <;> simp

private theorem addValue_at_most_one (bindings : Metta.Bindings) (name : VarName)
    (atom : Atom) : (Bindings.addVarBinding bindings name atom).length ≤ 1 := by
  unfold Bindings.addVarBinding
  split
  · exact addEquality_at_most_one _ _ _
  · split
    · simp
    · split
      · simp
      · simp
      · split <;> simp

/-- The default runtime merger makes no nondeterministic choices, including
when it must reconcile aliases. A custom grounded matcher is a separate
interface and is not used by the generated computation dispatcher. -/
theorem merge_at_most_one (left right : Metta.Bindings) :
    (Bindings.merge left right).length ≤ 1 := by
  have fold (relations : Metta.Bindings) (acc : List Metta.Bindings)
      (one : acc.length ≤ 1) : (relations.foldl Bindings.mergeOne acc).length ≤ 1 := by
    induction relations generalizing acc with
    | nil => exact one
    | cons relation rest ih =>
      apply ih
      unfold Bindings.mergeOne
      apply flatMap_at_most_one _ _ one
      intro bindings _
      cases relation with
      | val name atom => exact addValue_at_most_one bindings name atom
      | eq first second => exact addEquality_at_most_one bindings first second
  exact fold right [left] (by simp)

mutual

private theorem matchRaw_at_most_one (left right : Atom) :
    (Metta.matchAtomsWith none left right).length ≤ 1 := by
  cases left <;> cases right <;> simp only [Metta.matchAtomsWith]
  case expr.expr xs ys => exact matchAll_at_most_one [[]] xs ys (by simp)
  all_goals split <;> simp
termination_by sizeOf left + sizeOf right

private theorem matchAll_at_most_one (acc : List Metta.Bindings) (left right : List Atom)
    (one : acc.length ≤ 1) : (Metta.matchAll none acc left right).length ≤ 1 := by
  cases left with
  | nil => cases right <;> simp_all [Metta.matchAll]
  | cons first rest =>
    cases right with
    | nil => simp [Metta.matchAll]
    | cons other tail =>
      rw [Metta.matchAll]
      apply matchAll_at_most_one
      apply flatMap_at_most_one _ _ one
      intro bindings _
      apply flatMap_at_most_one
      · exact (List.length_filter_le _ _).trans (matchRaw_at_most_one first other)
      · intro matched _
        exact merge_at_most_one bindings matched
termination_by sizeOf left + sizeOf right

end

/-- Default matching yields at most one candidate. The statement covers open
atoms as well as generated patterns, and does not identify an arbitrary
custom grounded matcher with the default matcher. -/
theorem match_at_most_one (left right : Atom) :
    (Metta.matchAtoms left right).length ≤ 1 :=
  (List.length_filter_le _ _).trans (matchRaw_at_most_one left right)

/-- The custom-matcher boundary is substantive: an arbitrary grounded
matcher can supply multiple candidates for the same ground inputs. -/
theorem custom_matcher_can_branch :
    (Metta.matchAtomsWith (some (fun _ _ => [[], []]))
      (.gnd (.int 0)) (.gnd (.int 0))).length = 2 := by
  simp [Metta.matchAtomsWith]

private theorem singleton_of_member {α : Type} (items : List α) (item : α)
    (one : items.length ≤ 1) (member : item ∈ items) : items = [item] := by
  cases items with
  | nil => simp at member
  | cons first rest =>
    have empty : rest = [] := List.eq_nil_of_length_eq_zero (by simpa using one)
    subst rest
    simpa using (List.mem_singleton.mp member).symm

/-- A compatible candidate is the entire successor list of default `unify`,
not merely one path among possible extra answers. This is the executable
uniqueness fact used to compose an ordered generated dispatcher. -/
theorem unify_candidate_exact (previous : Stack) (target pattern yes no : Atom)
    (incoming matched output : Metta.Bindings)
    (matching : matched ∈ Metta.matchAtoms target pattern)
    (merging : output ∈ Bindings.merge incoming matched)
    (acyclic : output.hasLoop = false) :
    unifyOp previous target pattern yes no incoming =
      [finItem previous (instantiate output yes) output] := by
  let candidates := (Metta.matchAtoms target pattern).flatMap fun found =>
    (Bindings.merge incoming found).filterMap fun bindings =>
      if bindings.hasLoop then none
      else some (finItem previous (instantiate bindings yes) bindings)
  have one : candidates.length ≤ 1 := by
    apply flatMap_at_most_one _ _ (match_at_most_one target pattern)
    intro found _
    exact (List.length_filterMap_le _ _).trans (merge_at_most_one incoming found)
  have member : finItem previous (instantiate output yes) output ∈ candidates := by
    apply List.mem_flatMap.mpr
    refine ⟨matched, matching, List.mem_filterMap.mpr ?_⟩
    exact ⟨output, merging, by simp [acyclic]⟩
  have same := singleton_of_member candidates _ one member
  change (if candidates.isEmpty then [finItem previous no incoming] else candidates) = _
  rw [same]
  rfl

/-- A successful freshened equation contributes exactly its one instantiated
body to the executable query. Default matching and merging cannot contribute
additional answers from the same equation. -/
theorem query_rule_candidate_exact (previous : Stack) (query lhs rhs : Atom)
    (incoming matched output : Metta.Bindings) (counter : Nat)
    (matching : matched ∈ Metta.matchAtoms
      (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.1 query)
    (merging : output ∈ Bindings.merge incoming matched)
    (acyclic : output.hasLoop = false) :
    Metta.Minimal.queryOpItemsOfRule previous query incoming counter (lhs, rhs) =
      [evalResult previous (instantiate output
        (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.2) output] := by
  unfold Metta.Minimal.queryOpItemsOfRule
  apply singleton_of_member
  · apply flatMap_at_most_one _ _ (match_at_most_one _ _)
    intro found _
    exact (List.length_filterMap_le _ _).trans (merge_at_most_one incoming found)
  · apply List.mem_flatMap.mpr
    refine ⟨matched, matching, List.mem_filterMap.mpr ?_⟩
    exact ⟨output, merging, by simp [acyclic]⟩

/-- Query results beneath a retained caller stay in the work queue; they
cannot be prematurely collected as top-level answers. -/
theorem evalResult_pending (parent : Frame) (continuation : Stack)
    (result : Atom) (bindings : Metta.Bindings) :
    isFinal (evalResult (parent :: continuation) result bindings) = false := by
  unfold evalResult
  split
  · exact atomToStack_pending _ _ _ _
  · rfl

/-- An isolated dispatcher equation is selected by the actual query fold,
including its fresh-name counter update. The premise describes the loaded
equation table, not an execution of the guest computation. -/
theorem query_single_rule (environment : MinEnv) (state : St) (previous : Stack)
    (query lhs rhs : Atom) (incoming matched output : Metta.Bindings)
    (candidates : candidatesW environment state.world query = [(lhs, rhs)])
    (notVariable : isVariableHeaded query = false)
    (stored : ClosedValueBindings incoming) (closed : query.vars = [])
    (matching : matched ∈ Metta.matchAtoms
      (freshenRuleAvoiding state.counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.1 query)
    (merging : output ∈ Bindings.merge incoming matched) :
    ClosedValueBindings output ∧
      queryOp environment state previous query incoming =
        ([evalResult previous (instantiate output
          (freshenRuleAvoiding state.counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.2)
            output],
         { state with counter :=
           (freshenRuleAvoiding state.counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).2 }) := by
  have outputClosed := merge_closed_closed_mem stored
    (matchAtomsWith_closed_value_mem _ query matched closed
      (List.mem_filter.mp matching).1) merging
  refine ⟨outputClosed, ?_⟩
  have selected := query_rule_candidate_exact previous query lhs rhs incoming matched output
    state.counter matching merging outputClosed.hasLoop_false
  simp only [queryOp, notVariable, Bool.false_eq_true, ↓reduceIte, candidates,
    List.foldl_cons, List.foldl_nil, Metta.Minimal.queryOpFoldStep, selected, List.nil_append,
    List.isEmpty_cons]

private theorem lookup_remove_other (bindings : Metta.Bindings) (removed queried : VarName)
    (different : queried ≠ removed) :
    Bindings.lookupVal (Bindings.removeVal bindings removed) queried =
      Bindings.lookupVal bindings queried := by
  induction bindings with
  | nil => rfl
  | cons relation rest ih =>
    cases relation with
    | eq left right => simpa [Bindings.removeVal, Bindings.lookupVal] using ih
    | val name payload =>
      by_cases same : name = removed
      · subst name
        simpa [Bindings.removeVal, Bindings.lookupVal, different] using ih
      · have keep : Bindings.removeVal (.val name payload :: rest) removed =
            .val name payload :: Bindings.removeVal rest removed := by
          simp [Bindings.removeVal, same]
        rw [keep]
        simp only [Bindings.lookupVal, ih]

/-- A local value assignment leaves every other key unchanged. -/
theorem lookup_add_other (bindings : Metta.Bindings) (name other : String)
    (payload : Atom) (different : other ≠ name) :
    Bindings.lookupVal (Bindings.addValRaw bindings name payload) other =
      Bindings.lookupVal bindings other := by
  simp [Bindings.addValRaw, Bindings.lookupVal, different,
    lookup_remove_other bindings name other different]

/-- Extending a closed-value store at a fresh key commutes with materializing
the old store. Previously computed operands remain fixed, while the newly
computed operand is filled by one structural substitution. -/
theorem instantiate_add_closed_value (bindings : Metta.Bindings) (name : VarName)
    (payload body : Atom) (stored : ClosedValueBindings bindings)
    (closed : payload.vars = []) (fresh : Bindings.lookupVal bindings name = none) :
    instantiate (Bindings.addValRaw bindings name payload) body =
      Subst.apply [(name, payload)] (instantiate bindings body) := by
  have outputClosed : ClosedValueBindings (Bindings.addValRaw bindings name payload) :=
    addValRaw_closed closed stored
  induction body with
  | sym | gnd => simp only [instantiate, Bindings.resolveAtom, Subst.apply]
  | var other =>
    simp only [instantiate, Bindings.resolveAtom]
    rw [ClosedValueBindings.resolve_eq_lookupVal outputClosed,
      ClosedValueBindings.resolve_eq_lookupVal stored]
    by_cases same : other = name
    · simp [same, Bindings.addValRaw, Bindings.lookupVal, fresh,
        Subst.apply, Subst.lookup]
    · have lookup : Bindings.lookupVal (Bindings.addValRaw bindings name payload) other =
          Bindings.lookupVal bindings other := by
        simp [Bindings.addValRaw, Bindings.lookupVal, same,
          lookup_remove_other bindings name other same]
      rw [lookup]
      cases found : Bindings.lookupVal bindings other with
      | none => simp [Subst.apply, Subst.lookup, same]
      | some value =>
        exact (Subst.apply_of_closed _ _ (stored.lookup_closed found)).symm
  | expr items ih =>
    simp only [instantiate, Bindings.resolveAtom, Subst.apply, List.map_map, Atom.expr.injEq]
    exact List.map_congr_left (fun child member => ih child member)

/-- Binding a fresh variable to a closed result performs ordinary structural
substitution in a body whose other variables are unassigned. This connects
the matcher's equality-class store with generated lexical continuations. -/
theorem instantiate_fresh_value (bindings : Metta.Bindings) (name : VarName)
    (payload body : Atom) (stored : ClosedValueBindings bindings)
    (closed : payload.vars = [])
    (fresh : ∀ variableName ∈ body.vars, Bindings.lookupVal bindings variableName = none) :
    instantiate (Bindings.addValRaw bindings name payload) body =
      Subst.apply [(name, payload)] body := by
  have outputClosed : ClosedValueBindings (Bindings.addValRaw bindings name payload) :=
    addValRaw_closed closed stored
  induction body with
  | sym | gnd => simp only [instantiate, Bindings.resolveAtom, Subst.apply]
  | var other =>
    simp only [instantiate, Bindings.resolveAtom, Subst.apply]
    rw [ClosedValueBindings.resolve_eq_lookupVal outputClosed]
    by_cases same : other = name
    · simp [Bindings.addValRaw, Bindings.lookupVal, Subst.lookup, same]
    · have absent := fresh other (by simp [Atom.vars])
      simp [Bindings.addValRaw, Bindings.lookupVal, Subst.lookup, same,
        lookup_remove_other bindings name other same, absent]
  | expr items ih =>
    simp only [instantiate, Bindings.resolveAtom, Subst.apply, Atom.expr.injEq]
    apply List.map_congr_left
    intro child member
    apply ih child member
    intro variableName occurs
    apply fresh variableName
    simp only [Atom.vars, List.mem_flatten, List.mem_map]
    exact ⟨child.vars, ⟨child, member, rfl⟩, occurs⟩

theorem occurs_closed (name : VarName) (atom : Atom) (closed : atom.vars = []) :
    Subst.occurs name atom = false := by
  induction atom with
  | sym | gnd => simp [Subst.occurs]
  | var other => simp [Atom.vars] at closed
  | expr atoms ih =>
      simp only [Subst.occurs, List.any_eq_false]
      intro child _
      have children : ∀ atom ∈ atoms, atom.vars = [] := by
        simpa [Atom.vars, List.flatten_eq_nil_iff] using closed
      simpa using ih child.val child.property (children child.val child.property)

mutual

private theorem matchRaw_closed_input (input pattern : Atom) (output : Metta.Bindings)
    (closed : input.vars = []) (member : output ∈ Metta.matchAtomsWith none input pattern) :
    ClosedValueBindings output := by
  cases input with
  | var name => simp [Atom.vars] at closed
  | sym symbol =>
    cases pattern with
    | var name =>
      simp [Metta.matchAtomsWith, Subst.occurs] at member
      subst output
      exact .val closed .nil
    | sym | gnd | expr =>
      simp [Metta.matchAtomsWith] at member
      obtain ⟨_, rfl⟩ := member
      exact .nil
  | gnd grounded =>
    cases pattern with
    | var name =>
      simp [Metta.matchAtomsWith, Subst.occurs] at member
      subst output
      exact .val closed .nil
    | sym | gnd | expr =>
      simp [Metta.matchAtomsWith] at member
      obtain ⟨_, rfl⟩ := member
      exact .nil
  | expr items =>
    cases pattern with
    | var name =>
      have absent := occurs_closed name (.expr items) closed
      simp [Metta.matchAtomsWith, absent] at member
      subst output
      exact .val closed .nil
    | sym | gnd =>
      simp [Metta.matchAtomsWith] at member
      obtain ⟨_, rfl⟩ := member
      exact .nil
    | expr patterns =>
      exact matchAll_closed_inputs [[]] items patterns output
        (expr_vars_nil_of_mem closed) (by
          intro bindings member
          simp only [List.mem_singleton] at member
          subst bindings
          exact .nil)
        member
termination_by sizeOf input + sizeOf pattern

private theorem matchAll_closed_inputs (acc : List Metta.Bindings)
    (inputs patterns : List Atom) (output : Metta.Bindings)
    (closed : ∀ input ∈ inputs, input.vars = [])
    (stored : ∀ bindings ∈ acc, ClosedValueBindings bindings)
    (member : output ∈ Metta.matchAll none acc inputs patterns) :
    ClosedValueBindings output := by
  cases inputs with
  | nil =>
    cases patterns with
    | nil => exact stored output member
    | cons => simp [Metta.matchAll] at member
  | cons input rest =>
    cases patterns with
    | nil => simp [Metta.matchAll] at member
    | cons pattern tail =>
      apply matchAll_closed_inputs _ rest tail output
        (fun atom here => closed atom (by simp [here])) _ member
      intro bindings here
      obtain ⟨incoming, incomingHere, here⟩ := List.mem_flatMap.mp here
      obtain ⟨matched, matchedHere, merged⟩ := List.mem_flatMap.mp here
      exact merge_closed_closed_mem (stored incoming incomingHere)
        (matchRaw_closed_input input pattern matched (closed input (by simp))
          (List.mem_filter.mp matchedHere).1) merged
termination_by sizeOf inputs + sizeOf patterns

end

/-- Generated argument data are matched on the left of `unify`. Like the
closed-query case on the right, this direction creates only closed values,
with no variable aliases or open payloads. -/
theorem matching_closed_input (input pattern : Atom) (output : Metta.Bindings)
    (closed : input.vars = []) (member : output ∈ Metta.matchAtoms input pattern) :
    ClosedValueBindings output :=
  matchRaw_closed_input input pattern output closed (List.mem_filter.mp member).1

theorem matching_closed_side (left right : Atom) (output : Metta.Bindings)
    (closed : left.vars = [] ∨ right.vars = [])
    (member : output ∈ Metta.matchAtoms left right) : ClosedValueBindings output := by
  rcases closed with closed | closed
  · exact matching_closed_input left right output closed member
  · exact matchAtomsWith_closed_value_mem left right output closed (List.mem_filter.mp member).1

mutual

private theorem matchRaw_closed_keys (left right : Atom) (output : Metta.Bindings)
    (allowed : List VarName) (closed : left.vars = [] ∨ right.vars = [])
    (scope : ∀ name ∈ left.vars ++ right.vars, name ∈ allowed)
    (member : output ∈ Metta.matchAtomsWith none left right) :
    ∀ name ∈ bindingValueKeys output, name ∈ allowed := by
  cases left with
  | var key =>
    have targetClosed : right.vars = [] := by simpa [Atom.vars] using closed
    have absent := occurs_closed key right targetClosed
    cases right with
    | var => simp [Atom.vars] at targetClosed
    | sym | gnd | expr =>
      simp [Metta.matchAtomsWith, absent] at member
      subst output
      intro name here
      simp only [bindingValueKeys, List.mem_singleton] at here
      subst name
      exact scope key (by simp [Atom.vars])
  | sym symbol =>
    cases right with
    | var key =>
      simp [Metta.matchAtomsWith, Subst.occurs] at member
      subst output
      intro name here
      simp only [bindingValueKeys, List.mem_singleton] at here
      subst name
      exact scope key (by simp [Atom.vars])
    | sym | gnd | expr =>
      simp [Metta.matchAtomsWith] at member
      obtain ⟨_, rfl⟩ := member
      simp [bindingValueKeys]
  | gnd value =>
    cases right with
    | var key =>
      simp [Metta.matchAtomsWith, Subst.occurs] at member
      subst output
      intro name here
      simp only [bindingValueKeys, List.mem_singleton] at here
      subst name
      exact scope key (by simp [Atom.vars])
    | sym | gnd | expr =>
      simp [Metta.matchAtomsWith] at member
      obtain ⟨_, rfl⟩ := member
      simp [bindingValueKeys]
  | expr items =>
    cases right with
    | var key =>
      have inputClosed : (Atom.expr items).vars = [] := by simpa [Atom.vars] using closed
      have absent := occurs_closed key (.expr items) inputClosed
      simp [Metta.matchAtomsWith, absent] at member
      subst output
      intro name here
      simp only [bindingValueKeys, List.mem_singleton] at here
      subst name
      exact scope key (by simp [Atom.vars])
    | sym | gnd =>
      simp [Metta.matchAtomsWith] at member
      obtain ⟨_, rfl⟩ := member
      simp [bindingValueKeys]
    | expr patterns =>
      apply matchAll_closed_keys [[]] items patterns output allowed closed scope
      · intro bindings here
        simp only [List.mem_singleton] at here
        subst bindings
        exact .nil
      · simp [bindingValueKeys]
      · exact member
termination_by sizeOf left + sizeOf right

private theorem matchAll_closed_keys (acc : List Metta.Bindings)
    (left right : List Atom) (output : Metta.Bindings) (allowed : List VarName)
    (closed : (Atom.expr left).vars = [] ∨ (Atom.expr right).vars = [])
    (scope : ∀ name ∈ (Atom.expr left).vars ++ (Atom.expr right).vars, name ∈ allowed)
    (stored : ∀ bindings ∈ acc, ClosedValueBindings bindings)
    (keys : ∀ bindings ∈ acc, ∀ name ∈ bindingValueKeys bindings, name ∈ allowed)
    (member : output ∈ Metta.matchAll none acc left right) :
    ∀ name ∈ bindingValueKeys output, name ∈ allowed := by
  cases left with
  | nil =>
    cases right with
    | nil => exact keys output member
    | cons => simp [Metta.matchAll] at member
  | cons input rest =>
    cases right with
    | nil => simp [Metta.matchAll] at member
    | cons pattern tail =>
      have headsClosed : input.vars = [] ∨ pattern.vars = [] := by
        rcases closed with h | h
        · exact .inl (expr_vars_nil_of_mem h input (by simp))
        · exact .inr (expr_vars_nil_of_mem h pattern (by simp))
      have tailsClosed : (Atom.expr rest).vars = [] ∨ (Atom.expr tail).vars = [] := by
        rcases closed with h | h
        · exact .inl ((show input.vars = [] ∧ (Atom.expr rest).vars = [] by
            simpa [Atom.vars] using h).2)
        · exact .inr ((show pattern.vars = [] ∧ (Atom.expr tail).vars = [] by
            simpa [Atom.vars] using h).2)
      have headScope : ∀ name ∈ input.vars ++ pattern.vars, name ∈ allowed := by
        intro name here
        apply scope name
        simpa only [Atom.vars, List.map_cons, List.flatten_cons, List.mem_append] using
          (List.mem_append.mp here).elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inl h))
      have tailScope : ∀ name ∈ (Atom.expr rest).vars ++ (Atom.expr tail).vars, name ∈ allowed := by
        intro name here
        apply scope name
        simpa only [Atom.vars, List.map_cons, List.flatten_cons, List.mem_append] using
          (List.mem_append.mp here).elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))
      apply matchAll_closed_keys _ rest tail output allowed tailsClosed tailScope _ _ member
      · intro bindings here
        obtain ⟨incoming, incomingHere, here⟩ := List.mem_flatMap.mp here
        obtain ⟨matched, matchedHere, merged⟩ := List.mem_flatMap.mp here
        exact merge_closed_closed_mem (stored incoming incomingHere)
          (matching_closed_side input pattern matched headsClosed matchedHere) merged
      · intro bindings here name key
        obtain ⟨incoming, incomingHere, here⟩ := List.mem_flatMap.mp here
        obtain ⟨matched, matchedHere, merged⟩ := List.mem_flatMap.mp here
        rcases merge_closed_closed_valueKeys_subset (stored incoming incomingHere)
          (matching_closed_side input pattern matched headsClosed matchedHere) merged name key with h | h
        · exact keys incoming incomingHere name h
        · exact matchRaw_closed_keys input pattern matched allowed headsClosed headScope
            (List.mem_filter.mp matchedHere).1 name h
termination_by sizeOf left + sizeOf right

end

/-- Closed-data matching writes only variables of its two inputs. In
particular, a callee's fresh pattern cannot write a caller's local variables. -/
theorem matching_closed_keys (left right : Atom) (output : Metta.Bindings)
    (closed : left.vars = [] ∨ right.vars = [])
    (member : output ∈ Metta.matchAtoms left right) :
    ∀ name ∈ bindingValueKeys output, name ∈ left.vars ++ right.vars :=
  matchRaw_closed_keys left right output (left.vars ++ right.vars) closed
    (fun _ here => here) (List.mem_filter.mp member).1

/-- Closed-data matching cannot assign a variable absent from its pattern. -/
theorem matching_closed_preserves_unassigned
    (target pattern : Atom) (incoming matched output : Metta.Bindings) (name : VarName)
    (stored : ClosedValueBindings incoming) (closed : target.vars = [])
    (unassigned : Bindings.lookupVal incoming name = none) (absent : name ∉ pattern.vars)
    (matching : matched ∈ Metta.matchAtoms target pattern)
    (merging : output ∈ Bindings.merge incoming matched) :
    Bindings.lookupVal output name = none := by
  have matchedClosed := matching_closed_side target pattern matched (.inl closed) matching
  have outputClosed := merge_closed_closed_mem stored matchedClosed merging
  apply outputClosed.toValueBindings.lookup_none_of_not_key
  intro key
  rcases merge_closed_closed_valueKeys_subset stored matchedClosed merging name key with old | new
  · obtain ⟨value, found⟩ := stored.toValueBindings.lookup_some_of_key_mem old
    simp [unassigned] at found
  · apply absent
    simpa only [closed, List.nil_append] using
      matching_closed_keys target pattern matched (.inl closed) matching name new

theorem matching_closed_preserves_private_variable
    (target pattern : Atom) (incoming matched output : Metta.Bindings) (name : VarName)
    (stored : ClosedValueBindings incoming) (closed : target.vars = [])
    (unassigned : Bindings.lookupVal incoming name = none) (absent : name ∉ pattern.vars)
    (matching : matched ∈ Metta.matchAtoms target pattern)
    (merging : output ∈ Bindings.merge incoming matched) :
    instantiate output (.var name) = .var name := by
  have outputClosed := merge_closed_closed_mem stored
    (matching_closed_side target pattern matched (.inl closed) matching) merging
  simp only [instantiate, Bindings.resolveAtom]
  rw [outputClosed.resolve_eq_lookupVal,
    matching_closed_preserves_unassigned target pattern incoming matched output name
      stored closed unassigned absent matching merging]
  rfl


/-- A recursive equation call cannot assign an unassigned caller variable.
The runtime's avoidance set contains every live stack variable; matching
writes only its own fresh pattern variables, and closed-value merging adds
no other keys. -/
theorem query_preserves_unassigned_caller (previous : Stack) (query lhs rhs : Atom)
    (incoming matched output : Metta.Bindings) (counter : Nat) (name : VarName)
    (stored : ClosedValueBindings incoming) (closed : query.vars = [])
    (live : name ∈ liveStackVars previous) (unassigned : Bindings.lookupVal incoming name = none)
    (matching : matched ∈ Metta.matchAtoms
      (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.1
      query)
    (merging : output ∈ Bindings.merge incoming matched) :
    Bindings.lookupVal output name = none := by
  let pattern := (freshenRuleAvoiding counter
    (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.1
  have matchedClosed := matching_closed_side pattern query matched (.inr closed) matching
  have outputClosed := merge_closed_closed_mem stored matchedClosed merging
  apply ValueBindings.lookup_none_of_not_key outputClosed.toValueBindings
  intro key
  rcases merge_closed_closed_valueKeys_subset stored matchedClosed merging name key with old | new
  · obtain ⟨value, found⟩ := stored.toValueBindings.lookup_some_of_key_mem old
    simp [unassigned] at found
  · have patternKey : name ∈ pattern.vars := by
      simpa only [closed, List.append_nil] using
        matching_closed_keys pattern query matched (.inr closed) matching name new
    have fresh := freshenRuleAvoiding_vars_fresh counter
      (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs name
      (List.mem_append_left _ patternKey)
    apply fresh
    simp only [Metta.Minimal.queryOpAvoid, List.mem_append]
    exact .inr live

/-- Runtime resolution consequently leaves that caller variable syntactically
intact. This is the frame condition required when a callee returns to a
compiled continuation whose local control variables have not run yet. -/
theorem query_preserves_caller_variable (previous : Stack) (query lhs rhs : Atom)
    (incoming matched output : Metta.Bindings) (counter : Nat) (name : VarName)
    (stored : ClosedValueBindings incoming) (closed : query.vars = [])
    (live : name ∈ liveStackVars previous) (unassigned : Bindings.lookupVal incoming name = none)
    (matching : matched ∈ Metta.matchAtoms
      (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1.1
      query)
    (merging : output ∈ Bindings.merge incoming matched) :
    instantiate output (.var name) = .var name := by
  have outputClosed := merge_closed_closed_mem stored
    (matching_closed_side _ query matched (.inr closed) matching) merging
  simp only [instantiate, Bindings.resolveAtom]
  rw [ClosedValueBindings.resolve_eq_lookupVal outputClosed,
    query_preserves_unassigned_caller previous query lhs rhs incoming matched output counter name
      stored closed live unassigned matching merging]
  rfl

/-- Matching encoded input and merging it into a closed-value frame preserves
that frame discipline. Acyclicity follows from the representation, so it is
not an additional condition imposed on successful generated matches. -/
theorem unify_closed_candidate (previous : Stack) (input pattern yes no : Atom)
    (incoming matched output : Metta.Bindings)
    (stored : ClosedValueBindings incoming) (closed : input.vars = [])
    (matching : matched ∈ Metta.matchAtoms input pattern)
    (merging : output ∈ Bindings.merge incoming matched) :
    ClosedValueBindings output ∧
      unifyOp previous input pattern yes no incoming =
        [finItem previous (instantiate output yes) output] := by
  have outputClosed := merge_closed_closed_mem stored
    (matching_closed_input input pattern matched closed matching) merging
  exact ⟨outputClosed, unify_candidate_exact previous input pattern yes no
    incoming matched output matching merging outputClosed.hasLoop_false⟩

/-- Matching a closed payload against one variable has exactly one result. -/
theorem match_closed_variable (payload : Atom) (name : VarName)
    (closed : payload.vars = []) :
    Metta.matchAtoms payload (.var name) = [[.val name payload]] := by
  have absent : name ∉ payload.vars := by simp [closed]
  have occurs := occurs_closed name payload closed
  have acyclic := Metta.Bindings.hasLoop_singleton_val_of_not_mem name payload absent
  cases payload <;> simp_all [Metta.matchAtoms, Metta.matchAtomsWith, Atom.vars]

/-- A constructor tag does not alter the payload's single binding. -/
theorem match_tagged_variable (tag : String) (payload : Atom) (name : VarName)
    (closed : payload.vars = []) :
    Metta.matchAtoms (.expr [.sym tag, payload]) (.expr [.sym tag, .var name]) =
      [[.val name payload]] := by
  have absent : name ∉ payload.vars := by simp [closed]
  have occurs := occurs_closed name payload closed
  have acyclic := Metta.Bindings.hasLoop_singleton_val_of_not_mem name payload absent
  have noVariable : ∀ other, payload ≠ .var other := by
    intro other same
    simp [same, Atom.vars] at closed
  have merged : Metta.Bindings.merge [] [.val name payload] = [[.val name payload]] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne, Metta.Bindings.addValRaw, Metta.Bindings.removeVal]
      using Metta.Bindings.addVarBinding_fresh
        (b := []) (x := name) (v := payload) (by rfl) noVariable
  have raw : Metta.matchAtomsWith none payload (.var name) = [[.val name payload]] := by
    cases payload <;> simp_all [Metta.matchAtomsWith, Atom.vars]
  have emptyAcyclic : Metta.Bindings.hasLoop [] = false := rfl
  simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll, raw, merged, acyclic,
    Metta.Bindings.merge_empty_right, emptyAcyclic]

/-- A two-input equation header matches closed arguments exactly once,
retaining both values under its distinct parameter names. -/
theorem match_two_input_header (head firstName secondName : String)
    (firstValue secondValue : Atom) (different : secondName ≠ firstName)
    (firstClosed : firstValue.vars = []) (secondClosed : secondValue.vars = []) :
    Metta.matchAtoms (.expr [.sym head, .var firstName, .var secondName])
      (.expr [.sym head, firstValue, secondValue]) =
      [[.val secondName secondValue, .val firstName firstValue]] := by
  have raw (name : String) (payload : Atom) (closed : payload.vars = []) :
      Metta.matchAtomsWith none (.var name) payload = [[.val name payload]] := by
    have noOccurs := occurs_closed name payload closed
    cases payload <;> simp_all [Metta.matchAtomsWith, Atom.vars]
  have firstStored : ClosedValueBindings [.val firstName firstValue] := .val firstClosed .nil
  have secondStored : ClosedValueBindings [.val secondName secondValue] := .val secondClosed .nil
  have bothStored : ClosedValueBindings [.val secondName secondValue, .val firstName firstValue] :=
    .val secondClosed firstStored
  have firstMerge : Bindings.merge [] [.val firstName firstValue] = [[.val firstName firstValue]] := by
    simpa using merge_closed_noConflict_eq firstStored (by simp [bindingValueKeys]) .nil
      (by simp [bindingValueKeys])
  have secondMerge := merge_singleton_closed_vals_eq firstClosed secondClosed different
  have sameHead : Metta.matchAtomsWith none (.sym head) (.sym head) = [[]] := by
    simp only [Metta.matchAtomsWith, beq_self_eq_true, if_true]
  rw [Metta.matchAtoms, Metta.matchAtomsWith]
  simp [Metta.matchAll, sameHead, raw firstName firstValue firstClosed,
    raw secondName secondValue secondClosed, firstMerge, secondMerge,
    firstStored.hasLoop_false, secondStored.hasLoop_false, bothStored.hasLoop_false,
    Bindings.merge_empty_right, show Bindings.hasLoop [] = false from rfl]

/-- Actual capture-avoiding query freshening makes a two-input header viable
in every closed-value store, even when its original names already occur in
the caller. This supplies match and merge witnesses rather than assuming them. -/
theorem query_two_input_header (head firstName secondName : String)
    (firstValue secondValue rhs : Atom) (different : secondName ≠ firstName)
    (firstClosed : firstValue.vars = []) (secondClosed : secondValue.vars = [])
    (counter : Nat) (previous : Stack) (incoming : Metta.Bindings)
    (stored : ClosedValueBindings incoming) :
    let lhs := Atom.expr [.sym head, .var firstName, .var secondName]
    let query := Atom.expr [.sym head, firstValue, secondValue]
    let fresh := (freshenRuleAvoiding counter
      (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs).1
    ∃ matched output, matched ∈ Metta.matchAtoms fresh.1 query ∧
      output ∈ Bindings.merge incoming matched ∧ ClosedValueBindings output := by
  intro lhs query fresh
  obtain ⟨rename, injective, freshened⟩ := freshenRuleAvoiding_renaming counter
    (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs
  let matched : Metta.Bindings :=
    [.val (rename secondName) secondValue, .val (rename firstName) firstValue]
  have distinct : rename secondName ≠ rename firstName := fun same => different (injective same)
  have queryClosed : query.vars = [] := by simp [query, Atom.vars, firstClosed, secondClosed]
  have matching : matched ∈ Metta.matchAtoms fresh.1 query := by
    simp only [fresh, freshened, lhs, query, renBy, List.map_cons, List.map_nil]
    rw [match_two_input_header head (rename firstName) (rename secondName)
      firstValue secondValue distinct firstClosed secondClosed]
    exact List.mem_singleton.mpr rfl
  have matchedClosed : ClosedValueBindings matched := .val secondClosed (.val firstClosed .nil)
  have nodup : (bindingValueKeys matched).Nodup := by simp [matched, bindingValueKeys, distinct]
  have disjoint : ∀ name ∈ bindingValueKeys matched, name ∉ bindingValueKeys incoming := by
    intro name member key
    have patternKey : name ∈ fresh.1.vars := by
      simpa only [queryClosed, List.append_nil] using
        matching_closed_keys fresh.1 query matched (.inr queryClosed) matching name member
    have privateName := freshenRuleAvoiding_vars_fresh counter
      (Metta.Minimal.queryOpAvoid previous query incoming) lhs rhs name
      (List.mem_append_left _ patternKey)
    apply privateName
    simp only [Metta.Minimal.queryOpAvoid, List.mem_append]
    exact .inl (.inl (bindingValueKey_mem_vars key))
  have merging := merge_closed_noConflict_mem matchedClosed nodup stored disjoint
  exact ⟨matched, matched.reverse ++ incoming, matching, merging,
    merge_closed_closed_mem stored matchedClosed merging⟩

/-- A successful constructor match binds a fresh payload variable, without
discarding the incoming binding frame. -/
theorem unify_tagged_variable (previous : Stack) (tag : String)
    (payload yes no : Atom) (name : VarName) (bindings : Metta.Bindings)
    (closed : payload.vars = [])
    (fresh : Metta.Bindings.classValues bindings name = [])
    (acyclic : (Metta.Bindings.addValRaw bindings name payload).hasLoop = false) :
    unifyOp previous (.expr [.sym tag, payload]) (.expr [.sym tag, .var name])
        yes no bindings =
      [finItem previous (instantiate (Metta.Bindings.addValRaw bindings name payload) yes)
        (Metta.Bindings.addValRaw bindings name payload)] := by
  have noVariable : ∀ other, payload ≠ .var other := by
    intro other same
    simp [same, Atom.vars] at closed
  have merged : Metta.Bindings.merge bindings [.val name payload] =
      [Metta.Bindings.addValRaw bindings name payload] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using
      Metta.Bindings.addVarBinding_fresh fresh noVariable
  simp [unifyOp, match_tagged_variable tag payload name closed, merged, acyclic]

/-- An unmatched branch remains in the original frame; it does not introduce
bindings from the rejected pattern. -/
theorem unify_refuses (previous : Stack) (atom pattern yes no : Atom)
    (bindings : Metta.Bindings) (missing : Metta.matchAtoms atom pattern = []) :
    unifyOp previous atom pattern yes no bindings = [finItem previous no bindings] := by
  simp [unifyOp, missing]

/-- A match that conflicts with the incoming frame is also refused. Neither
partial matching nor a discarded cyclic merge can leak a new binding. -/
theorem unify_no_candidate (previous : Stack) (atom pattern yes no : Atom)
    (bindings : Metta.Bindings)
    (refused : ¬∃ matched merged,
      matched ∈ Metta.matchAtoms atom pattern ∧ merged ∈ Metta.Bindings.merge bindings matched ∧
        merged.hasLoop = false) :
    unifyOp previous atom pattern yes no bindings = [finItem previous no bindings] := by
  have empty : ((Metta.matchAtoms atom pattern).flatMap fun matched =>
      (Metta.Bindings.merge bindings matched).filterMap fun output =>
        if output.hasLoop then none
        else some (finItem previous (instantiate output yes) output)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro item member
    obtain ⟨matched, matchedHere, member⟩ := List.mem_flatMap.mp member
    obtain ⟨output, mergedHere, returned⟩ := List.mem_filterMap.mp member
    have acyclic : output.hasLoop = false := by
      cases loops : output.hasLoop <;> simp_all
    exact refused ⟨matched, output, matchedHere, mergedHere, acyclic⟩
  simp only [unifyOp, empty, List.isEmpty_nil, ↓reduceIte]

theorem match_symbol_tagged (symbol tag : String) (payload : Atom) :
    Metta.matchAtoms (.sym symbol) (.expr [.sym tag, payload]) = [] := by
  simp [Metta.matchAtoms, Metta.matchAtomsWith, Atom.equiv]

/-- Once any compatible acyclic match exists, the fallback is absent from
the result queue. This holds independently of what the selected body returns. -/
theorem unify_viable_ignores_fallback (previous : Stack)
    (atom pattern yes firstFallback secondFallback : Atom) (bindings : Metta.Bindings)
    (viable : ∃ matched merged,
      matched ∈ Metta.matchAtoms atom pattern ∧ merged ∈ Metta.Bindings.merge bindings matched ∧
        merged.hasLoop = false) :
    unifyOp previous atom pattern yes firstFallback bindings =
      unifyOp previous atom pattern yes secondFallback bindings := by
  obtain ⟨matched, merged, matchedHere, mergedHere, acyclic⟩ := viable
  have present : finItem previous (instantiate merged yes) merged ∈
      ((Metta.matchAtoms atom pattern).flatMap fun found =>
        (Metta.Bindings.merge bindings found).filterMap fun output =>
          if output.hasLoop then none
          else some (finItem previous (instantiate output yes) output)) := by
    apply List.mem_flatMap.mpr
    refine ⟨matched, matchedHere, List.mem_filterMap.mpr ?_⟩
    exact ⟨merged, mergedHere, by simp [acyclic]⟩
  have nonempty := List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem present)
  simp only [unifyOp, nonempty, Bool.false_eq_true, ↓reduceIte]

theorem unify_same_symbol (previous : Stack) (symbol : String) (yes no : Atom)
    (bindings : Metta.Bindings) (acyclic : bindings.hasLoop = false) :
    unifyOp previous (.sym symbol) (.sym symbol) yes no bindings =
      [finItem previous (instantiate bindings yes) bindings] := by
  have matched : Metta.matchAtoms (.sym symbol) (.sym symbol) = [[]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Bindings.hasLoop, Metta.Bindings.vars]
  simp [unifyOp, matched, Metta.Bindings.merge_empty_right, acyclic]

/-- Resuming an embedded instruction materializes its operands in the current
frame before pushing the next instruction. -/
theorem function_embedded_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody body : Atom)
    (scope : List VarName) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (embedded : isEmbeddedOp (instantiate bindings body) = true) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
        (finItem (parent :: continuation) body bindings :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (instantiate bindings body) (parent :: continuation), bindings⟩ :: rest)
        done := by
  intro parent
  apply driver_singleton_step
  · simp only [interpretStack1, finItem, parent, ↓reduceIte]
    split
    · rename_i returned same
      simp [same, isEmbeddedOp] at embedded
    · simp [embedded]
  · exact atomToStack_pending _ _ _ _

/-- The function handler materializes the next branch before executing it. -/
theorem function_unify_enters (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody atom pattern yes no : Atom)
    (scope : List VarName) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
        (finItem (parent :: continuation)
          (.expr [.sym "unify", atom, pattern, yes, no]) bindings :: rest) done =
      interpretFuel environment fuel state
        (⟨atomToStack (.expr [.sym "unify", instantiate bindings atom,
          instantiate bindings pattern, instantiate bindings yes, instantiate bindings no])
          (parent :: continuation), bindings⟩ :: rest) done := by
  intro parent
  apply driver_singleton_step
  · simp [interpretStack1, finItem, parent, instantiate, Metta.Bindings.resolveAtom, isEmbeddedOp]
  · exact atomToStack_pending _ _ _ _

/-- A selected return leaves the enclosing function through its actual caller. -/
theorem selected_return_to_caller (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parentBody value : Atom) (scope : List VarName)
    (caller : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings)) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + 1) state
        (finItem (parent :: caller :: continuation) (.expr [.sym "return", value])
          bindings :: rest) done =
      interpretFuel environment fuel state
        (finItem (caller :: continuation) (instantiate bindings value) bindings :: rest) done := by
  intro parent
  apply driver_singleton_step
  · exact step_function_return environment fuel state (caller :: continuation)
      scope parentBody value bindings
  · rfl

/-- One actual interpreter step selects the unique successful branch. -/
theorem unify_tagged_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (tag : String) (payload yes no : Atom)
    (name : VarName) (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (closed : payload.vars = [])
    (fresh : Metta.Bindings.classValues bindings name = [])
    (acyclic : (Metta.Bindings.addValRaw bindings name payload).hasLoop = false) :
    interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "unify", .expr [.sym tag, payload],
          .expr [.sym tag, .var name], yes, no]) (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (instantiate (Metta.Bindings.addValRaw bindings name payload) yes)
          (Metta.Bindings.addValRaw bindings name payload) :: rest) done := by
  apply driver_singleton_step
  · simp only [atomToStack, step_unify]
    exact congrArg (fun items => (items, state))
      (unify_tagged_variable _ tag payload yes no name bindings closed fresh acyclic)
  · rfl

/-- All conflicting or cyclic matches are discarded before falling back.
The driver retains the incoming frame and the rest of the work queue. -/
theorem unify_no_candidate_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (atom pattern yes no : Atom)
    (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (refused : ¬∃ matched merged,
      matched ∈ Metta.matchAtoms atom pattern ∧ merged ∈ Metta.Bindings.merge bindings matched ∧
        merged.hasLoop = false) :
    interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "unify", atom, pattern, yes, no])
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) no bindings :: rest) done := by
  apply driver_singleton_step
  · simp only [atomToStack, step_unify]
    exact congrArg (fun items => (items, state))
      (unify_no_candidate _ _ _ _ _ _ refused)
  · rfl

/-- Replacing a fallback after a viable match cannot affect any later driver
result or state, even if the chosen body subsequently refuses. -/
theorem unify_viable_execution (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (atom pattern yes firstFallback secondFallback : Atom)
    (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (viable : ∃ matched merged,
      matched ∈ Metta.matchAtoms atom pattern ∧ merged ∈ Metta.Bindings.merge bindings matched ∧
        merged.hasLoop = false) :
    interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "unify", atom, pattern, yes, firstFallback])
          continuation, bindings⟩ :: rest) done =
      interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "unify", atom, pattern, yes, secondFallback])
          continuation, bindings⟩ :: rest) done := by
  rw [FuelConvergenceInterpreter.interpretFuel_succ,
    FuelConvergenceInterpreter.interpretFuel_succ]
  simp only [atomToStack, step_unify]
  rw [unify_viable_ignores_fallback continuation atom pattern yes
    firstFallback secondFallback bindings viable]

/-- Failure of a pattern consumes one step and selects only its fallback. -/
theorem unify_unmatched_selects (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (atom pattern yes no : Atom)
    (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Atom × Metta.Bindings))
    (missing : Metta.matchAtoms atom pattern = []) :
    interpretFuel environment (fuel + 1) state
        (⟨atomToStack (.expr [.sym "unify", atom, pattern, yes, no])
          (parent :: continuation), bindings⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) no bindings :: rest) done := by
  apply driver_singleton_step
  · simp only [atomToStack, step_unify]
    exact congrArg (fun items => (items, state)) (unify_refuses _ _ _ _ _ _ missing)
  · rfl

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
