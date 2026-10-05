import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaCallExecution

/-!
# Source rows in the emitted dispatcher

The actual stateful emitter retains each source row, its generated pattern,
name table and body, in order. This connects the existing source selector to
the concrete runtime scan without a second checking or compilation algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open OrderedDispatch
open Control
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlExecution
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Metta.Minimal

mutual

private theorem pattern_table_interval (source : Term) (first : Nat) :
    ∀ entry ∈ (pattern source first).1.2,
      ∃ index, first ≤ index ∧ index < (pattern source first).2 ∧
        entry.2 = .var (freshName index) := by
  cases source with
  | sym => simp [pattern_symbol]
  | lit => simp [pattern_literal]
  | var name =>
    intro entry member
    have same : entry = (name, .var (freshName first)) := List.mem_singleton.mp member
    subst entry
    exact ⟨first, le_rfl, Nat.lt_succ_self _, rfl⟩
  | expr items => simpa only [pattern_expression] using patterns_table_interval items first
  | list items => simpa only [pattern_list] using patterns_table_interval items first
termination_by sizeOf source

private theorem patterns_table_interval (source : List Term) (first : Nat) :
    ∀ entry ∈ (patterns source first).1.2,
      ∃ index, first ≤ index ∧ index < (patterns source first).2 ∧
        entry.2 = .var (freshName index) := by
  cases source with
  | nil => simp [patterns_nil]
  | cons head rest =>
    rw [patterns_cons]
    intro entry member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨index, lower, upper, same⟩ := pattern_table_interval head first entry member
      exact ⟨index, lower, upper.trans_le (patterns_name_bounds rest _).1, same⟩
    · obtain ⟨index, lower, upper, same⟩ := patterns_table_interval rest _ entry member
      exact ⟨index, (pattern_name_bounds head first).1.trans lower, upper, same⟩
termination_by sizeOf source

end

private theorem patterns_table_bound (source : List Term) (first : Nat) :
    ∀ entry ∈ (patterns source first).1.2, UsesBefore (patterns source first).2 entry.2 := by
  intro entry member
  obtain ⟨index, _, upper, same⟩ := patterns_table_interval source first entry member
  simpa only [same, usesBefore_freshName] using upper

/-- A row's pattern and body share the allocator state and generated name
table. The existential records its actual position in the name supply. -/
def EmittedCase (program : Program) (fuel : Atom) (row : CaseRow)
    (branch : Atom × Atom) (lower : Nat := 0) : Prop :=
  ∃ first, lower ≤ first ∧
    branch.1 = (patterns row.equation.params first).1.1 ∧
    branch.2 = (expression program (patterns row.equation.params first).1.2
      fuel row.equation.body (patterns row.equation.params first).2).1

theorem EmittedCase.lower {program : Program} {fuel : Atom} {row : CaseRow}
    {branch : Atom × Atom} {lower upper : Nat}
    (emitted : EmittedCase program fuel row branch upper) (before : lower ≤ upper) :
    EmittedCase program fuel row branch lower := by
  obtain ⟨first, allocated, patternCode, bodyCode⟩ := emitted
  exact ⟨first, before.trans allocated, patternCode, bodyCode⟩

private theorem substitute_absent (name : String) (replacement atom : Atom)
    (absent : ¬AtomOccurs atom name) : substituteName name replacement atom = atom := by
  apply toLeaTTaAtom_injective
  rw [substituteName_runtime]
  exact substitute_fresh name (toLeaTTaAtom replacement) (toLeaTTaAtom atom)
    (fun member => absent (atomOccurs_of_mem_translated_vars member))

/-- A dispatcher input is allocated before every row-local name. Filling
that input therefore changes only the body's source fuel, leaving the
pattern, its name table and all local control binders intact. -/
theorem EmittedCase.substitute_input {program : Program} {fuel : Atom} {row : CaseRow}
    {branch : Atom × Atom} {lower : Nat}
    (emitted : EmittedCase program fuel row branch lower)
    (index : Nat) (replacement : Atom) (before : index < lower)
    (fuelBound : UsesBefore lower fuel) :
    EmittedCase program (substituteName (freshName index) replacement fuel) row
      (branch.1, substituteName (freshName index) replacement branch.2) lower := by
  obtain ⟨first, allocated, patternCode, bodyCode⟩ := emitted
  have startBefore : index < (patterns row.equation.params first).2 :=
    (before.trans_le allocated).trans_le (patterns_name_bounds _ _).1
  have nameTable : (patterns row.equation.params first).1.2.map
      (fun entry => (entry.1, substituteName (freshName index) replacement entry.2)) =
        (patterns row.equation.params first).1.2 := by
    calc
      _ = (patterns row.equation.params first).1.2.map id := by
        apply List.map_congr_left
        intro entry member
        obtain ⟨other, later, _, same⟩ := patterns_table_interval _ _ entry member
        have distinct : freshName other ≠ freshName index := by
          intro same
          have equalIndex := freshName_injective same
          omega
        exact Prod.ext rfl (by simp only [id_eq, same, substituteName, distinct, if_false])
      _ = _ := List.map_id _
  refine ⟨first, allocated, patternCode, ?_⟩
  rw [bodyCode]
  have transported := congrArg Prod.fst (expression_substitution program
    (patterns row.equation.params first).1.2 fuel replacement row.equation.body index
      (patterns row.equation.params first).2 startBefore (patterns_table_bound _ _)
      (fuelBound.mono (allocated.trans (patterns_name_bounds _ _).1)))
  simpa only [nameTable] using transported

theorem EmittedCase.pattern_input_fixed {program : Program} {fuel : Atom} {row : CaseRow}
    {branch : Atom × Atom} {lower : Nat}
    (emitted : EmittedCase program fuel row branch lower)
    (index : Nat) (replacement : Atom) (before : index < lower) :
    substituteName (freshName index) replacement branch.1 = branch.1 := by
  obtain ⟨first, allocated, patternCode, _⟩ := emitted
  apply substitute_absent
  rw [patternCode]
  intro occurrence
  obtain ⟨other, later, _, same⟩ := (patterns_name_bounds _ _).2 _ occurrence
  have equalIndex := freshName_injective same
  omega

private theorem row_loop_preserves (program : Program) (fuel : Atom)
    (rows : List CaseRow) (acc : List (Atom × Atom)) (first : Nat)
    (fuelBound : UsesBefore first fuel) :
    let generated := (forIn rows acc fun row branches => do
      let (left, names) ← patterns row.equation.params
      let right ← expression program names fuel row.equation.body
      pure (ForInStep.yield (branches ++ [(left, right)])) : Emit (List (Atom × Atom))) first
    ∃ added, generated.1 = acc ++ added ∧
      List.Forall₂ (fun row branch => EmittedCase program fuel row branch first) rows added ∧
      first ≤ generated.2 ∧
      ∀ branch ∈ added, UsesBefore generated.2 branch.1 ∧ UsesBefore generated.2 branch.2 := by
  induction rows generalizing acc first with
  | nil => exact ⟨[], (List.append_nil acc).symm, .nil, le_rfl, by simp⟩
  | cons row rows ih =>
    rcases hp : patterns row.equation.params first with ⟨⟨left, names⟩, afterPattern⟩
    rcases hr : expression program names fuel row.equation.body afterPattern with ⟨right, next⟩
    have patternLater : first ≤ afterPattern := by
      simpa only [hp] using (patterns_name_bounds row.equation.params first).1
    have namesBound : ∀ entry ∈ names, UsesBefore afterPattern entry.2 := by
      simpa only [hp] using patterns_table_bound row.equation.params first
    have bodyLater : afterPattern < next := by
      simpa only [hr] using
        (expression_scope program names fuel row.equation.body afterPattern namesBound
          (fuelBound.mono patternLater)).1
    have later : first ≤ next := patternLater.trans (Nat.le_of_lt bodyLater)
    have leftBound : UsesBefore next left := by
      intro name occurrence
      have boundedRows := (patterns_name_bounds row.equation.params first).2
      rw [hp] at boundedRows
      obtain ⟨index, _, upper, same⟩ := boundedRows name occurrence
      exact ⟨index, upper.trans_le (Nat.le_of_lt bodyLater), same⟩
    have rightBound : UsesBefore next right := by
      simpa only [hr] using
        (expression_scope program names fuel row.equation.body afterPattern namesBound
          (fuelBound.mono patternLater)).2
    obtain ⟨added, generated, related, afterRows, rowBounds⟩ :=
      ih (acc ++ [(left, right)]) next (fuelBound.mono later)
    have earlierRelated : List.Forall₂
        (fun row branch => EmittedCase program fuel row branch first) rows added :=
      related.imp (fun _ _ related => related.lower later)
    refine ⟨(left, right) :: added, ?_, .cons ⟨first, le_rfl, ?_, ?_⟩ earlierRelated, ?_, ?_⟩
    · simpa only [List.forIn_cons, bind, StateT.bind, pure, StateT.pure,
        hp, hr, List.append_assoc, List.singleton_append] using generated
    · simp only [hp]
    · simp only [hp, hr]
    · simpa only [List.forIn_cons, bind, StateT.bind, pure, StateT.pure, hp, hr]
        using later.trans afterRows
    · intro branch member
      simp only [List.forIn_cons, bind, StateT.bind, pure, StateT.pure, hp, hr]
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨leftBound.mono afterRows, rightBound.mono afterRows⟩
      · exact rowBounds branch member

/-- The concrete dispatcher contains exactly the source rows in their
original order, with their own generated patterns and bodies. Its fuel and
argument binders are separate from the row-local allocations. -/
theorem dispatcher_rows (program : Program) (head : String) (first : Nat) :
    ∃ branches checked,
      (dispatcher program head first).1.2 =
        call "=" [call (dispatchName head)
          [.var (freshName first), .var (freshName (first + 1))],
          call "function" [call "chain"
            [.var (freshName (first + 1)), .var (freshName checked),
              selectBranches (.var (freshName checked)) branches
                (returned (.symbol "nik:Failure"))]]] ∧
      List.Forall₂ (fun row branch => EmittedCase program (.var (freshName first))
        row branch (first + 2))
        (compileHead program head) branches ∧ first + 2 ≤ checked ∧
      ∀ branch ∈ branches, UsesBefore checked branch.1 ∧ UsesBefore checked branch.2 := by
  let rows := compileHead program head
  let generated := (forIn rows ([] : List (Atom × Atom)) fun row branches => do
    let (left, names) ← patterns row.equation.params
    let right ← expression program names (.var (freshName first)) row.equation.body
    pure (ForInStep.yield (branches ++ [(left, right)])) : Emit (List (Atom × Atom))) (first + 2)
  obtain ⟨branches, same, related, afterRows, rowBounds⟩ :=
    row_loop_preserves program (.var (freshName first)) rows [] (first + 2) (by simp)
  change generated.1 = [] ++ branches at same
  simp only [List.nil_append] at same
  refine ⟨branches, generated.2, ?_, related, afterRows, rowBounds⟩
  change call "=" [call (dispatchName head)
    [.var (freshName first), .var (freshName (first + 1))],
    call "function" [call "chain"
      [.var (freshName (first + 1)), .var (freshName generated.2),
        selectBranches (.var (freshName generated.2)) generated.1
          (returned (.symbol "nik:Failure"))]]] = _
  rw [same]

private theorem substitute_scan (name : String) (replacement target otherwise : Atom)
    (branches : List (Atom × Atom)) :
    substituteName name replacement (selectBranches target branches otherwise) =
      selectBranches (substituteName name replacement target)
        (branches.map fun branch =>
          (substituteName name replacement branch.1, substituteName name replacement branch.2))
        (substituteName name replacement otherwise) := by
  induction branches with
  | nil => rfl
  | cons branch branches ih =>
    simpa only [selectBranches, List.foldr_cons, List.map_cons,
      substituteName_call, List.map_nil] using congrArg
        (fun rest => call "unify" [substituteName name replacement target,
          substituteName name replacement branch.1, substituteName name replacement branch.2,
          rest]) ih

private theorem input_before_local (index localIndex : Nat) (replacement : Atom)
    (before : index < localIndex) :
    substituteName (freshName index) replacement (.var (freshName localIndex)) =
      .var (freshName localIndex) := by
  have different : freshName localIndex ≠ freshName index := by
    intro same
    have equalIndex := freshName_injective same
    omega
  simp only [substituteName, different, if_false]

private theorem rows_substitute_input {program : Program} {fuel : Atom}
    {rows : List CaseRow} {branches : List (Atom × Atom)} {lower : Nat}
    (related : List.Forall₂ (fun row branch => EmittedCase program fuel row branch lower)
      rows branches) (index : Nat) (replacement : Atom) (before : index < lower)
    (fuelBound : UsesBefore lower fuel) :
    List.Forall₂ (fun row branch =>
      EmittedCase program (substituteName (freshName index) replacement fuel) row branch lower)
      rows (branches.map fun branch =>
        (substituteName (freshName index) replacement branch.1,
          substituteName (freshName index) replacement branch.2)) := by
  induction related with
  | nil => exact .nil
  | cons emitted _ ih =>
    apply List.Forall₂.cons _ ih
    simpa only [emitted.pattern_input_fixed index replacement before] using
      emitted.substitute_input index replacement before fuelBound

private theorem rows_substitute_scope (branches : List (Atom × Atom)) (bound : Nat)
    (boundedRows : ∀ branch ∈ branches, UsesBefore bound branch.1 ∧ UsesBefore bound branch.2)
    (name : String) (replacement : Atom) (replacementBound : UsesBefore bound replacement) :
    ∀ branch ∈ branches.map (fun branch =>
      (substituteName name replacement branch.1, substituteName name replacement branch.2)),
      UsesBefore bound branch.1 ∧ UsesBefore bound branch.2 := by
  intro branch member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact ⟨substitute_scope _ _ _ _ (boundedRows original originalMember).1 replacementBound,
    substitute_scope _ _ _ _ (boundedRows original originalMember).2 replacementBound⟩

/-- Filling the actual dispatcher's two header inputs yields precisely the
ordered row code compiled with the supplied fuel. The argument vector stays
inert data; it is passed to the generated scan without evaluating its terms.
This equality includes the complete emitted body, not only its header. -/
theorem dispatcher_filled_inputs (program : Program) (head : String) (first fuel : Nat)
    (arguments : List Term) :
    ∃ rawBody branches checked,
      (dispatcher program head first).1.2 =
        call "=" [call (dispatchName head)
          [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] ∧
      fillInputs [(first, .grounded (.int fuel)),
          (first + 1, MeTTaData.encodeItems arguments)] rawBody =
        call "chain" [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))] ∧
      List.Forall₂ (fun row branch => EmittedCase program (.grounded (.int fuel))
        row branch (first + 2)) (compileHead program head) branches ∧
      first + 2 ≤ checked ∧
      ∀ branch ∈ branches, UsesBefore checked branch.1 ∧ UsesBefore checked branch.2 := by
  obtain ⟨rawBranches, checked, emitted, aligned, afterRows, rowBounds⟩ :=
    dispatcher_rows program head first
  let filledFuel := rawBranches.map fun branch =>
    (substituteName (freshName first) (.grounded (.int fuel)) branch.1,
      substituteName (freshName first) (.grounded (.int fuel)) branch.2)
  let filledArguments := filledFuel.map fun branch =>
    (substituteName (freshName (first + 1)) (MeTTaData.encodeItems arguments) branch.1,
      substituteName (freshName (first + 1)) (MeTTaData.encodeItems arguments) branch.2)
  have fuelRelated : List.Forall₂ (fun row branch =>
      EmittedCase program (.grounded (.int fuel)) row branch (first + 2))
      (compileHead program head) filledFuel := by
    simpa only [substituteName, if_true] using
      rows_substitute_input aligned first (.grounded (.int fuel)) (by omega) (by simp)
  have argumentRelated : List.Forall₂ (fun row branch =>
      EmittedCase program (.grounded (.int fuel)) row branch (first + 2))
      (compileHead program head) filledArguments := by
    simpa only [substituteName] using
      rows_substitute_input fuelRelated (first + 1) (MeTTaData.encodeItems arguments)
        (by omega) (usesBefore_grounded _ _)
  have fuelBounds := rows_substitute_scope rawBranches checked rowBounds
    (freshName first) (.grounded (.int fuel)) (usesBefore_grounded _ _)
  have argumentBounds := rows_substitute_scope filledFuel checked fuelBounds
    (freshName (first + 1)) (MeTTaData.encodeItems arguments) (by
      intro name occurrence
      exact False.elim (data_has_no_variables (MeTTaData.encodeItems_data arguments) name occurrence))
  refine ⟨_, filledArguments, checked, emitted, ?_, argumentRelated, afterRows, argumentBounds⟩
  simp only [fillInputs, substituteName_call, List.map_cons, List.map_nil,
    input_before_local first (first + 1) (.grounded (.int fuel)) (by omega),
    input_before_local first checked (.grounded (.int fuel)) (by omega),
    substitute_scan, returned, substituteName, if_true,
    input_before_local (first + 1) checked (MeTTaData.encodeItems arguments) (by omega)]
  rfl

/-- Matching a dispatcher's two fresh header variables materializes exactly
the supplied fuel and argument vector throughout its body. Every other
body variable remains unassigned. This follows from the actual match/merge
machine and its key bounds, rather than assuming a substitution result. -/
theorem matched_header_materialization (head fuelName argumentName : String)
    (fuel : Nat) (arguments : List Term) (body : Metta.Atom)
    (incoming matched output : Metta.Bindings)
    (stored : ClosedValueBindings incoming) (invariant : LeaRuntimeBindingInvariant incoming)
    (different : fuelName ≠ argumentName)
    (privateBody : ∀ name ∈ body.vars, Metta.Bindings.lookupVal incoming name = none)
    (matching : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (call head [.var fuelName, .var argumentName]))
      (toLeaTTaAtom (call head [.grounded (.int fuel), MeTTaData.encodeItems arguments])))
    (merging : output ∈ Metta.Bindings.merge incoming matched) :
    ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      Metta.instantiate output body =
        Metta.Subst.apply [(fuelName, .gnd (.int fuel)),
          (argumentName, toLeaTTaAtom (MeTTaData.encodeItems arguments))] body := by
  let header := call head [.var fuelName, .var argumentName]
  let query := call head [.grounded (.int fuel), MeTTaData.encodeItems arguments]
  have closed : (toLeaTTaAtom query).vars = [] := by
    simp only [query, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil,
      data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)]
  have matchedClosed := matching_closed_side (toLeaTTaAtom header) (toLeaTTaAtom query)
    matched (.inr closed) matching
  have outputClosed := merge_closed_closed_mem stored matchedClosed merging
  have outputInvariant := invariant.merge_matchOutput
    (toLeaTTaAtom_noFloat header) (toLeaTTaAtom_noFloat query)
    matching merging outputClosed.hasLoop_false
  have inputs := (leaMerge_solution_iff (leaClassSolution output) invariant.noFloat
    (leaMatchAtoms_result_noFloat (toLeaTTaAtom_noFloat header)
      (toLeaTTaAtom_noFloat query) matching) merging).mp outputInvariant.canonical.1
  have equation := (leaMatchAtoms_solution_iff (leaClassSolution output)
    (toLeaTTaAtom_noFloat header) (toLeaTTaAtom_noFloat query) matching).mp inputs.2
  have values : leaClassSolution output fuelName = .gnd (.int fuel) ∧
      leaClassSolution output argumentName = toLeaTTaAtom (MeTTaData.encodeItems arguments) := by
    simpa only [header, query, call, MettaEquationSatisfied, toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround,
      applyClassSolution, List.map_cons, List.map_nil, Metta.Atom.expr.injEq,
      List.cons.injEq, true_and, and_true, encoded_items_solution_fixed] using equation
  refine ⟨outputClosed, outputInvariant, instantiate_eq_subst_on_variables output _ body ?_⟩
  intro name occurrence
  by_cases isFuel : name = fuelName
  · subst name
    rw [← applyClassSolution_lea_eq_instantiate]
    simpa only [applyClassSolution, Metta.Subst.apply, Metta.Subst.lookup,
      beq_self_eq_true, ↓reduceIte, Option.getD_some] using values.1
  · by_cases isArgument : name = argumentName
    · subst name
      rw [← applyClassSolution_lea_eq_instantiate]
      simpa only [applyClassSolution, Metta.Subst.apply, Metta.Subst.lookup,
        beq_eq_false_iff_ne.mpr different.symm, beq_self_eq_true, Bool.false_eq_true,
        ↓reduceIte, Option.getD_some] using values.2
    · have unassigned : Metta.Bindings.lookupVal output name = none := by
        apply outputClosed.toValueBindings.lookup_none_of_not_key
        intro key
        rcases merge_closed_closed_valueKeys_subset stored matchedClosed merging name key with old | new
        · obtain ⟨value, present⟩ := stored.toValueBindings.lookup_some_of_key_mem old
          simp only [privateBody name occurrence, reduceCtorEq] at present
        · have occurs := matching_closed_keys (toLeaTTaAtom header) (toLeaTTaAtom query)
            matched (.inr closed) matching name new
          simp only [header, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
            List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
            List.nil_append, List.append_nil, closed, List.singleton_append,
            List.mem_cons, List.not_mem_nil, isFuel, isArgument, or_self] at occurs
      simp only [Metta.instantiate, Metta.Bindings.resolveAtom,
        ClosedValueBindings.resolve_eq_lookupVal outputClosed, unassigned,
        Metta.Subst.apply, Metta.Subst.lookup, beq_eq_false_iff_ne.mpr isFuel,
        beq_eq_false_iff_ne.mpr isArgument, Bool.false_eq_true, ↓reduceIte, Option.getD_none]

/-- The actual emitted equation and the actual query freshener satisfy the
header/body materialization contract together. Only a successful runtime
match and merge are supplied; the compiled body, private names and input
substitution are all obtained from those implementations. -/
theorem dispatcher_query_materialization (program : Program) (head : String)
    (first fuel counter : Nat) (arguments : List Term) (previous : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let lhs := toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))])
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int fuel), MeTTaData.encodeItems arguments])
    ∃ rawBody branches checked, ∃ rename : String → String,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] ∧
      List.Forall₂ (fun row branch => EmittedCase program (.grounded (.int fuel))
        row branch (first + 2)) (compileHead program head) branches ∧
      first + 2 ≤ checked ∧
      (∀ branch ∈ branches, UsesBefore checked branch.1 ∧ UsesBefore checked branch.2) ∧
      Function.Injective rename ∧
      (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming)
        lhs (toLeaTTaAtom (call "function" [rawBody]))).1 =
          (renBy rename lhs, renBy rename (toLeaTTaAtom (call "function" [rawBody]))) ∧
      ∀ matched output,
        matched ∈ Metta.matchAtoms
          (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming)
            lhs (toLeaTTaAtom (call "function" [rawBody]))).1.1 query →
        output ∈ Metta.Bindings.merge incoming matched →
        ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
          Metta.instantiate output
            (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming)
              lhs (toLeaTTaAtom (call "function" [rawBody]))).1.2 =
            renBy rename (toLeaTTaAtom (call "function" [call "chain"
              [MeTTaData.encodeItems arguments, .var (freshName checked),
                selectBranches (.var (freshName checked)) branches
                  (returned (.symbol "nik:Failure"))]])) := by
  intro lhs query
  obtain ⟨rawBody, branches, checked, emitted, filled, aligned, afterRows, rowBounds⟩ :=
    dispatcher_filled_inputs program head first fuel arguments
  obtain ⟨rename, injective, freshened⟩ := freshenRuleAvoiding_renaming counter
    (Metta.Minimal.queryOpAvoid previous query incoming) lhs (toLeaTTaAtom (call "function" [rawBody]))
  refine ⟨rawBody, branches, checked, rename, emitted, aligned, afterRows, rowBounds,
    injective, freshened, ?_⟩
  intro matched output matching merging
  have different : rename (freshName first) ≠ rename (freshName (first + 1)) := by
    intro same
    have equalIndex := freshName_injective (injective same)
    omega
  have privateBody : ∀ name ∈ (renBy rename (toLeaTTaAtom rawBody)).vars,
      Metta.Bindings.lookupVal incoming name = none := by
    intro name member
    apply query_fresh_variables_unassigned counter previous query lhs
      (toLeaTTaAtom (call "function" [rawBody])) incoming stored name
    rw [freshened]
    apply List.mem_append_right
    simpa only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons,
      List.map_nil, Metta.Atom.vars, List.flatten_cons, List.flatten_nil,
      List.nil_append, List.append_nil] using member
  have headerMatch : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (call (dispatchName head)
        [.var (rename (freshName first)), .var (rename (freshName (first + 1)))])) query := by
    rw [freshened] at matching
    simpa only [lhs, call, toLeaTTaAtom, toLeaTTaAtoms, renBy,
      List.map_cons, List.map_nil] using matching
  obtain ⟨outputClosed, outputInvariant, materialized⟩ := matched_header_materialization
    (dispatchName head) (rename (freshName first)) (rename (freshName (first + 1)))
    fuel arguments (renBy rename (toLeaTTaAtom rawBody)) incoming matched output
    stored invariant different privateBody headerMatch merging
  have transport := fillInputs_runtime
    [(first, .grounded (.int fuel)), (first + 1, MeTTaData.encodeItems arguments)]
    rawBody rename injective (by
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · simp only [toLeaTTaAtom, Metta.Atom.vars]
      · rcases List.mem_singleton.mp member with rfl
        exact data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
  rw [filled] at transport
  have inner : Metta.instantiate output (renBy rename (toLeaTTaAtom rawBody)) =
      renBy rename (toLeaTTaAtom (call "chain"
        [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))])) := by
    rw [materialized]
    simpa only [List.map_cons, List.map_nil, toLeaTTaAtom, toLeaTTaGround] using transport
  refine ⟨outputClosed, outputInvariant, ?_⟩
  rw [freshened]
  simpa only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
    Metta.instantiate, Metta.Bindings.resolveAtom] using
    congrArg (fun body => Metta.Atom.expr [.sym "function", body]) inner

/-- The dispatcher's encoded argument vector is inert data. Its sequencing
prefix materializes that vector and substitutes it into the scan in three
actual driver steps, preserving the entire caller and work queue. -/
theorem encoded_arguments_chain_enters (arguments : List Term)
    (template : Metta.Atom) (name : String) (environment : MinEnv) (state : St)
    (bindings : Metta.Bindings) (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    let payload := toLeaTTaAtom (MeTTaData.encodeItems arguments)
    interpretFuel environment (fuel + 3) state
      (⟨atomToStack (.expr [.sym "chain", payload, .var name, template])
        (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (⟨atomToStack (Metta.Subst.apply [(name, payload)] template)
        (parent :: continuation), bindings⟩ :: rest) done := by
  intro payload
  let body := Metta.Atom.expr [.sym "chain", payload, .var name, template]
  let scope := chainFrameVars (parent :: continuation) payload template
  let caller : Frame := { atom := body, ret := .chain, vars := scope }
  let start : Item := ⟨{ atom := payload, vars := scope } :: caller :: parent :: continuation,
    bindings⟩
  let ready : Item := ⟨{ atom := payload, fin := true, vars := scope } ::
    caller :: parent :: continuation, bindings⟩
  let middle : Item := ⟨{ atom := body, ret := .chain, vars := scope } :: parent :: continuation,
    bindings⟩
  have closed : Metta.instantiate bindings payload = payload :=
    Metta.instantiate_of_closed bindings payload
      (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
  have initial : atomToStack body (parent :: continuation) = start.stack := by
    cases arguments <;> simp [body, payload, scope, caller, start, MeTTaData.encodeItems,
      toLeaTTaAtom, toLeaTTaAtoms, atomToStack, varsCopy]
  have firstStep (budget : Nat) : interpretStack1 environment budget state start =
      ([ready], state) := by
    cases arguments <;> simp [start, ready, payload, MeTTaData.encodeItems,
      toLeaTTaAtom, toLeaTTaAtoms, interpretStack1, isEmbeddedOp]
  have secondStep (budget : Nat) : interpretStack1 environment budget state ready =
      ([middle], state) := by
    simp only [ready, middle, caller, body, interpretStack1, closed, if_true]
  have thirdStep (budget : Nat) : interpretStack1 environment budget state middle =
      ([⟨atomToStack (Metta.Subst.apply [(name, payload)] template)
        (parent :: continuation), bindings⟩], state) := by
    exact step_chain_apply environment budget state (parent :: continuation) scope
      payload template name bindings
  change interpretFuel environment (fuel + 3) state
    (⟨atomToStack body (parent :: continuation), bindings⟩ :: rest) done = _
  rw [initial]
  rw [driver_singleton_step environment (fuel + 2) state state start ready rest done
    (firstStep _) (by rfl)]
  rw [driver_singleton_step environment (fuel + 1) state state ready middle rest done
    (secondStep _) (by rfl)]
  exact driver_singleton_step environment fuel state state middle _ rest done
    (thirdStep _) (atomToStack_pending _ _ _ _)

private theorem substitute_renamed_scan (arguments : List Term)
    (branches : List (Atom × Atom)) (checked : Nat) (rename : String → String)
    (injective : Function.Injective rename)
    (bounds : ∀ branch ∈ branches, UsesBefore checked branch.1 ∧ UsesBefore checked branch.2) :
    Metta.Subst.apply [(rename (freshName checked),
        toLeaTTaAtom (MeTTaData.encodeItems arguments))]
      (renBy rename (toLeaTTaAtom (selectBranches (.var (freshName checked)) branches
        (returned (.symbol "nik:Failure"))))) =
    renBy rename (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
      (returned (.symbol "nik:Failure")))) := by
  have closed := renBy_eq_self_of_vars_nil rename
    (toLeaTTaAtom (MeTTaData.encodeItems arguments))
    (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
  induction branches with
  | nil => simp [selectBranches, returned, call, toLeaTTaAtom, toLeaTTaAtoms,
      renBy, Metta.Subst.apply]
  | cons branch branches ih =>
    have leftSame := substitute_fresh (rename (freshName checked))
      (toLeaTTaAtom (MeTTaData.encodeItems arguments))
      (renBy rename (toLeaTTaAtom branch.1))
      ((bounds branch (by simp)).1.renamed_runtime_fresh rename injective)
    have rightSame := substitute_fresh (rename (freshName checked))
      (toLeaTTaAtom (MeTTaData.encodeItems arguments))
      (renBy rename (toLeaTTaAtom branch.2))
      ((bounds branch (by simp)).2.renamed_runtime_fresh rename injective)
    have tailSame := ih (fun entry member => bounds entry (List.mem_cons_of_mem _ member))
    simpa only [selectBranches, List.foldr_cons, call, toLeaTTaAtom, toLeaTTaAtoms,
      renBy, List.map_cons, List.map_nil, Metta.Subst.apply, Metta.Subst.lookup,
      beq_self_eq_true, if_true, Option.getD_some, leftSame, rightSame, closed] using
      congrArg (fun tail => Metta.Atom.expr [.sym "unify",
        toLeaTTaAtom (MeTTaData.encodeItems arguments),
        renBy rename (toLeaTTaAtom branch.1), renBy rename (toLeaTTaAtom branch.2), tail]) tailSame

/-- The argument-materialization prefix of an actually allocated dispatcher
enters its ordered scan. The allocation theorem supplies the only freshness
condition, including after the runtime's injective rule renaming. -/
theorem dispatcher_body_enters_scan (arguments : List Term)
    (branches : List (Atom × Atom)) (checked : Nat) (rename : String → String)
    (injective : Function.Injective rename)
    (bounds : ∀ branch ∈ branches, UsesBefore checked branch.1 ∧ UsesBefore checked branch.2)
    (environment : MinEnv) (state : St) (bindings : Metta.Bindings)
    (parent : Frame) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings)) :
    interpretFuel environment (fuel + 3) state
      (⟨atomToStack (renBy rename (toLeaTTaAtom (call "chain"
        [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))]))) (parent :: continuation), bindings⟩ :: rest) done =
    interpretFuel environment fuel state
      (⟨atomToStack (renBy rename (toLeaTTaAtom
        (selectBranches (MeTTaData.encodeItems arguments) branches
          (returned (.symbol "nik:Failure"))))) (parent :: continuation), bindings⟩ :: rest) done := by
  have renamedData := renBy_eq_self_of_vars_nil rename
    (toLeaTTaAtom (MeTTaData.encodeItems arguments))
    (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
  have shape : renBy rename (toLeaTTaAtom (call "chain"
      [MeTTaData.encodeItems arguments, .var (freshName checked),
        selectBranches (.var (freshName checked)) branches (returned (.symbol "nik:Failure"))])) =
      .expr [.sym "chain", renBy rename (toLeaTTaAtom (MeTTaData.encodeItems arguments)),
        .var (rename (freshName checked)), renBy rename (toLeaTTaAtom
          (selectBranches (.var (freshName checked)) branches (returned (.symbol "nik:Failure"))))] := by
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil]
  rw [shape, renamedData, encoded_arguments_chain_enters,
    substitute_renamed_scan arguments branches checked rename injective bounds]

/-- A query's materialized dispatcher remains materialized after its closed
argument vector is substituted into the scan. Thus the row selector needs
no additional assumption about unresolved caller bindings. -/
theorem dispatcher_scan_materialized (arguments : List Term)
    (branches : List (Atom × Atom)) (checked : Nat) (rename : String → String)
    (injective : Function.Injective rename)
    (bounds : ∀ branch ∈ branches, UsesBefore checked branch.1 ∧ UsesBefore checked branch.2)
    (bindings : Metta.Bindings) (stored : ClosedValueBindings bindings)
    (raw : Metta.Atom)
    (materialized : Metta.instantiate bindings raw =
      renBy rename (toLeaTTaAtom (call "function" [call "chain"
        [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))]]))) :
    Metta.instantiate bindings (renBy rename (toLeaTTaAtom
      (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure"))))) =
      renBy rename (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure")))) := by
  have stable := instantiate_closed_value_bindings_idempotent stored raw
  rw [materialized] at stable
  have templateFixed : Metta.instantiate bindings (renBy rename (toLeaTTaAtom
      (selectBranches (.var (freshName checked)) branches (returned (.symbol "nik:Failure"))))) =
      renBy rename (toLeaTTaAtom
        (selectBranches (.var (freshName checked)) branches (returned (.symbol "nik:Failure")))) := by
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
      Metta.instantiate, Metta.Bindings.resolveAtom, Metta.Atom.expr.injEq,
      List.cons.injEq, true_and, and_true] at stable
    exact stable.2.2
  have filled := instantiate_substitute_fixed bindings (rename (freshName checked))
    (toLeaTTaAtom (MeTTaData.encodeItems arguments)) _
    (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)) templateFixed
  rwa [substitute_renamed_scan arguments branches checked rename injective bounds] at filled

private theorem selected_prefix {β : Type} {R : CaseRow → β → Prop}
    {rows : List CaseRow} {branches : List β} (aligned : List.Forall₂ R rows branches)
    (arguments : List Term) (selectedRow : CaseRow) (sourceBindings : Env)
    (selected : selectCase rows arguments = some (selectedRow, sourceBindings)) :
    ∃ earlierRows branch suffix,
      branches = earlierRows ++ branch :: suffix ∧ R selectedRow branch ∧
      matchTerms selectedRow.equation.params arguments = some sourceBindings ∧
      ∀ earlier ∈ earlierRows, ∃ row, R row earlier ∧
        matchTerms row.equation.params arguments = none := by
  induction aligned with
  | nil => simp [selectCase] at selected
  | @cons row branch rows branches related aligned ih =>
    cases matched : matchTerms row.equation.params arguments with
    | none =>
      have later : selectCase rows arguments = some (selectedRow, sourceBindings) := by
        simpa only [selectCase, vector_match, matched] using selected
      obtain ⟨earlierRows, chosen, suffix, same, chosenRel, chosenMatch, refused⟩ := ih later
      refine ⟨branch :: earlierRows, chosen, suffix, by simp only [same, List.cons_append],
        chosenRel, chosenMatch, ?_⟩
      intro earlier member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨row, related, matched⟩
      · exact refused earlier member
    | some found =>
      have same : (row, found) = (selectedRow, sourceBindings) := by
        simpa only [selectCase, vector_match, matched, Option.some.injEq] using selected
      cases same
      exact ⟨[], branch, branches, rfl, related, matched, by simp⟩

/-- A refused prefix followed by a viable row executes the selected body
exactly once. The result is equality of complete driver runs, with no extra
successes or fallback path left in the work queue. -/
theorem selectBranches_first_match (target : Atom) (earlierRows suffix : List (Atom × Atom))
    (pattern body otherwise : Atom) (environment : MinEnv) (state : St)
    (incoming matched output : Metta.Bindings) (parentBody : Metta.Atom)
    (scope : List String) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (stored : ClosedValueBindings incoming)
    (closed : (toLeaTTaAtom target).vars = [])
    (fixed : Metta.instantiate incoming
      (toLeaTTaAtom (selectBranches target (earlierRows ++ (pattern, body) :: suffix) otherwise)) =
        toLeaTTaAtom (selectBranches target (earlierRows ++ (pattern, body) :: suffix) otherwise))
    (refused : ∀ row ∈ earlierRows, ¬∃ candidate merged,
      candidate ∈ Metta.matchAtoms (toLeaTTaAtom target) (toLeaTTaAtom row.1) ∧
      merged ∈ Metta.Bindings.merge incoming candidate ∧ merged.hasLoop = false)
    (matching : matched ∈ Metta.matchAtoms (toLeaTTaAtom target) (toLeaTTaAtom pattern))
    (merging : output ∈ Metta.Bindings.merge incoming matched) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    ClosedValueBindings output ∧
      interpretFuel environment (fuel + 2 + 2 * earlierRows.length) state
        (finItem (parent :: continuation)
          (toLeaTTaAtom (selectBranches target (earlierRows ++ (pattern, body) :: suffix) otherwise))
          incoming :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation)
          (Metta.instantiate output (toLeaTTaAtom body)) output :: rest) done := by
  intro parent
  have suffixFixed : Metta.instantiate incoming
      (toLeaTTaAtom (selectBranches target ((pattern, body) :: suffix) otherwise)) =
      toLeaTTaAtom (selectBranches target ((pattern, body) :: suffix) otherwise) := by
    clear refused
    induction earlierRows with
    | nil => exact fixed
    | cons row rows ih =>
      apply ih
      have parts := fixed
      simp only [selectBranches, List.cons_append, List.foldr_cons, call,
        toLeaTTaAtom, toLeaTTaAtoms, Metta.instantiate, Metta.Bindings.resolveAtom,
        List.map_cons, List.map_nil, Metta.Atom.expr.injEq, List.cons.injEq,
        true_and, and_true] at parts
      exact parts.2.2.2
  let fallback := selectBranches target suffix otherwise
  have parts :
      Metta.instantiate incoming (toLeaTTaAtom target) = toLeaTTaAtom target ∧
      Metta.instantiate incoming (toLeaTTaAtom pattern) = toLeaTTaAtom pattern ∧
      Metta.instantiate incoming (toLeaTTaAtom body) = toLeaTTaAtom body ∧
      Metta.instantiate incoming (toLeaTTaAtom fallback) = toLeaTTaAtom fallback := by
    simpa only [fallback, selectBranches, List.foldr_cons, call,
      toLeaTTaAtom, toLeaTTaAtoms, Metta.instantiate, Metta.Bindings.resolveAtom,
      List.map_cons, List.map_nil, Metta.Atom.expr.injEq, List.cons.injEq,
      true_and, and_true] using suffixFixed
  obtain ⟨outputClosed, selected⟩ := unify_closed_candidate (parent :: continuation)
    (toLeaTTaAtom target) (toLeaTTaAtom pattern) (toLeaTTaAtom body)
    (toLeaTTaAtom fallback) incoming matched output stored closed matching merging
  refine ⟨outputClosed, ?_⟩
  rw [selectBranches_refused_prefix target earlierRows ((pattern, body) :: suffix) otherwise
    environment state incoming parentBody scope continuation (fuel + 2) rest done fixed refused]
  change interpretFuel environment ((fuel + 1) + 1) state
    (finItem (parent :: continuation)
      (.expr [.sym "unify", toLeaTTaAtom target, toLeaTTaAtom pattern,
        toLeaTTaAtom body, toLeaTTaAtom fallback]) incoming :: rest) done = _
  rw [function_unify_enters, parts.1, parts.2.1, parts.2.2.1, parts.2.2.2]
  apply driver_singleton_step
  · simpa only [atomToStack, step_unify] using
      congrArg (fun items => (items, state)) selected
  · rfl

/-- The row-level syntax obligation after query freshening. It contains the
actual compiled body as well as its pattern; freshness concerns the incoming
frame, not a hypothesized execution result. -/
def FreshEmittedCase (program : Program) (sourceFuel : Atom) (rename : String → String)
    (incoming : Metta.Bindings)
    (row : CaseRow) (branch : Atom × Atom) : Prop :=
  ∃ first,
    AlphaRenameAtomRel rename (patterns row.equation.params first).1.1 branch.1 ∧
    AlphaRenameAtomRel rename
      (expression program (patterns row.equation.params first).1.2
        sourceFuel row.equation.body (patterns row.equation.params first).2).1 branch.2 ∧
    ∀ name, AtomOccurs (patterns row.equation.params first).1.1 name →
      rename name ∉ incoming.vars

/-- Freshening the two parts of an actually emitted row establishes its
runtime syntax obligation. This uses the emitter's row theorem directly. -/
theorem EmittedCase.fresh {program : Program} {sourceFuel : Atom} {row : CaseRow}
    {raw branch : Atom × Atom} (emitted : EmittedCase program sourceFuel row raw)
    {rename : String → String} {incoming : Metta.Bindings}
    (left : AlphaRenameAtomRel rename raw.1 branch.1)
    (right : AlphaRenameAtomRel rename raw.2 branch.2)
    (privateNames : ∀ name, AtomOccurs raw.1 name →
      rename name ∉ incoming.vars) :
    FreshEmittedCase program sourceFuel rename incoming row branch := by
  obtain ⟨first, _, patternCode, bodyCode⟩ := emitted
  exact ⟨first, patternCode ▸ left, bodyCode ▸ right, patternCode ▸ privateNames⟩

private theorem scan_pattern_occurs (target otherwise : Atom)
    {branches : List (Atom × Atom)} {branch : Atom × Atom} {name : String}
    (member : branch ∈ branches) (occurs : AtomOccurs branch.1 name) :
    AtomOccurs (selectBranches target branches otherwise) name := by
  induction branches with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact (occurs_call_iff _ _ _).mpr ⟨branch.1, by simp, occurs⟩
    · exact (occurs_call_iff _ _ _).mpr
        ⟨selectBranches target rest otherwise, by simp [selectBranches], ih later⟩

private theorem scan_body_occurs (target otherwise : Atom)
    {branches : List (Atom × Atom)} {branch : Atom × Atom} {name : String}
    (member : branch ∈ branches) (occurs : AtomOccurs branch.2 name) :
    AtomOccurs (selectBranches target branches otherwise) name := by
  induction branches with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact (occurs_call_iff _ _ _).mpr ⟨branch.2, by simp, occurs⟩
    · exact (occurs_call_iff _ _ _).mpr
        ⟨selectBranches target rest otherwise, by simp [selectBranches], ih later⟩

private theorem renamed_scan_code (arguments : List Term) (branches : List (Atom × Atom))
    (rename : String → String) :
    toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments)
      (branches.map fun branch => (renameTypeVars rename branch.1, renameTypeVars rename branch.2))
        (returned (.symbol "nik:Failure"))) =
    renBy rename (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
      (returned (.symbol "nik:Failure")))) := by
  have dataFixed := renBy_eq_self_of_vars_nil rename
    (toLeaTTaAtom (MeTTaData.encodeItems arguments))
    (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
  induction branches with
  | nil => simp [selectBranches, returned, call, toLeaTTaAtom, toLeaTTaAtoms, renBy]
  | cons branch branches ih =>
    simpa only [List.map_cons, selectBranches, List.foldr_cons, call,
      toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_nil, dataFixed,
      (renamed_atom_contract rename branch.1).2,
      (renamed_atom_contract rename branch.2).2] using
      congrArg (fun tail => Metta.Atom.expr [.sym "unify",
        toLeaTTaAtom (MeTTaData.encodeItems arguments),
        renBy rename (toLeaTTaAtom branch.1), renBy rename (toLeaTTaAtom branch.2), tail]) ih

/-- Actual materialization supplies the row freshness required by the
ordered selector. The only row data used here is the stateful emitter's
pattern/body correspondence; there is no assumed pattern-selection result. -/
theorem emitted_rows_after_materialization {program : Program} {sourceFuel : Atom}
    {rows : List CaseRow} {branches : List (Atom × Atom)} {lower : Nat}
    (aligned : List.Forall₂ (fun row branch => EmittedCase program sourceFuel row branch lower)
      rows branches) (arguments : List Term) (rename : String → String)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (fixed : Metta.instantiate incoming (renBy rename (toLeaTTaAtom
      (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure"))))) =
      renBy rename (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure"))))) :
    List.Forall₂ (FreshEmittedCase program sourceFuel rename incoming) rows
      (branches.map fun branch => (renameTypeVars rename branch.1, renameTypeVars rename branch.2)) := by
  have privateNames : ∀ branch ∈ branches, ∀ name, AtomOccurs branch.1 name →
      rename name ∉ incoming.vars := by
    intro branch member name occurs
    apply fixed_closed_bindings_private incoming stored _ fixed (rename name)
    rw [renBy_vars]
    exact List.mem_map.mpr ⟨name,
      Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp
        (scan_pattern_occurs _ _ member occurs), rfl⟩
  clear fixed
  induction aligned with
  | nil => exact .nil
  | @cons row branch rows branches emitted aligned ih =>
    exact .cons ((emitted.lower (Nat.zero_le lower)).fresh
      (renamed_atom_contract rename branch.1).1 (renamed_atom_contract rename branch.2).1
      (privateNames branch (by simp)))
      (ih (fun chosen member => privateNames chosen (List.mem_cons_of_mem _ member)))

theorem selectBranches_fixed_body (target otherwise : Atom)
    (branches : List (Atom × Atom)) (bindings : Metta.Bindings)
    (fixed : Metta.instantiate bindings (toLeaTTaAtom (selectBranches target branches otherwise)) =
      toLeaTTaAtom (selectBranches target branches otherwise)) :
    ∀ branch ∈ branches, Metta.instantiate bindings (toLeaTTaAtom branch.2) =
      toLeaTTaAtom branch.2 := by
  induction branches with
  | nil => simp
  | cons first rest ih =>
    simp only [selectBranches, List.foldr_cons, call, toLeaTTaAtom, toLeaTTaAtoms,
      Metta.instantiate, Metta.Bindings.resolveAtom, List.map_cons, List.map_nil,
      Metta.Atom.expr.injEq, List.cons.injEq, true_and, and_true] at fixed
    intro branch member
    rcases List.mem_cons.mp member with rfl | member
    · exact fixed.2.2.1
    · exact ih fixed.2.2.2 branch member


/-- The authored first-match selector chooses exactly the generated runtime
row. The complete refused prefix executes before its body is selected, and
the runtime's resulting valuation realizes the source substitution. Bodies
are retained syntactically here; their recursive execution is composed later. -/
theorem source_selection_execution (program : Program) (sourceFuel : Atom)
    (fuelData : MeTTaData.DataAtom sourceFuel)
    (rows : List CaseRow) (branches : List (Atom × Atom))
    (arguments : List Term) (row : CaseRow) (sourceBindings : Env)
    (rename : String → String) (injective : Function.Injective rename)
    (incoming : Metta.Bindings) (invariant : LeaRuntimeBindingInvariant incoming)
    (stored : ClosedValueBindings incoming)
    (aligned : List.Forall₂
      (FreshEmittedCase program sourceFuel rename incoming) rows branches)
    (selected : selectCase rows arguments = some (row, sourceBindings))
    (environment : MinEnv) (parentBody : Metta.Atom)
    (scope : List String) (continuation : Stack)
    (fixed : Metta.instantiate incoming
      (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure")))) =
      toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure")))) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    ∃ earlierRows branch laterRows first output,
      branches = earlierRows ++ branch :: laterRows ∧
      AlphaRenameAtomRel rename
        (expression program (patterns row.equation.params first).1.2
          sourceFuel row.equation.body (patterns row.equation.params first).2).1 branch.2 ∧
      ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      ValuationFor (leaClassSolution output ∘ rename) first sourceBindings ∧
      Metta.instantiate output (toLeaTTaAtom branch.2) = renBy rename (toLeaTTaAtom
        (expression program (sourceBindings.map (fun entry =>
          (entry.1, MeTTaData.encode entry.2))) sourceFuel row.equation.body
          (patterns row.equation.params first).2).1) ∧
      (∀ name, (∀ branch ∈ branches, name ∉ (toLeaTTaAtom branch.1).vars) →
        Metta.Bindings.lookupVal incoming name = none →
          Metta.Bindings.lookupVal output name = none) ∧
      ∀ state fuel rest done, interpretFuel environment (fuel + 1 + 2 * earlierRows.length) state
        (⟨atomToStack
          (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
            (returned (.symbol "nik:Failure")))) (parent :: continuation), incoming⟩ :: rest) done =
        interpretFuel environment fuel state
          (finItem (parent :: continuation)
            (Metta.instantiate output (toLeaTTaAtom branch.2)) output :: rest) done := by
  intro parent
  obtain ⟨earlierRows, branch, laterRows, layout, related, matchedSource, earlierRefused⟩ :=
    selected_prefix aligned arguments row sourceBindings selected
  obtain ⟨first, patternCode, bodyCode, privateNames⟩ := related
  obtain ⟨matched, output, matching, merging, acyclic⟩ :=
    (alpha_patterns_closed_runtime_match_iff row.equation.params arguments first invariant stored
      injective patternCode privateNames).mpr ⟨sourceBindings, matchedSource⟩
  have refused : ∀ earlier ∈ earlierRows, ¬∃ candidate merged,
      candidate ∈ Metta.matchAtoms (toLeaTTaAtom (MeTTaData.encodeItems arguments))
        (toLeaTTaAtom earlier.1) ∧
      merged ∈ Metta.Bindings.merge incoming candidate ∧ merged.hasLoop = false := by
    intro earlier member
    obtain ⟨previous, previousCode, unmatched⟩ := earlierRefused earlier member
    obtain ⟨start, pattern, _, privatePattern⟩ := previousCode
    rw [alpha_patterns_closed_runtime_match_iff previous.equation.params arguments start
      invariant stored injective pattern privatePattern]
    simp [unmatched]
  have outputClosed := merge_closed_closed_mem stored
    (matching_closed_input _ _ matched
      (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)) matching) merging
  obtain ⟨outputInvariant, actual, matchActual, valuation⟩ :=
    alpha_patterns_runtime_bindings row.equation.params arguments first invariant
      patternCode matching merging acyclic
  have same : actual = sourceBindings := Option.some.inj (matchActual.symm.trans matchedSource)
  subst actual
  have bodyFixed := selectBranches_fixed_body (MeTTaData.encodeItems arguments)
    (returned (.symbol "nik:Failure")) branches incoming fixed branch
      (by rw [layout]; simp)
  have translatedBody := alpha_runtime_shape bodyCode
  rw [translatedBody] at bodyFixed
  have materialized := matched_expression_materialization program row.equation.params arguments
    first sourceFuel fuelData sourceBindings row.equation.body matchedSource rename injective
    branch.1 patternCode incoming matched output stored bodyFixed valuation matching merging
  rw [← translatedBody] at materialized
  refine ⟨earlierRows, branch, laterRows, first, output, layout, bodyCode, outputClosed,
    outputInvariant, valuation, materialized, ?_, ?_⟩
  · intro name absent unassigned
    exact matching_closed_preserves_unassigned
      (toLeaTTaAtom (MeTTaData.encodeItems arguments)) (toLeaTTaAtom branch.1)
      incoming matched output name stored
      (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)) unassigned
      (absent branch (by rw [layout]; simp)) matching merging
  intro state fuel rest done
  obtain ⟨_, execution⟩ := selectBranches_first_match
    (MeTTaData.encodeItems arguments) earlierRows laterRows branch.1 branch.2
    (returned (.symbol "nik:Failure")) environment state incoming matched output
    parentBody scope continuation fuel rest done stored
    (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
    (layout ▸ fixed) refused matching merging
  have embedded : isEmbeddedOp (Metta.instantiate incoming
      (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure"))))) = true := by
    rw [fixed, layout]
    cases earlierRows <;> simp only [List.nil_append, List.cons_append,
      selectBranches, List.foldr_cons, call, toLeaTTaAtom, toLeaTTaAtoms, isEmbeddedOp] <;> rfl
  have enter := function_embedded_enters environment state incoming parentBody
    (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
      (returned (.symbol "nik:Failure")))) scope continuation
    (fuel + 1 + 2 * earlierRows.length) rest done embedded
  rw [fixed] at enter
  have completed := layout.symm ▸ execution
  exact enter.symm.trans (by
    simpa only [show fuel + 1 + 2 * earlierRows.length + 1 =
      fuel + 2 + 2 * earlierRows.length by omega] using completed)

/-- After the actual query match, an emitted dispatcher reaches exactly the
body selected by the source program. Query freshening, closed-input
materialization, argument sequencing and ordered matching are composed here;
no fresh-row or successful-selection hypothesis is added at the runtime.
The remaining body execution is deliberately visible in the conclusion. -/
theorem dispatcher_selected_execution (program : Program) (head : String)
    (first sourceFuel counter : Nat) (arguments : List Term)
    (row : CaseRow) (sourceBindings : Env)
    (selected : selectCase (compileHead program head) arguments = some (row, sourceBindings))
    (environment : MinEnv) (continuation : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let lhs := toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))])
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ rawBody, ∃ rename : String → String,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] ∧
      Function.Injective rename ∧
      ∀ matched merged,
        let fresh := (freshenRuleAvoiding counter
          (Metta.Minimal.queryOpAvoid continuation query incoming) lhs
          (toLeaTTaAtom (call "function" [rawBody]))).1
        matched ∈ Metta.matchAtoms fresh.1 query →
        merged ∈ Metta.Bindings.merge incoming matched →
        let function := Metta.instantiate merged fresh.2
        let parent : Frame := { atom := function, ret := .function, vars := varsCopy continuation }
        ∃ skipped start body output,
          AlphaRenameAtomRel rename
            (expression program (patterns row.equation.params start).1.2
              (.grounded (.int sourceFuel)) row.equation.body
              (patterns row.equation.params start).2).1 body ∧
          ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
          ValuationFor (leaClassSolution output ∘ rename) start sourceBindings ∧
          Metta.instantiate output (toLeaTTaAtom body) = renBy rename (toLeaTTaAtom
            (expression program (sourceBindings.map (fun entry =>
              (entry.1, MeTTaData.encode entry.2))) (.grounded (.int sourceFuel))
              row.equation.body (patterns row.equation.params start).2).1) ∧
          (∀ name ∈ liveStackVars continuation,
            Metta.Bindings.lookupVal incoming name = none →
              Metta.Bindings.lookupVal output name = none) ∧
          (∀ name ∈ (Metta.instantiate output (toLeaTTaAtom body)).vars,
            name ∉ liveStackVars continuation) ∧
          isFinal (evalResult continuation function merged) = false ∧
          ∀ state fuel rest done,
            interpretFuel environment (fuel + 4 + 2 * skipped) state
              (evalResult continuation function merged :: rest) done =
            interpretFuel environment fuel state
              (finItem (parent :: continuation)
                (Metta.instantiate output (toLeaTTaAtom body)) output :: rest) done := by
  intro lhs query
  obtain ⟨rawBody, branches, checked, rename, emitted, aligned, _, bounds,
      injective, _, materializes⟩ := dispatcher_query_materialization program head first
    sourceFuel counter arguments continuation incoming stored invariant
  refine ⟨rawBody, rename, emitted, injective, ?_⟩
  intro matched merged fresh matching merging function parent
  obtain ⟨mergedClosed, mergedInvariant, materialized⟩ :=
    materializes matched merged matching merging
  change Metta.instantiate merged fresh.2 = _ at materialized
  have fixed := dispatcher_scan_materialized arguments branches checked rename injective
    bounds merged mergedClosed fresh.2 materialized
  let renamedBranches := branches.map fun branch =>
    (renameTypeVars rename branch.1, renameTypeVars rename branch.2)
  have freshRows := emitted_rows_after_materialization aligned arguments rename merged mergedClosed fixed
  have renamedFixed : Metta.instantiate merged
      (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) renamedBranches
        (returned (.symbol "nik:Failure")))) =
      toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) renamedBranches
        (returned (.symbol "nik:Failure"))) := by
    rw [renamed_scan_code]
    exact fixed
  obtain ⟨earlier, branch, later, start, output, layout, bodyCode, outputClosed,
      outputInvariant, valuation, bodyMaterialized, scanPreserves, selectedExecution⟩ := source_selection_execution program
    (.grounded (.int sourceFuel)) (.grounded _) (compileHead program head) renamedBranches arguments row
    sourceBindings rename injective merged mergedInvariant mergedClosed freshRows selected
    environment function (varsCopy continuation) continuation renamedFixed
  have branchesPrivate (branch : Atom × Atom) (member : branch ∈ renamedBranches)
      (name : String) (occurs : name ∈ (toLeaTTaAtom branch.1).vars ++
        (toLeaTTaAtom branch.2).vars) : name ∉ liveStackVars continuation := by
    intro live
    have absent := materialized_query_excludes_caller counter continuation query lhs
      (toLeaTTaAtom (call "function" [rawBody])) incoming merged mergedClosed name live
    change name ∉ (Metta.instantiate merged fresh.2).vars at absent
    rw [materialized] at absent
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    simp only [(renamed_atom_contract rename original.1).2,
      (renamed_atom_contract rename original.2).2, renBy_vars] at occurs
    obtain ⟨originalName, occurrence, same⟩ :
        ∃ originalName, originalName ∈ (toLeaTTaAtom original.1).vars ++
          (toLeaTTaAtom original.2).vars ∧ rename originalName = name := by
      simpa only [← List.map_append, List.mem_map] using occurs
    have inScan : AtomOccurs (selectBranches (.var (freshName checked)) branches
        (returned (.symbol "nik:Failure"))) originalName := by
      rcases List.mem_append.mp occurrence with left | right
      · exact scan_pattern_occurs _ _ originalMember
          (Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mpr left)
      · exact scan_body_occurs _ _ originalMember
          (Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mpr right)
    have inChain : AtomOccurs (call "chain"
        [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))]) originalName :=
      (occurs_call_iff _ _ _).mpr ⟨_, by simp, inScan⟩
    apply absent
    rw [renBy_vars]
    exact List.mem_map.mpr ⟨originalName,
      Spec.Match.ModelTheory.atomOccurs_iff_mem_translated_vars.mp
        ((occurs_call_iff _ _ _).mpr ⟨_, by simp, inChain⟩), same⟩
  have branchMember : branch ∈ renamedBranches := by rw [layout]; simp
  have callerPreserved : ∀ name ∈ liveStackVars continuation,
      Metta.Bindings.lookupVal incoming name = none →
        Metta.Bindings.lookupVal output name = none := by
    intro name live unassigned
    apply scanPreserves name
    · intro chosen member occurrence
      exact branchesPrivate chosen member name (List.mem_append_left _ occurrence) live
    · exact query_preserves_unassigned_caller continuation query lhs
        (toLeaTTaAtom (call "function" [rawBody])) incoming matched merged counter name
        stored (by simp [query, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
          data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)])
        live unassigned matching merging
  have selectedPrivate : ∀ name ∈ (Metta.instantiate output (toLeaTTaAtom branch.2)).vars,
      name ∉ liveStackVars continuation := by
    intro name occurs
    exact branchesPrivate branch branchMember name (List.mem_append_right _
      (instantiate_closed_vars_subset output outputClosed _ name occurs))
  have startShape : evalResult continuation function merged =
      ⟨atomToStack (renBy rename (toLeaTTaAtom (call "chain"
        [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))]))) (parent :: continuation), merged⟩ := by
    simp only [function, parent, materialized, call, toLeaTTaAtom, toLeaTTaAtoms,
      renBy, List.map_cons, List.map_nil, evalResult, atomToStack]
  refine ⟨earlier.length, start, branch.2, output, bodyCode, outputClosed, outputInvariant,
    valuation, bodyMaterialized, callerPreserved, selectedPrivate, ?_, ?_⟩
  · rw [startShape]
    exact atomToStack_pending _ _ _ _
  intro state fuel rest done
  have execute := selectedExecution state fuel rest done
  rw [renamed_scan_code] at execute
  have prefixRun := dispatcher_body_enters_scan arguments branches checked rename injective bounds
    environment state merged parent continuation (fuel + 1 + 2 * earlier.length) rest done
  rw [startShape, show fuel + 4 + 2 * earlier.length =
    (fuel + 1 + 2 * earlier.length) + 3 by omega, prefixRun]
  exact execute

private theorem refused_rows {β : Type} {R : CaseRow → β → Prop}
    {rows : List CaseRow} {branches : List β} (aligned : List.Forall₂ R rows branches)
    (arguments : List Term) (refused : selectCase rows arguments = none) :
    ∀ branch ∈ branches, ∃ row, R row branch ∧
      matchTerms row.equation.params arguments = none := by
  induction aligned with
  | nil => simp
  | @cons row branch rows branches related aligned ih =>
    cases matched : matchTerms row.equation.params arguments with
    | some => simp [selectCase, vector_match, matched] at refused
    | none =>
      have tailRefused : selectCase rows arguments = none := by
        simpa only [selectCase, vector_match, matched] using refused
      intro chosen member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨row, related, matched⟩
      · exact ih tailRefused chosen member

/-- If no authored row matches, the complete runtime scan reaches a logical
failure return in its function handler. It does not evaluate any row body or ask the host to
invent an alternative rule. -/
theorem source_refusal_execution (program : Program) (sourceFuel : Atom)
    (rows : List CaseRow) (branches : List (Atom × Atom)) (arguments : List Term)
    (rename : String → String) (injective : Function.Injective rename)
    (incoming : Metta.Bindings) (invariant : LeaRuntimeBindingInvariant incoming)
    (stored : ClosedValueBindings incoming)
    (aligned : List.Forall₂
      (FreshEmittedCase program sourceFuel rename incoming) rows branches)
    (refused : selectCase rows arguments = none)
    (environment : MinEnv) (state : St) (parentBody : Metta.Atom)
    (scope : List String) (continuation : Stack) (fuel : Nat)
    (rest : List Item) (done : List (Metta.Atom × Metta.Bindings))
    (fixed : Metta.instantiate incoming
      (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure")))) =
      toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
        (returned (.symbol "nik:Failure")))) :
    let parent : Frame := { atom := parentBody, ret := .function, vars := scope }
    interpretFuel environment (fuel + if branches = [] then 1 else 2 * branches.length - 1) state
        (⟨atomToStack
          (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) branches
            (returned (.symbol "nik:Failure")))) (parent :: continuation), incoming⟩ :: rest) done =
      interpretFuel environment fuel state
        (finItem (parent :: continuation) (.expr [.sym "return", .sym "nik:Failure"]) incoming :: rest) done := by
  intro parent
  have none : ∀ branch ∈ branches, ¬∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom (MeTTaData.encodeItems arguments))
        (toLeaTTaAtom branch.1) ∧
      merged ∈ Metta.Bindings.merge incoming matched ∧ merged.hasLoop = false := by
    intro branch member
    obtain ⟨row, related, noMatch⟩ := refused_rows aligned arguments refused branch member
    obtain ⟨first, patternCode, _, privateNames⟩ := related
    rw [alpha_patterns_closed_runtime_match_iff row.equation.params arguments first invariant stored
      injective patternCode privateNames]
    simp [noMatch]
  have scan := selectBranches_refused_prefix (MeTTaData.encodeItems arguments)
    branches [] (returned (.symbol "nik:Failure")) environment state incoming
    parentBody scope continuation fuel rest done
    (by simpa only [List.append_nil] using fixed) none
  simp only [List.append_nil, selectBranches, List.foldr_nil] at scan
  cases branches with
  | nil =>
    simpa only [if_pos rfl, if_true, selectBranches, List.foldr_nil, returned, call,
      toLeaTTaAtom, toLeaTTaAtoms, Metta.instantiate, Metta.Bindings.resolveAtom] using
      return_enters_handler environment state incoming parentBody (.sym "nik:Failure")
        scope continuation fuel rest done
  | cons branch branches =>
    have embedded : isEmbeddedOp (Metta.instantiate incoming
        (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) (branch :: branches)
          (returned (.symbol "nik:Failure"))))) = true := by
      rw [fixed]
      simp only [selectBranches, List.foldr_cons, call, toLeaTTaAtom, toLeaTTaAtoms,
        isEmbeddedOp]
      rfl
    have enter := function_embedded_enters environment state incoming parentBody
      (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) (branch :: branches)
        (returned (.symbol "nik:Failure")))) scope continuation
      (fuel + (2 * (branch :: branches).length - 1)) rest done embedded
    rw [fixed] at enter
    simpa only [List.cons_ne_nil, if_false] using enter.symm.trans (by
      simpa only [selectBranches, returned, call, toLeaTTaAtom, toLeaTTaAtoms,
        show fuel + (2 * (branch :: branches).length - 1) + 1 =
          fuel + 2 * (branch :: branches).length by simp only [List.length_cons]; omega] using scan)

/-- A dispatcher with no matching source row reaches a logical refusal in
its function handler after a fixed number of administrative steps. This covers
empty and nonempty refused scans on both public and nested stacks. -/
theorem dispatcher_refused_execution (program : Program) (head : String)
    (first sourceFuel counter : Nat) (arguments : List Term)
    (refused : selectCase (compileHead program head) arguments = none)
    (environment : MinEnv) (previous : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming) :
    let lhs := toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))])
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ rawBody,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] ∧
      ∀ matched merged,
        let fresh := (freshenRuleAvoiding counter
          (Metta.Minimal.queryOpAvoid previous query incoming) lhs
          (toLeaTTaAtom (call "function" [rawBody]))).1
        matched ∈ Metta.matchAtoms fresh.1 query →
        merged ∈ Metta.Bindings.merge incoming matched →
        ∃ cost, ∀ state fuel rest done,
          interpretFuel environment (fuel + cost) state
            (evalResult previous (Metta.instantiate merged fresh.2) merged :: rest) done =
          interpretFuel environment fuel state
            (finItem ({ atom := Metta.instantiate merged fresh.2, ret := .function, vars := varsCopy previous } :: previous)
              (.expr [.sym "return", .sym "nik:Failure"]) merged :: rest) done := by
  intro lhs query
  obtain ⟨rawBody, branches, checked, rename, emitted, aligned, _, bounds,
      injective, _, materializes⟩ := dispatcher_query_materialization program head first
    sourceFuel counter arguments previous incoming stored invariant
  refine ⟨rawBody, emitted, ?_⟩
  intro matched merged fresh matching merging
  obtain ⟨mergedClosed, mergedInvariant, materialized⟩ :=
    materializes matched merged matching merging
  change Metta.instantiate merged fresh.2 = _ at materialized
  let function := Metta.instantiate merged fresh.2
  let parent : Frame := { atom := function, ret := .function, vars := varsCopy previous }
  have fixed := dispatcher_scan_materialized arguments branches checked rename injective
    bounds merged mergedClosed fresh.2 materialized
  let renamedBranches := branches.map fun branch =>
    (renameTypeVars rename branch.1, renameTypeVars rename branch.2)
  have freshRows := emitted_rows_after_materialization aligned arguments rename merged mergedClosed fixed
  have renamedFixed : Metta.instantiate merged
      (toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) renamedBranches
        (returned (.symbol "nik:Failure")))) =
      toLeaTTaAtom (selectBranches (MeTTaData.encodeItems arguments) renamedBranches
        (returned (.symbol "nik:Failure"))) := by
    rw [renamed_scan_code]
    exact fixed
  let scanCost := if renamedBranches = [] then 1 else 2 * renamedBranches.length - 1
  refine ⟨scanCost + 3, ?_⟩
  intro state fuel rest done
  have execute := source_refusal_execution program (.grounded (.int sourceFuel))
    (compileHead program head) renamedBranches arguments rename injective merged mergedInvariant
    mergedClosed freshRows refused environment state function (varsCopy previous) previous
    fuel rest done renamedFixed
  rw [renamed_scan_code] at execute
  have prefixRun := dispatcher_body_enters_scan arguments branches checked rename injective bounds
    environment state merged parent previous (fuel + scanCost) rest done
  have startShape : evalResult previous function merged =
      ⟨atomToStack (renBy rename (toLeaTTaAtom (call "chain"
        [MeTTaData.encodeItems arguments, .var (freshName checked),
          selectBranches (.var (freshName checked)) branches
            (returned (.symbol "nik:Failure"))]))) (parent :: previous), merged⟩ := by
    simp only [function, parent, materialized, call, toLeaTTaAtom, toLeaTTaAtoms,
      renBy, List.map_cons, List.map_nil, evalResult, atomToStack]
  change interpretFuel environment (fuel + (scanCost + 3)) state
    (evalResult previous function merged :: rest) done = _
  rw [startShape, ← Nat.add_assoc, prefixRun]
  exact execute

/-- The emitted dispatcher opens a real function frame, even at the public
entry point. It cannot be collected before its rule scan executes. -/
theorem dispatcher_instantiated_pending (program : Program) (head : String) (first counter : Nat)
    (rawBody : Atom)
    (emitted : (dispatcher program head first).1.2 = call "="
      [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
        call "function" [rawBody]])
    (previous : Stack) (query : Metta.Atom) (incoming output : Metta.Bindings) :
    let lhs := toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))])
    let fresh := freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming)
      lhs (toLeaTTaAtom (call "function" [rawBody]))
    isFinal (evalResult previous (Metta.instantiate output fresh.1.2) output) = false := by
  intro lhs fresh
  obtain ⟨branches, checked, shape, _⟩ := dispatcher_rows program head first
  have body : rawBody = call "chain" [.var (freshName (first + 1)), .var (freshName checked),
      selectBranches (.var (freshName checked)) branches (returned (.symbol "nik:Failure"))] := by
    simpa only [call, Atom.expression.injEq, List.cons.injEq, true_and, and_true]
      using emitted.symm.trans shape
  obtain ⟨rename, _, renamed⟩ := freshenRuleAvoiding_renaming counter
    (Metta.Minimal.queryOpAvoid previous query incoming) lhs (toLeaTTaAtom (call "function" [rawBody]))
  change isFinal (evalResult previous (Metta.instantiate output
    (freshenRuleAvoiding counter (Metta.Minimal.queryOpAvoid previous query incoming)
      lhs (toLeaTTaAtom (call "function" [rawBody]))).1.2) output) = false
  rw [renamed, body]
  simp only [call, toLeaTTaAtom, toLeaTTaAtoms, renBy, List.map_cons, List.map_nil,
    Metta.instantiate, Metta.Bindings.resolveAtom, evalResult, atomToStack]
  exact atomToStack_pending _ _ _ _

/-- Querying the loaded equation constructs its fresh header bindings and
enters the generated function. Selection and refusal share this entry. -/
theorem loaded_dispatcher_entry (program : Program) (head : String) (first sourceFuel : Nat)
    (arguments : List Term) (rawBody : Atom)
    (emitted : (dispatcher program head first).1.2 = call "="
      [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
        call "function" [rawBody]])
    (environment : MinEnv) (state : St) (previous : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (nativeMiss : Metta.callGrounded environment.gt (dispatchName head)
      ([toLeaTTaAtom (.grounded (.int sourceFuel)),
        toLeaTTaAtom (MeTTaData.encodeItems arguments)].map
          (fun atom => resolveStates state.world (subTokens state.world atom))) = .noReduce)
    (notEmbedded : isEmbeddedOp (toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) = false)
    (loaded : candidatesW environment state.world (toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) =
      [(toLeaTTaAtom (call (dispatchName head)
          [.var (freshName first), .var (freshName (first + 1))]),
        toLeaTTaAtom (call "function" [rawBody]))]) :
    let lhs := toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))])
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    let fresh := freshenRuleAvoiding state.counter
      (Metta.Minimal.queryOpAvoid previous query incoming) lhs
      (toLeaTTaAtom (call "function" [rawBody]))
    ∃ matched output, matched ∈ Metta.matchAtoms fresh.1.1 query ∧
      output ∈ Metta.Bindings.merge incoming matched ∧ ClosedValueBindings output ∧
      ∀ fuel rest done,
        interpretFuel environment (fuel + 1) state
          (⟨atomToStack (.expr [.sym "eval", query]) previous, incoming⟩ :: rest) done =
        interpretFuel environment fuel { state with counter := fresh.2 }
          (evalResult previous (Metta.instantiate output fresh.1.2) output :: rest) done := by
  intro lhs query fresh
  have distinct : freshName (first + 1) ≠ freshName first := by
    intro same
    have equalIndex := freshName_injective same
    omega
  obtain ⟨matched, output, matching, merging, outputClosed⟩ := query_two_input_header
    (dispatchName head) (freshName first) (freshName (first + 1)) (.gnd (.int sourceFuel))
    (toLeaTTaAtom (MeTTaData.encodeItems arguments)) (toLeaTTaAtom (call "function" [rawBody]))
    distinct (by simp [Metta.Atom.vars])
    (data_atom_runtime_closed (MeTTaData.encodeItems_data arguments))
    state.counter previous incoming stored
  refine ⟨matched, output, matching, merging, outputClosed, ?_⟩
  intro fuel rest done
  have queryClosed : query.vars = [] := by
    simp only [query, call, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars,
      List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil, data_atom_runtime_closed (MeTTaData.encodeItems_data arguments)]
  obtain ⟨_, queried⟩ := query_single_rule environment state previous query lhs
    (toLeaTTaAtom (call "function" [rawBody])) incoming matched output loaded
    (by simp [query, call, toLeaTTaAtom, toLeaTTaAtoms, isVariableHeaded])
    stored queryClosed matching merging
  apply driver_singleton_step
  · have entryShape : atomToStack (.expr [.sym "eval", query]) previous =
        { atom := .expr [.sym "eval", query], vars := varsCopy previous } :: previous := by
      simp [query, call, toLeaTTaAtom, toLeaTTaAtoms, atomToStack]
    have native := nativeMiss
    simp only [toLeaTTaAtom] at native
    have ordinary := notEmbedded
    simp only [call, toLeaTTaAtom, toLeaTTaAtoms] at ordinary
    rw [entryShape, step_eval, evalOp, Metta.instantiate_of_closed incoming _ queryClosed]
    simpa only [query, fresh, call, toLeaTTaAtom, toLeaTTaAtoms, native, ordinary,
      Bool.false_eq_true, if_false] using queried
  · exact dispatcher_instantiated_pending program head first state.counter rawBody emitted
      previous query incoming output

/-- A loaded emitted dispatcher executes the actual `eval` query and reaches
the source-selected body. Match and merge witnesses are constructed from
closed inputs. The environment premises specify only the loaded equation
and absence of a conflicting native or embedded instruction. -/
theorem loaded_dispatcher_selection (program : Program) (head : String)
    (first sourceFuel : Nat) (arguments : List Term) (row : CaseRow) (sourceBindings : Env)
    (selected : selectCase (compileHead program head) arguments = some (row, sourceBindings))
    (environment : MinEnv) (state : St) (previous : Stack)
    (incoming : Metta.Bindings) (stored : ClosedValueBindings incoming)
    (invariant : LeaRuntimeBindingInvariant incoming)
    (nativeMiss : Metta.callGrounded environment.gt (dispatchName head)
      ([toLeaTTaAtom (.grounded (.int sourceFuel)),
        toLeaTTaAtom (MeTTaData.encodeItems arguments)].map
          (fun atom => resolveStates state.world (subTokens state.world atom))) = .noReduce)
    (notEmbedded : isEmbeddedOp (toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) = false)
    (loaded : ∀ rawBody,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] →
      candidatesW environment state.world (toLeaTTaAtom (call (dispatchName head)
        [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])) =
      [(toLeaTTaAtom (call (dispatchName head)
          [.var (freshName first), .var (freshName (first + 1))]),
        toLeaTTaAtom (call "function" [rawBody]))]) :
    let lhs := toLeaTTaAtom (call (dispatchName head)
      [.var (freshName first), .var (freshName (first + 1))])
    let query := toLeaTTaAtom (call (dispatchName head)
      [.grounded (.int sourceFuel), MeTTaData.encodeItems arguments])
    ∃ rawBody, ∃ rename : String → String, ∃ headerBindings output skipped start body,
      (dispatcher program head first).1.2 = call "="
        [call (dispatchName head) [.var (freshName first), .var (freshName (first + 1))],
          call "function" [rawBody]] ∧
      Function.Injective rename ∧
      AlphaRenameAtomRel rename
        (expression program (patterns row.equation.params start).1.2
          (.grounded (.int sourceFuel)) row.equation.body
          (patterns row.equation.params start).2).1 body ∧
      ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      ValuationFor (leaClassSolution output ∘ rename) start sourceBindings ∧
      Metta.instantiate output (toLeaTTaAtom body) = renBy rename (toLeaTTaAtom
        (expression program (sourceBindings.map (fun entry =>
          (entry.1, MeTTaData.encode entry.2))) (.grounded (.int sourceFuel))
          row.equation.body (patterns row.equation.params start).2).1) ∧
      (∀ name ∈ liveStackVars previous,
        Metta.Bindings.lookupVal incoming name = none →
          Metta.Bindings.lookupVal output name = none) ∧
      (∀ name ∈ (Metta.instantiate output (toLeaTTaAtom body)).vars,
        name ∉ liveStackVars previous) ∧
      let fresh := freshenRuleAvoiding state.counter
        (Metta.Minimal.queryOpAvoid previous query incoming) lhs
        (toLeaTTaAtom (call "function" [rawBody]))
      let function := Metta.instantiate headerBindings fresh.1.2
      let parent : Frame := { atom := function, ret := .function, vars := varsCopy previous }
      ∀ fuel rest done,
        interpretFuel environment (fuel + 5 + 2 * skipped) state
          (⟨atomToStack (.expr [.sym "eval", query]) previous, incoming⟩ :: rest) done =
        interpretFuel environment fuel { state with counter := fresh.2 }
          (finItem (parent :: previous) (Metta.instantiate output (toLeaTTaAtom body)) output :: rest) done := by
  intro lhs query
  obtain ⟨rawBody, rename, emitted, injective, executes⟩ := dispatcher_selected_execution
    program head first sourceFuel state.counter arguments row sourceBindings selected
    environment previous incoming stored invariant
  obtain ⟨matched, headerBindings, matching, merging, _, queryEntry⟩ :=
    loaded_dispatcher_entry program head first sourceFuel arguments rawBody emitted
      environment state previous incoming stored nativeMiss notEmbedded (loaded rawBody emitted)
  obtain ⟨skipped, start, body, output, bodyCode, outputClosed, outputInvariant,
    valuation, bodyMaterialized, callerPreserved, bodyPrivate, _, bodyExecution⟩ := executes matched headerBindings matching merging
  refine ⟨rawBody, rename, headerBindings, output, skipped, start, body, emitted, injective,
    bodyCode, outputClosed, outputInvariant, valuation, bodyMaterialized,
    callerPreserved, bodyPrivate, ?_⟩
  intro fresh function parent fuel rest done
  rw [show fuel + 5 + 2 * skipped = (fuel + 4 + 2 * skipped) + 1 by omega,
    queryEntry (fuel + 4 + 2 * skipped) rest done]
  exact bodyExecution _ fuel rest done

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
