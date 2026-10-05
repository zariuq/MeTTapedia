import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaFuelExecution
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalControlUnify

/-!
# Generated patterns in the executable matcher

The independent pattern semantics and LeaTTa's match/merge machine agree on
which generated branches are viable. The incoming frame carries the existing
paired binding invariant; rule variables are fresh for that entire frame.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
open Mettapedia.Languages.MeTTa.HE.CanonAbsorbsFreshening
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)

/-- The existing structural renamer supplies both the declarative alpha
relation and the actual runtime spelling. No fresh-pattern oracle is needed. -/
theorem renamed_atom_contract (rename : String → String) (atom : Atom) :
    AlphaRenameAtomRel rename atom (renameTypeVars rename atom) ∧
      toLeaTTaAtom (renameTypeVars rename atom) = renBy rename (toLeaTTaAtom atom) := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
    AlphaRenameAtomsRel rename atoms (atoms.map (renameTypeVars rename)) ∧
      toLeaTTaAtoms (atoms.map (renameTypeVars rename)) =
        (toLeaTTaAtoms atoms).map (renBy rename)) with
  | symbol name =>
    simp only [renameTypeVars]
    exact ⟨.symbol name, by simp only [toLeaTTaAtom, renBy]⟩
  | var name =>
    simp only [renameTypeVars]
    exact ⟨.variable name, by simp only [toLeaTTaAtom, renBy]⟩
  | grounded value =>
    simp only [renameTypeVars]
    exact ⟨.grounded value, by simp only [toLeaTTaAtom, renBy]⟩
  | expression atoms ih =>
    simp only [renameTypeVars]
    refine ⟨.expression ih.1, ?_⟩
    simpa only [toLeaTTaAtom, renBy] using (congrArg Metta.Atom.expr ih.2)
  | nil => exact ⟨.nil, rfl⟩
  | cons atom atoms ihAtom ihAtoms =>
    exact ⟨.cons ihAtom.1 ihAtoms.1, by
      simpa only [List.map_cons, toLeaTTaAtoms] using congrArg₂ List.cons ihAtom.2 ihAtoms.2⟩

theorem alpha_runtime_shape {rename : String → String} {source target : Atom}
    (renamed : AlphaRenameAtomRel rename source target) :
    toLeaTTaAtom target = renBy rename (toLeaTTaAtom source) := by
  induction renamed using AlphaRenameAtomRel.rec
      (motive_2 := fun source target _ => toLeaTTaAtoms target =
        (toLeaTTaAtoms source).map (renBy rename)) with
  | symbol | «variable» | grounded => simp only [toLeaTTaAtom, renBy]
  | expression _ ih =>
    simpa only [toLeaTTaAtom, renBy] using congrArg Metta.Atom.expr ih
  | nil => rfl
  | cons _ _ head tail =>
    simpa only [toLeaTTaAtoms, List.map_cons] using congrArg₂ List.cons head tail


private theorem runtime_match_iff_solution (target pattern : Atom)
    {runtime : Metta.Bindings} (invariant : LeaRuntimeBindingInvariant runtime)
    (disjoint : VarsDisjoint target pattern) :
    (∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom target) (toLeaTTaAtom pattern) ∧
      merged ∈ Metta.Bindings.merge runtime matched ∧ merged.hasLoop = false) ↔
      ∃ valuation, HEAtomEquationSatisfied valuation target pattern ∧
        LeaBindingSatisfied valuation runtime := by
  constructor
  · rintro ⟨matched, merged, matchedHere, mergedHere, acyclic⟩
    have outputInvariant := invariant.merge_matchOutput
      (toLeaTTaAtom_noFloat target) (toLeaTTaAtom_noFloat pattern)
      matchedHere mergedHere acyclic
    let valuation := leaClassSolution merged
    have matchedNoFloat := leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat target) (toLeaTTaAtom_noFloat pattern) matchedHere
    have inputs := (leaMerge_solution_iff valuation invariant.noFloat
      matchedNoFloat mergedHere).mp outputInvariant.canonical.1
    exact ⟨valuation,
      (leaMatchAtoms_solution_iff valuation (toLeaTTaAtom_noFloat target)
        (toLeaTTaAtom_noFloat pattern) matchedHere).mp inputs.2, inputs.1⟩
  · rintro ⟨valuation, same, incomingSatisfied⟩
    obtain ⟨specMatched, matchProof, matchedSatisfied⟩ :=
      Spec.Match.Completeness.exists_specMatch_of_solution same.symm
    obtain ⟨matched, matchedHere, matchedTheory⟩ :=
      specMatch_observational_complete_of_satisfiable matchProof disjoint.symm
        ⟨valuation, same.symm⟩
    have matchedNoFloat := leaMatchAtoms_result_noFloat
      (toLeaTTaAtom_noFloat target) (toLeaTTaAtom_noFloat pattern) matchedHere
    obtain ⟨merged, mergedHere, satisfied, _⟩ :=
      LeaTTaMergeExistence.merge_exists_of_satisfied invariant.noFloat matchedNoFloat
        incomingSatisfied ((matchedTheory valuation).mp matchedSatisfied)
    exact ⟨matched, merged, matchedHere, mergedHere,
      leaBindings_hasLoop_false_of_satisfied satisfied
        (leaMerge_result_assignmentsNonVariable invariant.assignmentsNonVariable mergedHere)
        (leaMerge_result_equalitiesIrreflexive invariant.equalitiesIrreflexive mergedHere)⟩

private theorem runtime_match_iff_model (target pattern : Atom)
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (disjoint : VarsDisjoint target pattern) :
    (∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom target) (toLeaTTaAtom pattern) ∧
      merged ∈ Metta.Bindings.merge runtime matched ∧ merged.hasLoop = false) ↔
      ∃ valuation, HEAtomEquationSatisfied valuation target pattern ∧
        HEBindingSatisfied valuation spec := by
  rw [runtime_match_iff_solution target pattern invariant.runtime disjoint]
  apply exists_congr
  intro valuation
  exact and_congr Iff.rfl (invariant.solutionTheory valuation).symm

/-- Closed runtime bindings suffice for a fresh pattern check. All freshness
is stated against the actual runtime's variable domain; a separate spec
binding record need not be carried through generated function calls. -/
theorem alpha_patterns_closed_runtime_match_iff (source values : List Term) (first : Nat)
    {runtime : Metta.Bindings} {rename : String → String} {fresh : Atom}
    (invariant : LeaRuntimeBindingInvariant runtime) (stored : ClosedValueBindings runtime)
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      rename name ∉ runtime.vars) :
    (∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom (MeTTaData.encodeItems values))
        (toLeaTTaAtom fresh) ∧
      merged ∈ Metta.Bindings.merge runtime matched ∧ merged.hasLoop = false) ↔
      ∃ environment, matchTerms source values = some environment := by
  have disjoint : VarsDisjoint (MeTTaData.encodeItems values) fresh := by
    intro name member
    simp only [data_atom_runtime_closed (MeTTaData.encodeItems_data values), List.not_mem_nil]
      at member
  rw [runtime_match_iff_solution _ _ invariant disjoint]
  constructor
  · rintro ⟨valuation, same, _⟩
    apply (patterns_equation_has_model_iff source values first).mp
    exact ⟨valuation ∘ rename, by simpa only [HEAtomEquationSatisfied,
      encoded_items_solution_fixed, alpha_solution renamed valuation] using same⟩
  · intro matched
    obtain ⟨sourceModel, same⟩ :=
      (patterns_equation_has_model_iff source values first).mpr matched
    let live := runtime.vars.map Atom.var
    have privateSpec : ∀ name, AtomOccurs (patterns source first).1.1 name →
        ¬QueryVisibleName live (MeTTaData.encodeItems values) Bindings.empty (rename name) := by
      intro name occurs visible
      rcases visible with query | liveName | assigned | payload | equal
      · exact data_has_no_variables (MeTTaData.encodeItems_data values) _ query
      · obtain ⟨atom, member, occursHere⟩ := liveName
        obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
        cases occursHere
        exact privateNames name occurs originalMember
      · simp [Bindings.empty] at assigned
      · simp [Bindings.empty] at payload
      · simp [Bindings.empty] at equal
    obtain ⟨extended, patternValue, _, agrees⟩ := alpha_extend_model injective renamed
      privateSpec sourceModel (leaClassSolution runtime) (by simp [HEBindingSatisfied, Bindings.empty])
    have retained : LeaBindingSatisfied extended runtime := by
      have keys : ∀ name ∈ runtime.vars, extended name = leaClassSolution runtime name := by
        intro name member
        exact agrees name (.inr (.inl ⟨.var name, List.mem_map.mpr ⟨name, member, rfl⟩,
          .var name⟩))
      constructor
      · intro name value member
        have closed : value.vars = [] := stored.val_mem_closed member
        have key : name ∈ runtime.vars := by
          simp only [Metta.Bindings.vars, List.mem_eraseDups, List.mem_flatMap]
          exact ⟨.val name value, member, by simp⟩
        rw [keys name key]
        exact (invariant.canonical.1.1 name value member).trans
          (applyClassSolution_congr_on_atom_vars value (by simp [closed]))
      · intro left right member
        have noEqual : ∀ {bindings : Metta.Bindings}, ValueBindings bindings →
            ∀ left right, Metta.BindingRel.eq left right ∉ bindings := by
          intro bindings onlyValues
          induction onlyValues with
          | nil => simp
          | val _ ih => simpa using ih
        exact False.elim (noEqual stored.toValueBindings left right member)
    exact ⟨extended, by simpa only [HEAtomEquationSatisfied, encoded_items_solution_fixed,
      patternValue] using same, retained⟩

/-- The actual matcher and merger select a fresh generated pattern exactly
when the source argument vector matches. The incoming frame's satisfiability
is established by its runtime invariant, not supplied as an extra premise. -/
theorem alpha_patterns_runtime_match_iff (source values : List Term) (first : Nat)
    {live : List Atom} {spec : Bindings} {runtime : Metta.Bindings}
    {rename : String → String} {fresh : Atom}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      ¬QueryVisibleName live (MeTTaData.encodeItems values) spec (rename name)) :
    (∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom (MeTTaData.encodeItems values))
        (toLeaTTaAtom fresh) ∧
      merged ∈ Metta.Bindings.merge runtime matched ∧ merged.hasLoop = false) ↔
      ∃ environment, matchTerms source values = some environment := by
  have disjoint : VarsDisjoint (MeTTaData.encodeItems values) fresh := by
    intro name member
    simp only [data_atom_runtime_closed (MeTTaData.encodeItems_data values), List.not_mem_nil]
      at member
  rw [runtime_match_iff_model _ _ invariant disjoint,
    ← unify_iff_common_model _ _ _ invariant.specAssignmentsNonVariable]
  exact alpha_patterns_unify_iff source values first injective renamed privateNames
    invariant.specAssignmentsNonVariable
    ⟨leaClassSolution runtime, (invariant.solutionTheory _).mpr invariant.runtime.canonical.1⟩

/-- Every surviving runtime match gives the source bindings when read by the
runtime's own resolver. This establishes actual materialization of the guest
operands, rather than only equality under an unspecified model. -/
theorem alpha_patterns_runtime_bindings (source values : List Term) (first : Nat)
    {incoming matched output : Metta.Bindings}
    {rename : String → String} {fresh : Atom}
    (invariant : LeaRuntimeBindingInvariant incoming)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (matchedHere : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (MeTTaData.encodeItems values)) (toLeaTTaAtom fresh))
    (mergedHere : output ∈ Metta.Bindings.merge incoming matched)
    (acyclic : output.hasLoop = false) :
    LeaRuntimeBindingInvariant output ∧
      ∃ environment, matchTerms source values = some environment ∧
        ValuationFor (leaClassSolution output ∘ rename) first environment := by
  have outputInvariant := invariant.merge_matchOutput
    (toLeaTTaAtom_noFloat (MeTTaData.encodeItems values)) (toLeaTTaAtom_noFloat fresh)
    matchedHere mergedHere acyclic
  refine ⟨outputInvariant, ?_⟩
  let valuation := leaClassSolution output
  have matchedNoFloat := leaMatchAtoms_result_noFloat
    (toLeaTTaAtom_noFloat (MeTTaData.encodeItems values)) (toLeaTTaAtom_noFloat fresh) matchedHere
  have inputs := (leaMerge_solution_iff valuation invariant.noFloat
    matchedNoFloat mergedHere).mp outputInvariant.canonical.1
  have same := (leaMatchAtoms_solution_iff valuation
    (toLeaTTaAtom_noFloat (MeTTaData.encodeItems values)) (toLeaTTaAtom_noFloat fresh)
    matchedHere).mp inputs.2
  apply patterns_solution_reflects source values first (valuation ∘ rename)
  simpa only [MettaEquationSatisfied, encoded_items_solution_fixed,
    alpha_solution renamed valuation] using same.symm

private theorem valuationFor_name_lookup (valuation : String → Metta.Atom)
    (bindings : Env) (first : Nat) (aligned : ValuationFor valuation first bindings)
    (name : String) :
    ((namesForMatch first bindings).find? (fun entry => entry.1 == name)).map
        (fun entry => applyClassSolution valuation (toLeaTTaAtom entry.2)) =
      (bindings.lookup name).map (fun term => toLeaTTaAtom (MeTTaData.encode term)) := by
  induction bindings generalizing first with
  | nil => rfl
  | cons entry remaining ih =>
    rw [namesForMatch_cons]
    by_cases same : entry.1 = name
    · simpa [List.find?, Env.lookup, same, toLeaTTaAtom, applyClassSolution]
        using congrArg some aligned.1
    · have different : (entry.1 == name) = false := by simp [same]
      simpa [List.find?, Env.lookup, different] using ih (first + 1) aligned.2

/-- Reading a variable through the compiler's actual name table materializes
its source value. Freshening changes only the target spelling, including when
the source environment contains repeated variable names. -/
theorem alpha_patterns_runtime_lookup (source values : List Term) (first : Nat)
    {spec : Bindings} {incoming matched output : Metta.Bindings}
    {rename : String → String} {fresh : Atom} {bindings : Env}
    (invariant : LeaQueryOpBindingInvariant spec incoming)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (sourceMatch : matchTerms source values = some bindings)
    (matchedHere : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (MeTTaData.encodeItems values)) (toLeaTTaAtom fresh))
    (mergedHere : output ∈ Metta.Bindings.merge incoming matched)
    (acyclic : output.hasLoop = false)
    (name label target : String) (payload : Term)
    (found : (patterns source first).1.2.find? (fun entry => entry.1 == name) =
      some (label, .var target))
    (expected : bindings.lookup name = some payload) :
    Metta.instantiate output (.var (rename target)) =
      toLeaTTaAtom (MeTTaData.encode payload) := by
  obtain ⟨_, environment, matchedSource, aligned⟩ :=
    alpha_patterns_runtime_bindings source values first invariant.runtime renamed matchedHere mergedHere acyclic
  have same : environment = bindings := Option.some.inj (matchedSource.symm.trans sourceMatch)
  subst environment
  have lookup := valuationFor_name_lookup (leaClassSolution output ∘ rename) bindings first aligned name
  rw [← patterns_names_of_match source values bindings sourceMatch first, found, expected] at lookup
  simp only [Option.map_some, Option.some.injEq, toLeaTTaAtom, applyClassSolution,
    Function.comp_apply] at lookup
  rw [← applyClassSolution_lea_eq_instantiate]
  simpa only [applyClassSolution] using lookup

/-- A successful generated pattern takes exactly one runtime step into the
selected body, with the source match and materialized input valuation exposed.
There are no additional successors hidden by an existential execution claim. -/
theorem alpha_patterns_success_execution (source values : List Term) (first : Nat)
    {spec : Bindings} {incoming matched output : Metta.Bindings}
    {rename : String → String} {fresh : Atom}
    (invariant : LeaQueryOpBindingInvariant spec incoming)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (matchedHere : matched ∈ Metta.matchAtoms
      (toLeaTTaAtom (MeTTaData.encodeItems values)) (toLeaTTaAtom fresh))
    (mergedHere : output ∈ Metta.Bindings.merge incoming matched)
    (stored : ClosedValueBindings incoming)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (yes no : Metta.Atom) (parent : Metta.Minimal.Frame)
    (continuation : Metta.Minimal.Stack) (fuel : Nat)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings)) :
    ClosedValueBindings output ∧ LeaRuntimeBindingInvariant output ∧
      ∃ bindings, matchTerms source values = some bindings ∧
        ValuationFor (leaClassSolution output ∘ rename) first bindings ∧
        Metta.Minimal.interpretFuel environment (fuel + 1) state
          (⟨Metta.Minimal.atomToStack (.expr [.sym "unify",
            toLeaTTaAtom (MeTTaData.encodeItems values), toLeaTTaAtom fresh, yes, no])
            (parent :: continuation), incoming⟩ :: rest) done =
          Metta.Minimal.interpretFuel environment fuel state
            (Metta.Minimal.finItem (parent :: continuation)
              (Metta.instantiate output yes) output :: rest) done := by
  obtain ⟨outputClosed, selected⟩ :=
    LeaTTaMinimalControlExecution.unify_closed_candidate (parent :: continuation)
      _ _ yes no incoming matched output stored
      (data_atom_runtime_closed (MeTTaData.encodeItems_data values)) matchedHere mergedHere
  obtain ⟨outputInvariant, bindings, sourceMatch, valuesAligned⟩ :=
    alpha_patterns_runtime_bindings source values first invariant.runtime renamed matchedHere mergedHere outputClosed.hasLoop_false
  refine ⟨outputClosed, outputInvariant, bindings, sourceMatch, valuesAligned, ?_⟩
  apply LeaTTaMinimalControlExecution.driver_singleton_step
  · simpa only [Metta.Minimal.atomToStack, LeaTTaMinimalControlExecution.step_unify] using
      congrArg (fun items => (items, state)) selected
  · rfl

/-- If a source vector fails to match, the emitted branch takes exactly the
fallback. No binding from a rejected partial match reaches the continuation. -/
theorem alpha_patterns_runtime_refusal (source values : List Term) (first : Nat)
    {live : List Atom} {spec : Bindings} {runtime : Metta.Bindings}
    {rename : String → String} {fresh : Atom}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      ¬QueryVisibleName live (MeTTaData.encodeItems values) spec (rename name))
    (refused : matchTerms source values = none)
    (previous : Metta.Minimal.Stack) (yes no : Metta.Atom) :
    Metta.Minimal.unifyOp previous (toLeaTTaAtom (MeTTaData.encodeItems values))
        (toLeaTTaAtom fresh) yes no runtime =
      [Metta.Minimal.finItem previous no runtime] := by
  have noCandidate : ¬∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom (MeTTaData.encodeItems values))
        (toLeaTTaAtom fresh) ∧
      merged ∈ Metta.Bindings.merge runtime matched ∧ merged.hasLoop = false := by
    rw [alpha_patterns_runtime_match_iff source values first invariant injective renamed privateNames]
    simp [refused]
  exact LeaTTaMinimalControlExecution.unify_no_candidate previous _ _ yes no runtime noCandidate

/-- A viable source row commits the real runtime to its body. Later rows
cannot affect the run, including when that body returns logical refusal. -/
theorem alpha_patterns_viable_execution (source values : List Term) (first : Nat)
    {live : List Atom} {spec : Bindings} {runtime : Metta.Bindings}
    {rename : String → String} {fresh : Atom}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      ¬QueryVisibleName live (MeTTaData.encodeItems values) spec (rename name))
    (matched : ∃ bindings, matchTerms source values = some bindings)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (yes firstFallback secondFallback : Metta.Atom) (continuation : Metta.Minimal.Stack)
    (fuel : Nat) (rest : List Metta.Minimal.Item)
    (done : List (Metta.Atom × Metta.Bindings)) :
    Metta.Minimal.interpretFuel environment (fuel + 1) state
        (⟨Metta.Minimal.atomToStack (.expr [.sym "unify",
          toLeaTTaAtom (MeTTaData.encodeItems values), toLeaTTaAtom fresh,
          yes, firstFallback]) continuation, runtime⟩ :: rest) done =
      Metta.Minimal.interpretFuel environment (fuel + 1) state
        (⟨Metta.Minimal.atomToStack (.expr [.sym "unify",
          toLeaTTaAtom (MeTTaData.encodeItems values), toLeaTTaAtom fresh,
          yes, secondFallback]) continuation, runtime⟩ :: rest) done := by
  exact LeaTTaMinimalControlExecution.unify_viable_execution environment state runtime
    _ _ yes firstFallback secondFallback continuation fuel rest done
    ((alpha_patterns_runtime_match_iff source values first invariant injective renamed
      privateNames).mpr matched)

/-- The real driver skips a refused prefix in source order. It preserves
the entire incoming frame, state and pending work; only the selected suffix
can subsequently run. The fixed-point premise describes already materialized
syntax, as produced by the function handler. -/
theorem selectBranches_refused_prefix (target : Atom)
    (earlier suffix : List (Atom × Atom)) (otherwise : Atom)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (bindings : Metta.Bindings) (parentBody : Metta.Atom) (scope : List String)
    (continuation : Metta.Minimal.Stack) (fuel : Nat)
    (rest : List Metta.Minimal.Item) (done : List (Metta.Atom × Metta.Bindings))
    (fixed : Metta.instantiate bindings
      (toLeaTTaAtom (selectBranches target (earlier ++ suffix) otherwise)) =
        toLeaTTaAtom (selectBranches target (earlier ++ suffix) otherwise))
    (refused : ∀ row ∈ earlier, ¬∃ matched merged,
      matched ∈ Metta.matchAtoms (toLeaTTaAtom target) (toLeaTTaAtom row.1) ∧
      merged ∈ Metta.Bindings.merge bindings matched ∧ merged.hasLoop = false) :
    let parent : Metta.Minimal.Frame :=
      { atom := parentBody, ret := .function, vars := scope }
    Metta.Minimal.interpretFuel environment (fuel + 2 * earlier.length) state
        (Metta.Minimal.finItem (parent :: continuation)
          (toLeaTTaAtom (selectBranches target (earlier ++ suffix) otherwise)) bindings :: rest)
        done =
      Metta.Minimal.interpretFuel environment fuel state
        (Metta.Minimal.finItem (parent :: continuation)
          (toLeaTTaAtom (selectBranches target suffix otherwise)) bindings :: rest) done := by
  intro parent
  revert fixed refused
  induction earlier with
  | nil => intro _ _; rfl
  | cons row rows ih =>
    rcases row with ⟨pattern, body⟩
    intro fixed refused
    let next := selectBranches target (rows ++ suffix) otherwise
    have parts :
        Metta.instantiate bindings (toLeaTTaAtom target) = toLeaTTaAtom target ∧
        Metta.instantiate bindings (toLeaTTaAtom pattern) = toLeaTTaAtom pattern ∧
        Metta.instantiate bindings (toLeaTTaAtom body) = toLeaTTaAtom body ∧
        Metta.instantiate bindings (toLeaTTaAtom next) = toLeaTTaAtom next := by
      simpa only [next, selectBranches, List.cons_append, List.foldr_cons, call,
        toLeaTTaAtom, toLeaTTaAtoms, Metta.instantiate, Metta.Bindings.resolveAtom,
        List.map_cons, List.map_nil, Metta.Atom.expr.injEq, List.cons.injEq,
        true_and, and_true] using fixed
    have budget : fuel + 2 * (rows.length + 1) = (fuel + 2 * rows.length + 1) + 1 := by omega
    change Metta.Minimal.interpretFuel environment (fuel + 2 * (rows.length + 1)) state
      (Metta.Minimal.finItem (parent :: continuation)
        (.expr [.sym "unify", toLeaTTaAtom target, toLeaTTaAtom pattern,
          toLeaTTaAtom body, toLeaTTaAtom next]) bindings :: rest) done = _
    rw [budget, LeaTTaMinimalControlExecution.function_unify_enters,
      parts.1, parts.2.1, parts.2.2.1, parts.2.2.2,
      LeaTTaMinimalControlExecution.unify_no_candidate_selects environment state bindings
        _ _ _ _ parent continuation (fuel + 2 * rows.length) rest done
        (refused (pattern, body) (by simp))]
    exact ih parts.2.2.2 (fun row member => refused row (by simp [member]))

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
