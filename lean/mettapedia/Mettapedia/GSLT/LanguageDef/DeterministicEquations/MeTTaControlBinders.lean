import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaDataBindings

/-!
# Fresh control binders through equation selection

The target's observation of a selected body is not itself a syntactic
substitution. Local control binders must remain variables. A name private to
the matched inputs remains unconstrained in every output binding theory;
varying its value distinguishes its syntax from a data-valued alias.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
open MeTTaData

/-- Match and merge add exactly the matched equation to the incoming theory. -/
theorem candidate_solution_iff {target pattern : Atom} {incoming output : Bindings}
    (candidate : UnifyCandidateRel target pattern incoming output)
    (valuation : String → Metta.Atom) :
    HEBindingSatisfied valuation output ↔
      HEBindingSatisfied valuation incoming ∧ HEAtomEquationSatisfied valuation target pattern := by
  obtain ⟨matched, matching, merged, _, _⟩ := candidate
  rw [Spec.Match.SolutionTheory.mergeRel_solution_iff merged valuation,
    Spec.Match.SolutionTheory.matchRel_solution_iff matching valuation]
  exact and_comm

/-- A name outside both matched inputs and the incoming frame stays free in
the output theory. No particular representation of that theory is required. -/
theorem candidate_free_update {target pattern : Atom} {incoming output : Bindings}
    (candidate : UnifyCandidateRel target pattern incoming output)
    (name : String) (privateName : ¬QueryVisibleName [pattern] target incoming name)
    (valuation : String → Metta.Atom) (satisfied : HEBindingSatisfied valuation output)
    (replacement : Metta.Atom) :
    HEBindingSatisfied (Function.update valuation name replacement) output := by
  have inputs := (candidate_solution_iff candidate valuation).mp satisfied
  have agrees : ∀ other, QueryVisibleName [pattern] target incoming other →
      Function.update valuation name replacement other = valuation other := by
    intro other visible
    have different : other ≠ name := by
      rintro rfl
      exact privateName visible
    exact Function.update_of_ne different replacement valuation
  have patternSame : applyClassSolution (Function.update valuation name replacement)
      (toLeaTTaAtom pattern) = applyClassSolution valuation (toLeaTTaAtom pattern) := by
    apply applyClassSolution_congr_on_atom_vars
    intro other occurrence
    exact agrees other (.inr (.inl ⟨pattern, by simp,
      atomOccurs_of_mem_translated_vars occurrence⟩))
  refine (candidate_solution_iff candidate _).mpr
    ⟨query_visible_preserves_model agrees inputs.1, ?_⟩
  change applyClassSolution _ (toLeaTTaAtom target) = applyClassSolution _ (toLeaTTaAtom pattern)
  rw [query_visible_solution agrees, patternSame]
  exact inputs.2

/-- An unconstrained name cannot be observed as a non-variable atom, or as
another name whose value is data. -/
theorem binder_shape_of_observation {output : Bindings}
    (valuation : String → Metta.Atom)
    (data : ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom)
    (name : String)
    (free : ∀ replacement, HEBindingSatisfied (Function.update valuation name replacement) output)
    (emitted : Atom)
    (observed : ∀ model, HEBindingSatisfied model output →
      HEAtomEquationSatisfied model emitted (.var name)) :
    emitted = .var name := by
  have same := observed (Function.update valuation name (.var name)) (free (.var name))
  simp only [HEAtomEquationSatisfied, toLeaTTaAtom, applyClassSolution,
    Function.update_self] at same
  cases emitted with
  | symbol | grounded | expression =>
      simp only [toLeaTTaAtom, applyClassSolution] at same
      contradiction
  | var other =>
      by_cases equalName : other = name
      · exact congrArg Atom.var equalName
      · obtain ⟨atom, atomData, assigned⟩ := data other
        have atomIsVariable : toLeaTTaAtom atom = .var name := by
          simpa only [toLeaTTaAtom, applyClassSolution,
            Function.update_of_ne equalName, assigned] using same
        cases atomData <;> simp only [toLeaTTaAtom] at atomIsVariable <;> contradiction

/-- The freshness obligation is discharged against the actual matching
inputs, rather than assumed as a property of the emitted code. -/
theorem candidate_binder_shape {target pattern : Atom} {incoming output : Bindings}
    (candidate : UnifyCandidateRel target pattern incoming output)
    (valuation : String → Metta.Atom) (satisfied : HEBindingSatisfied valuation output)
    (data : ∀ name, ∃ atom, DataAtom atom ∧ valuation name = toLeaTTaAtom atom)
    (name : String) (privateName : ¬QueryVisibleName [pattern] target incoming name)
    (emitted : Atom)
    (observed : ∀ model, HEBindingSatisfied model output →
      HEAtomEquationSatisfied model emitted (.var name)) :
    emitted = .var name :=
  binder_shape_of_observation valuation data name
    (candidate_free_update candidate name privateName valuation satisfied) emitted observed

/-- In particular, selection cannot replace a fresh `chain` binder by data. -/
theorem selected_chain_binder {target pattern source template emitted : Atom}
    {incoming output : Bindings} (name : String)
    (privateName : ¬QueryVisibleName [pattern] target incoming name)
    (valuation : String → Metta.Atom) (satisfied : HEBindingSatisfied valuation output)
    (data : ∀ other, ∃ atom, DataAtom atom ∧ valuation other = toLeaTTaAtom atom)
    (selected : UnifySuccessRel target pattern (call "chain" [source, .var name, template])
      incoming emitted output) :
    ∃ actualSource actualTemplate,
      emitted = call "chain" [actualSource, .var name, actualTemplate] ∧
      ∀ model, HEBindingSatisfied model output →
        HEAtomEquationSatisfied model actualSource source ∧
        HEAtomEquationSatisfied model actualTemplate template := by
  obtain ⟨items, shape, observations⟩ :=
    control_shape_of_model ⟨valuation, satisfied, data⟩ (by simp [dataSymbols])
      [source, .var name, template] emitted selected.2
  have length : items.length = 3 := by
    have same := congrArg List.length (observations valuation satisfied)
    simpa only [List.length_map, toLeaTTaAtoms, List.length_cons, List.length_nil,
      solutionTheory_toLeaTTaAtoms_eq_map] using same
  obtain ⟨actualSource, actualBinder, actualTemplate, rfl⟩ :
      ∃ a b c, items = [a, b, c] := by
    cases items with
    | nil => simp at length
    | cons first rest =>
        cases rest with
        | nil => simp at length
        | cons second tail =>
            cases tail with
            | nil => simp at length
            | cons third extra =>
                have empty : extra = [] := by simpa using length
                exact ⟨first, second, third, by rw [empty]⟩
  have parts : ∀ model, HEBindingSatisfied model output →
      HEAtomEquationSatisfied model actualSource source ∧
      HEAtomEquationSatisfied model actualBinder (.var name) ∧
      HEAtomEquationSatisfied model actualTemplate template := by
    intro model modelSatisfied
    simpa only [HEAtomEquationSatisfied, toLeaTTaAtoms, List.map_cons, List.map_nil,
      List.cons.injEq, and_true] using observations model modelSatisfied
  have binder := candidate_binder_shape selected.1 valuation satisfied data name privateName
    actualBinder (fun model modelSatisfied => (parts model modelSatisfied).2.1)
  refine ⟨actualSource, actualTemplate, ?_, ?_⟩
  · simpa only [binder] using shape
  · intro model modelSatisfied
    exact ⟨(parts model modelSatisfied).1, (parts model modelSatisfied).2.2⟩

/-- Without freshness, actual selection may identify a binder with data.
The instruction head is preserved, but the binder is no longer a variable. -/
theorem captured_chain_binder_counterexample :
    ∃ output, UnifySuccessRel (.symbol "nik:Nil") (.var "slot")
      (call "chain" [.symbol "nik:Nil", .var "slot", returned (.symbol "nik:Nil")])
      Bindings.empty
      (call "chain" [.symbol "nik:Nil", .symbol "nik:Nil", returned (.symbol "nik:Nil")])
      output := by
  obtain ⟨output, candidate⟩ :=
    (unify_empty_iff_model (.symbol "nik:Nil") (.var "slot")).mpr
      ⟨fun _ => .sym "nik:Nil", by
        simp only [HEAtomEquationSatisfied, toLeaTTaAtom, applyClassSolution]⟩
  refine ⟨output, candidate, ?_⟩
  intro valuation satisfied
  have same := ((candidate_solution_iff candidate valuation).mp satisfied).2
  have assigned : valuation "slot" = .sym "nik:Nil" := by
    simpa only [HEAtomEquationSatisfied, toLeaTTaAtom, applyClassSolution] using same.symm
  simp [HEAtomEquationSatisfied, call, returned, toLeaTTaAtom, toLeaTTaAtoms,
    applyClassSolution, assigned]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control
