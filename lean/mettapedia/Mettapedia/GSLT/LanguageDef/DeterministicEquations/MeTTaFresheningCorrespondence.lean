import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaPatternSemantics
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-!
# Fresh equation instances preserve computational matching

The target evaluator freshens both sides of an equation before matching.
Its complete visible-name condition includes assignment values and equality
aliases. A lawful fresh instance extends every incoming model without
changing its visible values. The laws below use that existing condition and
the independent target match/merge relations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings Space)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

mutual

/-- Simultaneous structural renaming pulls a valuation back along its name map. -/
theorem alpha_solution {rename : String → String} {source target : Atom}
    (renamed : AlphaRenameAtomRel rename source target)
    (valuation : String → Metta.Atom) :
    applyClassSolution valuation (toLeaTTaAtom target) =
      applyClassSolution (valuation ∘ rename) (toLeaTTaAtom source) := by
  cases renamed with
  | symbol | «variable» | grounded =>
      simp only [toLeaTTaAtom, applyClassSolution, Function.comp_apply]
  | expression items =>
      simp only [toLeaTTaAtom, applyClassSolution, Metta.Atom.expr.injEq]
      exact alpha_solutions items valuation
termination_by sizeOf source

theorem alpha_solutions {rename : String → String} {source target : List Atom}
    (renamed : AlphaRenameAtomsRel rename source target)
    (valuation : String → Metta.Atom) :
    (toLeaTTaAtoms target).map (applyClassSolution valuation) =
      (toLeaTTaAtoms source).map (applyClassSolution (valuation ∘ rename)) := by
  cases renamed with
  | nil => rfl
  | cons head tail =>
      simp only [toLeaTTaAtoms, List.map_cons]
      rw [alpha_solution head valuation, alpha_solutions tail valuation]
termination_by sizeOf source

end

/-- Preserving all names visible to the query preserves the incoming theory.
Assignment keys alone would miss both value dependencies and equality aliases. -/
theorem query_visible_preserves_model {live : List Atom} {query : Atom}
    {incoming : Bindings} {base extended : String → Metta.Atom}
    (agrees : ∀ name, QueryVisibleName live query incoming name →
      extended name = base name)
    (satisfied : HEBindingSatisfied base incoming) :
    HEBindingSatisfied extended incoming := by
  constructor
  · intro name value member
    rw [agrees name (Or.inr (Or.inr (Or.inl ⟨value, member⟩)))]
    rw [satisfied.1 name value member]
    symm
    apply applyClassSolution_congr_on_atom_vars
    intro candidate occurrence
    exact agrees candidate (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨name, value, member, atomOccurs_of_mem_translated_vars occurrence⟩))))
  · intro left right member
    rw [agrees left (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨left, right, member, Or.inl rfl⟩))))]
    rw [agrees right (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨left, right, member, Or.inr rfl⟩))))]
    exact satisfied.2 left right member

/-- Fresh private variables can realize any pattern model while preserving
the query's entire incoming model. This is a construction, not an assumed
agreement between matching implementations. -/
theorem alpha_extend_model_range {live : List Atom} {query raw fresh : Atom}
    {incoming : Bindings} {rename : String → String}
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename raw fresh)
    (privateNames : ∀ name, AtomOccurs raw name →
      ¬QueryVisibleName live query incoming (rename name))
    (sourceModel base : String → Metta.Atom)
    (satisfied : HEBindingSatisfied base incoming) :
    ∃ extended,
      applyClassSolution extended (toLeaTTaAtom fresh) =
        applyClassSolution sourceModel (toLeaTTaAtom raw) ∧
      HEBindingSatisfied extended incoming ∧
      (∀ name, QueryVisibleName live query incoming name →
        extended name = base name) ∧
      ∀ name, (∃ original, extended name = sourceModel original) ∨
        extended name = base name := by
  classical
  let extended : String → Metta.Atom := fun name =>
    if ∃ original, AtomOccurs raw original ∧ rename original = name then
      sourceModel (Function.invFun rename name)
    else base name
  have agrees : ∀ name, QueryVisibleName live query incoming name →
      extended name = base name := by
    intro name visible
    have absent : ¬∃ original, AtomOccurs raw original ∧ rename original = name := by
      rintro ⟨original, occurs, rfl⟩
      exact privateNames original occurs visible
    simp only [extended, if_neg absent]
  refine ⟨extended, ?_, query_visible_preserves_model agrees satisfied, agrees, ?_⟩
  · rw [alpha_solution renamed extended]
    apply applyClassSolution_congr_on_atom_vars
    intro name occurs
    have present : ∃ original, AtomOccurs raw original ∧ rename original = rename name :=
      ⟨name, atomOccurs_of_mem_translated_vars occurs, rfl⟩
    simp only [Function.comp_apply, extended, if_pos present,
      Function.leftInverse_invFun injective name]
  · intro name
    by_cases present : ∃ original, AtomOccurs raw original ∧ rename original = name
    · exact Or.inl ⟨Function.invFun rename name, if_pos present⟩
    · exact Or.inr (if_neg present)

theorem alpha_extend_model {live : List Atom} {query raw fresh : Atom}
    {incoming : Bindings} {rename : String → String}
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename raw fresh)
    (privateNames : ∀ name, AtomOccurs raw name →
      ¬QueryVisibleName live query incoming (rename name))
    (sourceModel base : String → Metta.Atom)
    (satisfied : HEBindingSatisfied base incoming) :
    ∃ extended,
      applyClassSolution extended (toLeaTTaAtom fresh) =
        applyClassSolution sourceModel (toLeaTTaAtom raw) ∧
      HEBindingSatisfied extended incoming ∧
      ∀ name, QueryVisibleName live query incoming name →
        extended name = base name := by
  obtain ⟨extended, pattern, model, agrees, _⟩ :=
    alpha_extend_model_range injective renamed privateNames sourceModel base satisfied
  exact ⟨extended, pattern, model, agrees⟩

theorem query_visible_solution {live : List Atom} {query : Atom} {incoming : Bindings}
    {base extended : String → Metta.Atom}
    (agrees : ∀ name, QueryVisibleName live query incoming name → extended name = base name) :
    applyClassSolution extended (toLeaTTaAtom query) =
      applyClassSolution base (toLeaTTaAtom query) := by
  apply applyClassSolution_congr_on_atom_vars
  intro name occurrence
  exact agrees name (.inl (atomOccurs_of_mem_translated_vars occurrence))

/-- The caller may retain a symbolic argument vector. If its incoming frame
determines that vector's value, fresh pattern selection still checks precisely
the corresponding source match. -/
theorem alpha_patterns_unify_iff_observed (source values : List Term) (first : Nat)
    {live : List Atom} {query fresh : Atom} {incoming : Bindings} {rename : String → String}
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      ¬QueryVisibleName live query incoming (rename name))
    (frameValues : HEAssignmentsNonVariable incoming)
    (hasModel : ∃ base, HEBindingSatisfied base incoming)
    (queryValue : ∀ valuation, HEBindingSatisfied valuation incoming →
      applyClassSolution valuation (toLeaTTaAtom query) =
        toLeaTTaAtom (MeTTaData.encodeItems values)) :
    (∃ output, UnifyCandidateRel query fresh incoming output) ↔
      ∃ environment, matchTerms source values = some environment := by
  rw [unify_iff_common_model query fresh incoming frameValues]
  constructor
  · rintro ⟨valuation, same, satisfied⟩
    apply (patterns_equation_has_model_iff source values first).mp
    refine ⟨valuation ∘ rename, ?_⟩
    simpa only [HEAtomEquationSatisfied, queryValue valuation satisfied,
      alpha_solution renamed valuation, encoded_items_solution_fixed] using same
  · intro matched
    obtain ⟨sourceModel, same⟩ :=
      (patterns_equation_has_model_iff source values first).mpr matched
    obtain ⟨base, satisfied⟩ := hasModel
    obtain ⟨extended, patternValue, extendedSatisfied, agrees⟩ :=
      alpha_extend_model injective renamed privateNames sourceModel base satisfied
    refine ⟨extended, ?_, extendedSatisfied⟩
    change applyClassSolution extended (toLeaTTaAtom query) =
      applyClassSolution extended (toLeaTTaAtom fresh)
    rw [query_visible_solution agrees, queryValue base satisfied, patternValue]
    simpa only [HEAtomEquationSatisfied, encoded_items_solution_fixed] using same

/-- Every successful symbolic-query candidate binds the original source
occurrences, independently of the representation chosen for its output frame. -/
theorem alpha_patterns_binding_observation_observed (source values : List Term) (first : Nat)
    {query fresh : Atom} {incoming output : Bindings} {rename : String → String}
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (queryValue : ∀ valuation, HEBindingSatisfied valuation incoming →
      applyClassSolution valuation (toLeaTTaAtom query) =
        toLeaTTaAtom (MeTTaData.encodeItems values))
    (candidate : UnifyCandidateRel query fresh incoming output)
    (valuation : String → Metta.Atom) (satisfied : HEBindingSatisfied valuation output) :
    ∃ environment, matchTerms source values = some environment ∧
      ValuationFor (valuation ∘ rename) first environment := by
  obtain ⟨matched, matchProof, mergeProof, _, _⟩ := candidate
  have inputs :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.mergeRel_solution_iff
      mergeProof valuation).mp satisfied
  have same :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.matchRel_solution_iff
      matchProof valuation).mp inputs.1
  apply patterns_solution_reflects source values first (valuation ∘ rename)
  simpa only [queryValue valuation inputs.2, alpha_solution renamed valuation] using same.symm

/-- A closed query and an independently satisfiable frame admit exactly the
same fresh pattern matches as the original pattern in an empty frame. -/
theorem alpha_unify_iff_closed_model {live : List Atom} {query raw fresh : Atom}
    {incoming : Bindings} {rename : String → String}
    (closed : ∀ valuation, applyClassSolution valuation (toLeaTTaAtom query) =
      toLeaTTaAtom query)
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename raw fresh)
    (privateNames : ∀ name, AtomOccurs raw name →
      ¬QueryVisibleName live query incoming (rename name))
    (values : HEAssignmentsNonVariable incoming)
    (hasModel : ∃ base, HEBindingSatisfied base incoming) :
    (∃ output, UnifyCandidateRel query fresh incoming output) ↔
      ∃ valuation, HEAtomEquationSatisfied valuation query raw := by
  rw [unify_iff_common_model query fresh incoming values]
  constructor
  · rintro ⟨valuation, equal, _⟩
    refine ⟨valuation ∘ rename, ?_⟩
    simpa only [HEAtomEquationSatisfied, closed, alpha_solution renamed valuation] using equal
  · rintro ⟨sourceModel, same⟩
    obtain ⟨base, satisfied⟩ := hasModel
    obtain ⟨extended, extendedValue, extendedSatisfied, _⟩ :=
      alpha_extend_model injective renamed privateNames sourceModel base satisfied
    refine ⟨extended, ?_, extendedSatisfied⟩
    simpa only [HEAtomEquationSatisfied, closed, extendedValue] using same

/-- A generated vector pattern still checks exactly the source arguments
after the target evaluator has chosen an injective fresh spelling. -/
theorem alpha_patterns_unify_iff (source values : List Term) (first : Nat)
    {live : List Atom} {incoming : Bindings} {rename : String → String} {fresh : Atom}
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      ¬QueryVisibleName live (MeTTaData.encodeItems values) incoming (rename name))
    (frameValues : HEAssignmentsNonVariable incoming)
    (hasModel : ∃ base, HEBindingSatisfied base incoming) :
    (∃ output, UnifyCandidateRel (MeTTaData.encodeItems values) fresh incoming output) ↔
      ∃ environment, matchTerms source values = some environment := by
  rw [alpha_unify_iff_closed_model (fun valuation => encoded_items_solution_fixed valuation values)
    injective renamed privateNames frameValues hasModel,
    patterns_equation_has_model_iff]

theorem alpha_patterns_unify_refusal_iff (source values : List Term) (first : Nat)
    {live : List Atom} {incoming : Bindings} {rename : String → String} {fresh : Atom}
    (injective : Function.Injective rename)
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (privateNames : ∀ name, AtomOccurs (patterns source first).1.1 name →
      ¬QueryVisibleName live (MeTTaData.encodeItems values) incoming (rename name))
    (frameValues : HEAssignmentsNonVariable incoming)
    (hasModel : ∃ base, HEBindingSatisfied base incoming) :
    UnifyNoMatchRel (MeTTaData.encodeItems values) fresh incoming ↔
      matchTerms source values = none := by
  change (∀ output, ¬UnifyCandidateRel _ _ _ output) ↔ _
  simp only [← not_exists,
    alpha_patterns_unify_iff source values first injective renamed privateNames frameValues hasModel]
  cases matchTerms source values <;> simp

/-- Every output model records the original source occurrence values under
the chosen target spelling; arbitrary binding representation does not matter. -/
theorem alpha_patterns_binding_observation (source values : List Term) (first : Nat)
    {incoming output : Bindings} {rename : String → String} {fresh : Atom}
    (renamed : AlphaRenameAtomRel rename (patterns source first).1.1 fresh)
    (viable : UnifyCandidateRel (MeTTaData.encodeItems values) fresh incoming output)
    (valuation : String → Metta.Atom) (satisfied : HEBindingSatisfied valuation output) :
    ∃ environment, matchTerms source values = some environment ∧
      ValuationFor (valuation ∘ rename) first environment := by
  obtain ⟨matched, matchProof, mergeProof, _, _⟩ := viable
  have inputSatisfied :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.mergeRel_solution_iff
      mergeProof valuation).mp satisfied
  have same :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.matchRel_solution_iff
      matchProof valuation).mp inputSatisfied.1
  apply patterns_solution_reflects source values first (valuation ∘ rename)
  simpa only [encoded_items_solution_fixed, alpha_solution renamed valuation] using same.symm

/-- Actual equation selection can use any lawful fresh instance. The RHS is
returned here as syntax; its subsequent evaluation is a separate judgment. -/
theorem equation_variant_has_candidate {space : Space} {live : List Atom}
    {query rawLhs rawRhs freshLhs freshRhs : Atom} {incoming : Bindings}
    (member : .expression [.symbol "=", rawLhs, rawRhs] ∈ space.atoms)
    (variant : AlphaVariantRel live query incoming rawLhs rawRhs freshLhs freshRhs)
    (closed : ∀ valuation, applyClassSolution valuation (toLeaTTaAtom query) =
      toLeaTTaAtom query)
    (values : HEAssignmentsNonVariable incoming)
    (hasModel : ∃ base, HEBindingSatisfied base incoming)
    (sourceMatch : ∃ model, HEAtomEquationSatisfied model query rawLhs) :
    ∃ output, EquationQueryCandidateRel space live query incoming freshRhs output := by
  obtain ⟨rename, injective, leftRenamed, rightRenamed, privateNames⟩ := variant
  obtain ⟨base, baseSatisfied⟩ := hasModel
  obtain ⟨sourceModel, same⟩ := sourceMatch
  obtain ⟨extended, extendedValue, extendedSatisfied, _⟩ :=
    alpha_extend_model injective leftRenamed (fun name occurrence =>
      privateNames name (Or.inl occurrence)) sourceModel base baseSatisfied
  have queryMatch : HEAtomEquationSatisfied extended query freshLhs := by
    simpa only [HEAtomEquationSatisfied, closed, extendedValue] using same
  obtain ⟨matched, matchProof, matchSatisfied⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMatch_of_solution queryMatch
  obtain ⟨output, mergeProof, outputSatisfied, outputValues⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMerge_of_solution
      extendedSatisfied values matchSatisfied (specMatch_assignmentsNonVariable matchProof)
  exact ⟨output, freshLhs, freshRhs, matched,
    ⟨rawLhs, rawRhs, member,
      ⟨rename, injective, leftRenamed, rightRenamed, privateNames⟩, matchProof⟩, mergeProof,
    semanticLoopFree_of_satisfied_nonvariable outputSatisfied outputValues,
    ⟨extended, outputSatisfied⟩, fun _ _ => rfl⟩

/-- Equation selection from a closed query cannot create a rule or invent a
match by choosing private names or a redundant binding representation. -/
theorem equation_candidate_reflects_closed_query {space : Space} {live : List Atom}
    {query emitted : Atom} {incoming output : Bindings}
    (closed : ∀ valuation, applyClassSolution valuation (toLeaTTaAtom query) =
      toLeaTTaAtom query)
    (candidate : EquationQueryCandidateRel space live query incoming emitted output) :
    ∃ rawLhs rawRhs, .expression [.symbol "=", rawLhs, rawRhs] ∈ space.atoms ∧
      ∃ model, HEAtomEquationSatisfied model query rawLhs := by
  obtain ⟨freshLhs, freshRhs, matched, ruleMatch, mergeProof, _,
    ⟨valuation, satisfied⟩, _⟩ := candidate
  obtain ⟨rawLhs, rawRhs, member, variant, matchProof⟩ := ruleMatch
  obtain ⟨rename, _, leftRenamed, _, _⟩ := variant
  have matchedSatisfied :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.mergeRel_solution_iff
      mergeProof valuation).mp satisfied |>.2
  have same :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.matchRel_solution_iff
      matchProof valuation).mp matchedSatisfied
  refine ⟨rawLhs, rawRhs, member, valuation ∘ rename, ?_⟩
  simpa only [HEAtomEquationSatisfied, closed, alpha_solution leftRenamed valuation] using same

private def callerAlias : Bindings :=
  (Bindings.empty.assign "old" (MeTTaData.encode (.sym "old"))).addEquality
    (freshName 0) "old"

private theorem callerAlias_values : HEAssignmentsNonVariable callerAlias := by
  intro name value member
  simp [callerAlias, Bindings.empty, Bindings.assign, Bindings.isBound,
    Bindings.lookup, Bindings.addEquality, MeTTaData.encode] at member

private theorem callerAlias_model :
    HEBindingSatisfied (fun _ => toLeaTTaAtom (MeTTaData.encode (.sym "old"))) callerAlias := by
  constructor
  · intro name value member
    simp only [callerAlias, Bindings.assign, Bindings.isBound, Bindings.lookup,
      Bindings.empty, Bindings.addEquality, List.lookup_nil, Option.isSome_none,
      Bool.false_eq_true, if_false, List.nil_append, List.mem_singleton, Prod.mk.injEq] at member
    rw [member.2, encoded_solution_fixed]
  · intro _ _ _
    rfl

private theorem callerAlias_fresh :
    ¬QueryVisibleName [] (MeTTaData.encode (.sym "new")) callerAlias "fresh" := by
  rintro (occurrence | ⟨atom, member, _⟩ | ⟨value, member⟩ |
    ⟨name, value, member, occurrence⟩ | ⟨left, right, member, endpoint⟩)
  · have impossible := mem_translated_vars_of_atomOccurs occurrence
    simp [MeTTaData.encode, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars] at impossible
  · simp at member
  · simp [callerAlias, Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup, Bindings.addEquality] at member
  · simp only [callerAlias, Bindings.assign, Bindings.isBound, Bindings.lookup,
      Bindings.empty, Bindings.addEquality, List.lookup_nil, Option.isSome_none,
      Bool.false_eq_true, if_false, List.nil_append, List.mem_singleton, Prod.mk.injEq] at member
    rw [member.2] at occurrence
    have impossible := mem_translated_vars_of_atomOccurs occurrence
    simp [MeTTaData.encode, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.vars] at impossible
  · simp [callerAlias, Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup, Bindings.addEquality, freshName] at member
    obtain ⟨rfl, rfl⟩ := member
    simp at endpoint
    exact (by decide : "fresh" ≠ "nik" ++ Nat.repr 0) endpoint

/-- Freshening permits a new value even when the original private spelling
is occupied through a caller alias. The preceding module gives the refusal
when that alias is accidentally reused. -/
theorem freshening_separates_caller_alias :
    ∃ output, UnifyCandidateRel (MeTTaData.encode (.sym "new"))
      (.var "fresh") callerAlias output := by
  apply (alpha_unify_iff_closed_model
    (fun valuation => encoded_solution_fixed valuation (.sym "new"))
    (Equiv.swap (freshName 0) "fresh").injective
    (raw := (pattern (.var "x") 0).1.1) (live := [])
    (by simpa only [pattern_variable, Equiv.swap_apply_left] using
      AlphaRenameAtomRel.variable (rename := Equiv.swap (freshName 0) "fresh") (freshName 0))
    (by
      intro name occurrence
      change AtomOccurs (.var (freshName 0)) name at occurrence
      cases occurrence
      simpa only [Equiv.swap_apply_left] using callerAlias_fresh)
    callerAlias_values ⟨_, callerAlias_model⟩).mpr
  exact (pattern_equation_has_model_iff (.var "x") (.sym "new") 0).mpr
    ⟨[("x", .sym "new")], rfl⟩

/-- Replacing an injective renaming with a collapsing name map can lose a
valid source match. Distinct occurrence bindings must remain distinct. -/
theorem merging_pattern_names_loses_valid_match :
    matchTerms [.var "x", .var "y"] [.sym "a", .sym "b"] =
      some [("x", .sym "a"), ("y", .sym "b")] ∧
    UnifyNoMatchRel (MeTTaData.encodeItems [.sym "a", .sym "b"])
      (call "nik:Cons" [.var "same",
        call "nik:Cons" [.var "same", .symbol "nik:Nil"]]) Bindings.empty := by
  constructor
  · rfl
  · intro output viable
    obtain ⟨valuation, same⟩ := (unify_empty_iff_model _ _).mp ⟨output, viable⟩
    simp [HEAtomEquationSatisfied, MeTTaData.encodeItems, MeTTaData.encode,
      toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround, applyClassSolution, call] at same
    have impossible := same.1.trans same.2.symm
    simp at impossible

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
