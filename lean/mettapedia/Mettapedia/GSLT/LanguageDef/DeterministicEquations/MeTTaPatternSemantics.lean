import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaBindingCorrespondence
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

/-!
# Emitted patterns in the independent MeTTa matching semantics

The semantic matcher uses atom equations and binding models. These laws
connect that interface to the actual generated patterns. In particular,
semantic refusal does not rely on exhausting an executable matcher's fuel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.LeaTTaSpecConformance
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

/-- A valuation reads each fresh occurrence as its corresponding guest datum. -/
def ValuationFor (valuation : String → Metta.Atom) : Nat → Env → Prop
  | _, [] => True
  | first, (_, value) :: rest =>
      valuation (freshName first) = toLeaTTaAtom (MeTTaData.encode value) ∧
        ValuationFor valuation (first + 1) rest

theorem valuationFor_append (valuation : String → Metta.Atom)
    (first : Nat) (left right : Env) :
    ValuationFor valuation first (left ++ right) ↔
      ValuationFor valuation first left ∧
        ValuationFor valuation (first + left.length) right := by
  induction left generalizing first with
  | nil => simp [ValuationFor]
  | cons entry rest ih =>
      simp [ValuationFor, ih, and_assoc, Nat.add_left_comm, Nat.add_comm]

theorem valuationFor_of_index (valuation : String → Metta.Atom)
    (first : Nat) (environment : Env)
    (aligned : ∀ (index : Nat) (inside : index < environment.length),
      valuation (freshName (first + index)) =
        toLeaTTaAtom (MeTTaData.encode environment[index].2)) :
    ValuationFor valuation first environment := by
  induction environment generalizing first with
  | nil => trivial
  | cons entry rest ih =>
      constructor
      · have head := aligned 0 (by simp)
        change valuation (freshName (first + 0)) =
          toLeaTTaAtom (MeTTaData.encode entry.2) at head
        simpa only [Nat.add_zero] using head
      · apply ih
        intro index inside
        have next := aligned (index + 1) (by simpa using inside)
        change valuation (freshName (first + (index + 1))) =
          toLeaTTaAtom (MeTTaData.encode rest[index].2) at next
        simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next

/-- A concrete model of every fresh pattern occurrence. -/
def matchedValuation (first : Nat) (environment : Env) (name : String) : Metta.Atom :=
  (((extendMatch first environment Bindings.empty).lookup name).map toLeaTTaAtom).getD
    (.var name)

theorem matchedValuation_reads (first : Nat) (environment : Env) :
    ValuationFor (matchedValuation first environment) first environment := by
  apply valuationFor_of_index
  intro index inside
  simp only [matchedValuation,
    extendMatch_lookup_index environment (FreshFrom.empty first) index inside,
    Option.map_some, Option.getD_some]

mutual

theorem encoded_solution_fixed (valuation : String → Metta.Atom) (term : Term) :
    applyClassSolution valuation (toLeaTTaAtom (MeTTaData.encode term)) =
      toLeaTTaAtom (MeTTaData.encode term) := by
  cases term with
  | sym | lit | var =>
      simp [MeTTaData.encode, toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution]
  | expr items | list items =>
      simp [MeTTaData.encode, toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution,
        encoded_items_solution_fixed valuation items]
termination_by sizeOf term

theorem encoded_items_solution_fixed (valuation : String → Metta.Atom)
    (terms : List Term) :
    applyClassSolution valuation (toLeaTTaAtom (MeTTaData.encodeItems terms)) =
      toLeaTTaAtom (MeTTaData.encodeItems terms) := by
  cases terms with
  | nil => simp [MeTTaData.encodeItems, toLeaTTaAtom, applyClassSolution]
  | cons first rest =>
      simp [MeTTaData.encodeItems, toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution,
        encoded_solution_fixed valuation first, encoded_items_solution_fixed valuation rest]
termination_by sizeOf terms

end

mutual

theorem pattern_solution_of_match (source value : Term) (environment : Env)
    (matched : matchTerm source value = some environment) (first : Nat)
    (valuation : String → Metta.Atom) (reads : ValuationFor valuation first environment) :
    applyClassSolution valuation (toLeaTTaAtom (pattern source first).1.1) =
      toLeaTTaAtom (MeTTaData.encode value) := by
  cases source with
  | var name =>
      cases matched
      simpa only [pattern_variable, toLeaTTaAtom, applyClassSolution] using reads.1
  | sym name =>
      cases value <;> simp [matchTerm] at matched
      rcases matched with ⟨rfl, rfl⟩
      exact encoded_solution_fixed valuation (.sym _)
  | lit spelling =>
      cases value <;> simp [matchTerm] at matched
      rcases matched with ⟨rfl, rfl⟩
      exact encoded_solution_fixed valuation (.lit _)
  | expr items =>
      cases value <;> simp [matchTerm] at matched
      simp only [pattern_expression, call, MeTTaData.encode, toLeaTTaAtom,
        toLeaTTaAtoms, applyClassSolution, List.map_cons, List.map_nil]
      rw [patterns_solution_of_match items _ environment matched first valuation reads]
  | list items =>
      cases value <;> simp [matchTerm] at matched
      simp only [pattern_list, call, MeTTaData.encode, toLeaTTaAtom,
        toLeaTTaAtoms, applyClassSolution, List.map_cons, List.map_nil]
      rw [patterns_solution_of_match items _ environment matched first valuation reads]
termination_by sizeOf source

theorem patterns_solution_of_match (source values : List Term) (environment : Env)
    (matched : matchTerms source values = some environment) (first : Nat)
    (valuation : String → Metta.Atom) (reads : ValuationFor valuation first environment) :
    applyClassSolution valuation (toLeaTTaAtom (patterns source first).1.1) =
      toLeaTTaAtom (MeTTaData.encodeItems values) := by
  cases source with
  | nil => cases values <;> simp_all [matchTerms, patterns_nil,
      MeTTaData.encodeItems, toLeaTTaAtom, applyClassSolution]
  | cons head rest =>
      cases values with
      | nil => simp [matchTerms] at matched
      | cons value tail =>
          cases headMatch : matchTerm head value with
          | none => simp [matchTerms, headMatch] at matched
          | some headEnvironment =>
              cases tailMatch : matchTerms rest tail with
              | none => simp [matchTerms, headMatch, tailMatch] at matched
              | some tailEnvironment =>
                  have same : headEnvironment ++ tailEnvironment = environment := by
                    simpa [matchTerms, headMatch, tailMatch] using matched
                  subst environment
                  rw [valuationFor_append] at reads
                  simp only [patterns_cons, call, MeTTaData.encodeItems, toLeaTTaAtom,
                    toLeaTTaAtoms, applyClassSolution, List.map_cons, List.map_nil]
                  rw [pattern_solution_of_match head value headEnvironment headMatch
                      first valuation reads.1,
                    pattern_end_of_match head value headEnvironment headMatch,
                    patterns_solution_of_match rest tail tailEnvironment tailMatch
                      (first + headEnvironment.length) valuation reads.2]
termination_by sizeOf source

end

mutual

/-- A model of the emitted pattern equation cannot invent a source match. -/
theorem pattern_solution_reflects (source value : Term) (first : Nat)
    (valuation : String → Metta.Atom)
    (same : applyClassSolution valuation (toLeaTTaAtom (pattern source first).1.1) =
      toLeaTTaAtom (MeTTaData.encode value)) :
    ∃ environment, matchTerm source value = some environment ∧
      ValuationFor valuation first environment := by
  cases source with
  | var name =>
      refine ⟨[(name, value)], rfl, ?_, trivial⟩
      simpa only [pattern_variable, toLeaTTaAtom, applyClassSolution] using same
  | sym name =>
      simp only [pattern_symbol, encoded_solution_fixed] at same
      cases value <;>
        simp_all [MeTTaData.encode,
          toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround, matchTerm, ValuationFor]
  | lit spelling =>
      simp only [pattern_literal, encoded_solution_fixed] at same
      cases value <;>
        simp_all [MeTTaData.encode,
          toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround, matchTerm, ValuationFor]
  | expr items =>
      cases value <;>
        simp [pattern_expression, call, MeTTaData.encode, toLeaTTaAtom,
          toLeaTTaAtoms, applyClassSolution] at same
      exact patterns_solution_reflects items _ first valuation same
  | list items =>
      cases value <;>
        simp [pattern_list, call, MeTTaData.encode, toLeaTTaAtom,
          toLeaTTaAtoms, applyClassSolution] at same
      exact patterns_solution_reflects items _ first valuation same
termination_by sizeOf source

theorem patterns_solution_reflects (source values : List Term) (first : Nat)
    (valuation : String → Metta.Atom)
    (same : applyClassSolution valuation (toLeaTTaAtom (patterns source first).1.1) =
      toLeaTTaAtom (MeTTaData.encodeItems values)) :
    ∃ environment, matchTerms source values = some environment ∧
      ValuationFor valuation first environment := by
  cases source with
  | nil =>
      cases values <;>
        simp_all [patterns_nil, MeTTaData.encodeItems, toLeaTTaAtom,
          toLeaTTaAtoms, applyClassSolution, matchTerms, ValuationFor]
  | cons head rest =>
      cases values with
      | nil =>
          simp [patterns_cons, call, MeTTaData.encodeItems, toLeaTTaAtom,
            toLeaTTaAtoms, applyClassSolution] at same
      | cons value tail =>
          simp only [patterns_cons, call, MeTTaData.encodeItems, toLeaTTaAtom,
            toLeaTTaAtoms, applyClassSolution, List.map_cons, List.map_nil,
            Metta.Atom.expr.injEq, List.cons.injEq] at same
          obtain ⟨headEnvironment, headMatch, headReads⟩ :=
            pattern_solution_reflects head value first valuation same.2.1
          obtain ⟨tailEnvironment, tailMatch, tailReads⟩ :=
            patterns_solution_reflects rest tail (pattern head first).2 valuation same.2.2.1
          refine ⟨headEnvironment ++ tailEnvironment,
            by simp [matchTerms, headMatch, tailMatch], ?_⟩
          rw [valuationFor_append]
          rw [pattern_end_of_match head value headEnvironment headMatch] at tailReads
          exact ⟨headReads, tailReads⟩
termination_by sizeOf source

end

/-- The independent atom equation has a model exactly for source matches. -/
theorem pattern_equation_has_model_iff (source value : Term) (first : Nat) :
    (∃ valuation, HEAtomEquationSatisfied valuation
      (MeTTaData.encode value) (pattern source first).1.1) ↔
      ∃ environment, matchTerm source value = some environment := by
  constructor
  · rintro ⟨valuation, same⟩
    obtain ⟨environment, matched, _⟩ := pattern_solution_reflects source value first valuation
      (by simpa only [HEAtomEquationSatisfied, encoded_solution_fixed] using same.symm)
    exact ⟨environment, matched⟩
  · rintro ⟨environment, matched⟩
    refine ⟨matchedValuation first environment, ?_⟩
    simpa only [HEAtomEquationSatisfied, encoded_solution_fixed] using
      (pattern_solution_of_match source value environment matched first
        (matchedValuation first environment) (matchedValuation_reads first environment)).symm

theorem patterns_equation_has_model_iff (source values : List Term) (first : Nat) :
    (∃ valuation, HEAtomEquationSatisfied valuation
      (MeTTaData.encodeItems values) (patterns source first).1.1) ↔
      ∃ environment, matchTerms source values = some environment := by
  constructor
  · rintro ⟨valuation, same⟩
    obtain ⟨environment, matched, _⟩ := patterns_solution_reflects source values first valuation
      (by simpa only [HEAtomEquationSatisfied, encoded_items_solution_fixed] using same.symm)
    exact ⟨environment, matched⟩
  · rintro ⟨environment, matched⟩
    refine ⟨matchedValuation first environment, ?_⟩
    simpa only [HEAtomEquationSatisfied, encoded_items_solution_fixed] using
      (patterns_solution_of_match source values environment matched first
        (matchedValuation first environment) (matchedValuation_reads first environment)).symm

/-- Viable matching extends exactly the common models of the atom equation
and incoming frame. Bare-variable aliases are represented by equality edges. -/
theorem unify_iff_common_model (target source : Atom) (incoming : Bindings)
    (values : HEAssignmentsNonVariable incoming) :
    (∃ output, UnifyCandidateRel target source incoming output) ↔
      ∃ valuation, HEAtomEquationSatisfied valuation target source ∧
        HEBindingSatisfied valuation incoming := by
  constructor
  · rintro ⟨output, matched, matchProof, mergeProof, _, valuation, satisfies⟩
    have inputSatisfied :=
      (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.mergeRel_solution_iff
        mergeProof valuation).mp satisfies
    exact ⟨valuation,
      (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.matchRel_solution_iff
        matchProof valuation).mp inputSatisfied.1, inputSatisfied.2⟩
  · rintro ⟨valuation, same, incomingSatisfied⟩
    obtain ⟨matched, matchProof, satisfies⟩ :=
      Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMatch_of_solution same
    obtain ⟨output, merged, outputSatisfied, outputValues⟩ :=
      Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness.exists_specMerge_of_solution
        satisfies (specMatch_assignmentsNonVariable matchProof) incomingSatisfied values
    exact ⟨output, matched, matchProof, merged,
      semanticLoopFree_of_satisfied_nonvariable outputSatisfied outputValues,
      valuation, outputSatisfied⟩

/-- Empty frames impose no extra constraint on the atom equation. -/
theorem unify_empty_iff_model (target source : Atom) :
    (∃ output, UnifyCandidateRel target source Bindings.empty output) ↔
      ∃ valuation, HEAtomEquationSatisfied valuation target source := by
  rw [unify_iff_common_model target source Bindings.empty (by
    intro key value member
    simp [Bindings.empty] at member)]
  simp only [hesat_empty_iff, and_true]

theorem pattern_unify_iff (source value : Term) (first : Nat) :
    (∃ output, UnifyCandidateRel (MeTTaData.encode value)
      (pattern source first).1.1 Bindings.empty output) ↔
      ∃ environment, matchTerm source value = some environment := by
  rw [unify_empty_iff_model, pattern_equation_has_model_iff]

theorem patterns_unify_iff (source values : List Term) (first : Nat) :
    (∃ output, UnifyCandidateRel (MeTTaData.encodeItems values)
      (patterns source first).1.1 Bindings.empty output) ↔
      ∃ environment, matchTerms source values = some environment := by
  rw [unify_empty_iff_model, patterns_equation_has_model_iff]

/-- Refusal holds in the independent, fuel-free semantics. -/
theorem pattern_unify_refusal_iff (source value : Term) (first : Nat) :
    UnifyNoMatchRel (MeTTaData.encode value) (pattern source first).1.1 Bindings.empty ↔
      matchTerm source value = none := by
  change (∀ output, ¬UnifyCandidateRel _ _ _ output) ↔ _
  simp only [← not_exists, pattern_unify_iff]
  cases matchTerm source value <;> simp

theorem patterns_unify_refusal_iff (source values : List Term) (first : Nat) :
    UnifyNoMatchRel (MeTTaData.encodeItems values) (patterns source first).1.1 Bindings.empty ↔
      matchTerms source values = none := by
  change (∀ output, ¬UnifyCandidateRel _ _ _ output) ↔ _
  simp only [← not_exists, patterns_unify_iff]
  cases matchTerms source values <;> simp

/-- Every model of a viable target match reads the source bindings faithfully. -/
theorem pattern_unify_binding_observation (source value : Term) (first : Nat)
    (incoming output : Bindings) (viable : UnifyCandidateRel (MeTTaData.encode value)
      (pattern source first).1.1 incoming output)
    (valuation : String → Metta.Atom) (satisfies : HEBindingSatisfied valuation output) :
    ∃ environment, matchTerm source value = some environment ∧
      ValuationFor valuation first environment := by
  obtain ⟨matched, matchProof, mergeProof, _, _⟩ := viable
  have inputSatisfied :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.mergeRel_solution_iff
      mergeProof valuation).mp satisfies
  have same :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.matchRel_solution_iff
      matchProof valuation).mp inputSatisfied.1
  apply pattern_solution_reflects source value first valuation
  simpa only [encoded_solution_fixed] using same.symm

theorem patterns_unify_binding_observation (source values : List Term) (first : Nat)
    (incoming output : Bindings) (viable : UnifyCandidateRel (MeTTaData.encodeItems values)
      (patterns source first).1.1 incoming output)
    (valuation : String → Metta.Atom) (satisfies : HEBindingSatisfied valuation output) :
    ∃ environment, matchTerms source values = some environment ∧
      ValuationFor valuation first environment := by
  obtain ⟨matched, matchProof, mergeProof, _, _⟩ := viable
  have inputSatisfied :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.mergeRel_solution_iff
      mergeProof valuation).mp satisfies
  have same :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory.matchRel_solution_iff
      matchProof valuation).mp inputSatisfied.1
  apply patterns_solution_reflects source values first valuation
  simpa only [encoded_items_solution_fixed] using same.symm

theorem patterns_unify_in_frame_iff (source values : List Term) (first : Nat)
    (incoming : Bindings) (frameValues : HEAssignmentsNonVariable incoming) :
    (∃ output, UnifyCandidateRel (MeTTaData.encodeItems values)
      (patterns source first).1.1 incoming output) ↔
      ∃ environment valuation, matchTerms source values = some environment ∧
        ValuationFor valuation first environment ∧ HEBindingSatisfied valuation incoming := by
  rw [unify_iff_common_model _ _ incoming frameValues]
  constructor
  · rintro ⟨valuation, same, satisfies⟩
    obtain ⟨environment, matched, reads⟩ :=
      patterns_solution_reflects source values first valuation
        (by simpa only [HEAtomEquationSatisfied, encoded_items_solution_fixed] using same.symm)
    exact ⟨environment, valuation, matched, reads, satisfies⟩
  · rintro ⟨environment, valuation, matched, reads, satisfies⟩
    refine ⟨valuation, ?_, satisfies⟩
    simpa only [HEAtomEquationSatisfied, encoded_items_solution_fixed] using
      (patterns_solution_of_match source values environment matched first valuation reads).symm

theorem semantic_match_keeps_guest_variable_as_data :
    ∃ output, UnifyCandidateRel (MeTTaData.encode (.var "nik0"))
      (pattern (.var "x") 0).1.1 Bindings.empty output :=
  (pattern_unify_iff _ _ _).mpr ⟨[("x", .var "nik0")], rfl⟩

theorem semantic_vector_match_refuses_wrong_arity :
    UnifyNoMatchRel (MeTTaData.encodeItems [.sym "a", .sym "b"])
      (patterns [.var "x"] 0).1.1 Bindings.empty :=
  (patterns_unify_refusal_iff _ _ _).mpr rfl

theorem semantic_match_refuses_late_literal_mismatch :
    UnifyNoMatchRel (MeTTaData.encode (.expr [.sym "f", .lit "wrong"]))
      (pattern (.expr [.sym "f", .lit "required"]) 0).1.1 Bindings.empty :=
  (pattern_unify_refusal_iff _ _ _).mpr rfl

/-- An unused assignment key can still be occupied through an equality alias. -/
theorem semantic_frame_alias_capture :
    let incoming := (Bindings.empty.assign "old" (MeTTaData.encode (.sym "old"))).addEquality
      (freshName 0) "old"
    incoming.lookup (freshName 0) = none ∧
      UnifyNoMatchRel (MeTTaData.encode (.sym "new")) (pattern (.var "x") 0).1.1 incoming := by
  dsimp only
  constructor
  · rfl
  · intro output viable
    obtain ⟨valuation, same, satisfies⟩ :=
      (unify_iff_common_model _ _ _ (by
        intro key value member
        simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
          Bindings.addEquality, MeTTaData.encode] at member)).mp ⟨output, viable⟩
    have oldValue := satisfies.1 "old" (MeTTaData.encode (.sym "old")) (by
      simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, Bindings.addEquality])
    have aliasEq := satisfies.2 (freshName 0) "old" (by
      simp [Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup, Bindings.addEquality])
    simp only [HEAtomEquationSatisfied, encoded_solution_fixed, pattern_variable,
      toLeaTTaAtom, applyClassSolution, aliasEq, oldValue] at same
    simp [MeTTaData.encode, toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround] at same

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit
