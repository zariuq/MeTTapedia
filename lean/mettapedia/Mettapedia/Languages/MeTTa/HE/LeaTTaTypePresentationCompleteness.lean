import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ExactNormal

/-!
# Completeness of repaired LeaTTa for finite type presentations

Exact negative type outcomes require both directions of the type boundary.
This module proves the converse of presentation soundness: every satisfiable
finite presentation derivation on disjoint fresh type scopes is realized by
LeaTTa's repaired deterministic type matcher.

The proof follows the raw wildcard/expression structure of the spec
presentation.  At ordinary leaves it assembles the clean matcher completeness
seal with semantic LeaTTa merge existence.  A satisfying valuation is
threaded through the recursion, so every constructed candidate survives the
runtime loop filter; head selection may choose a different most-general
presentation, but its solution theory remains the same.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationCompleteness

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance
open LeaTTaMergeExistence

/-- A repaired runtime accumulator together with one fixed translated native
model.  Keeping the model explicit makes prefix compatibility available at
every recursive type child. -/
structure RuntimeValuationState
    (valuation : String → Atom) (bindings : Metta.Bindings) : Prop where
  satisfied : LeaBindingSatisfied
    (fun name => toLeaTTaAtom (valuation name)) bindings
  runtime : LeaRuntimeBindingInvariant bindings

/-- Empty runtime bindings satisfy every translated native valuation. -/
theorem runtimeValuationState_empty (valuation : String → Atom) :
    RuntimeValuationState valuation Metta.Bindings.empty := by
  constructor
  · simp [LeaBindingSatisfied, Metta.Bindings.empty]
  · exact leaRuntimeBindingInvariant_empty

private theorem toLeaTTaAtom_beq_undefined_eq_false
    (atom : Atom) (hneq : atom ≠ Atom.undefinedType) :
    (toLeaTTaAtom atom == Metta.Atom.sym "%Undefined%") = false := by
  cases atom with
  | symbol name =>
      simp [Atom.undefinedType] at hneq
      change (name == "%Undefined%") = false
      simp [hneq]
  | var | grounded | expression => rfl

private theorem toLeaTTaAtom_beq_atomType_eq_false
    (atom : Atom) (hneq : atom ≠ Atom.atomType) :
    (toLeaTTaAtom atom == Metta.Atom.sym "Atom") = false := by
  cases atom with
  | symbol name =>
      simp [Atom.atomType] at hneq
      change (name == "Atom") = false
      simp [hneq]
  | var | grounded | expression => rfl

private theorem mettaEquationSatisfied_of_native
    (valuation : String → Atom) {left right : Atom}
    (equation : applyTypeValuation valuation left =
      applyTypeValuation valuation right) :
    MettaEquationSatisfied (fun name => toLeaTTaAtom (valuation name))
      (toLeaTTaAtom left, toLeaTTaAtom right) := by
  have translated := congrArg toLeaTTaAtom equation
  simpa [MettaEquationSatisfied, toLeaTTaAtom_applyTypeValuation] using
    translated

/-- A satisfiable, scope-disjoint ordinary leaf makes the repaired runtime
leaf matcher return a loop-free accumulator satisfying the same valuation.
The selected head need not be the witness used to prove nonemptiness. -/
private theorem matchReduced_leaf_exists
    (valuation : String → Atom)
    {bindings : Metta.Bindings} (state : RuntimeValuationState valuation bindings)
    {left right : Atom}
    (leftNotUndefined : left ≠ Atom.undefinedType)
    (rightNotUndefined : right ≠ Atom.undefinedType)
    (leafShape : ReducedTypeLeafShape left right)
    (disjoint : VarsDisjoint left right)
    (equation : applyTypeValuation valuation left =
      applyTypeValuation valuation right) :
    ∃ output,
      Metta.Minimal.matchReduced bindings
          (toLeaTTaAtom left) (toLeaTTaAtom right) = some output ∧
        RuntimeValuationState valuation output := by
  let leaValuation : String → Metta.Atom :=
    fun name => toLeaTTaAtom (valuation name)
  have mettaEquation : MettaEquationSatisfied leaValuation
      (toLeaTTaAtom left, toLeaTTaAtom right) :=
    mettaEquationSatisfied_of_native valuation equation
  have specEquation : HEAtomEquationSatisfied leaValuation right left := by
    simpa [HEAtomEquationSatisfied, MettaEquationSatisfied, eq_comm] using
      mettaEquation
  obtain ⟨specMatched, specMatch, specMatchedSatisfied⟩ :=
    Spec.Match.Completeness.exists_specMatch_of_solution specEquation
  obtain ⟨matched, matchedMember, matchedTheory⟩ :=
    specMatch_observational_complete_of_satisfiable
      specMatch disjoint.symm ⟨leaValuation, by
        simpa [MettaEquationSatisfied, eq_comm] using mettaEquation⟩
  have matchedSatisfied : LeaBindingSatisfied leaValuation matched :=
    (matchedTheory leaValuation).mp specMatchedSatisfied
  obtain ⟨merged, mergedMember, mergedSatisfied, mergedNoFloat⟩ :=
    merge_exists_of_satisfied state.runtime.noFloat
      (leaMatchAtoms_result_noFloat
        (toLeaTTaAtom_noFloat left) (toLeaTTaAtom_noFloat right)
        matchedMember)
      state.satisfied matchedSatisfied
  have mergedNonVariable : LeaAssignmentsNonVariable merged :=
    leaMerge_result_assignmentsNonVariable
      state.runtime.assignmentsNonVariable mergedMember
  have mergedIrreflexive : LeaEqualitiesIrreflexive merged :=
    leaMerge_result_equalitiesIrreflexive
      state.runtime.equalitiesIrreflexive mergedMember
  have mergedLoop : merged.hasLoop = false :=
    leaBindings_hasLoop_false_of_satisfied mergedSatisfied
      mergedNonVariable mergedIrreflexive
  let candidates :=
    ((Metta.matchAtoms (toLeaTTaAtom left) (toLeaTTaAtom right)).flatMap
      (Metta.Bindings.merge bindings)).filter
        (fun candidate => !candidate.hasLoop)
  have mergedCandidate : merged ∈ candidates := by
    apply List.mem_filter.mpr
    constructor
    · exact List.mem_flatMap.mpr ⟨matched, matchedMember, mergedMember⟩
    · simp [mergedLoop]
  cases candidatesEquation : candidates with
  | nil => simp [candidatesEquation] at mergedCandidate
  | cons selected remaining =>
      have selectedCandidate : selected ∈ candidates := by
        rw [candidatesEquation]
        simp
      have selectedParts := List.mem_filter.mp selectedCandidate
      obtain ⟨selectedMatched, selectedMatch, selectedMerge⟩ :=
        List.mem_flatMap.mp selectedParts.1
      have selectedLoop : selected.hasLoop = false := by
        simpa using selectedParts.2
      have selectedMatchedNoFloat : LeaBindingsNoFloat selectedMatched :=
        leaMatchAtoms_result_noFloat
          (toLeaTTaAtom_noFloat left) (toLeaTTaAtom_noFloat right)
          selectedMatch
      have selectedMatchedSatisfied :
          LeaBindingSatisfied leaValuation selectedMatched :=
        (leaMatchAtoms_solution_iff leaValuation
          (toLeaTTaAtom_noFloat left) (toLeaTTaAtom_noFloat right)
          selectedMatch).mpr mettaEquation
      have selectedSatisfied : LeaBindingSatisfied leaValuation selected :=
        (leaMerge_solution_iff leaValuation state.runtime.noFloat
          selectedMatchedNoFloat selectedMerge).mpr
            ⟨state.satisfied, selectedMatchedSatisfied⟩
      have selectedRuntime : LeaRuntimeBindingInvariant selected :=
        state.runtime.merge_matchOutput
          (toLeaTTaAtom_noFloat left) (toLeaTTaAtom_noFloat right)
          selectedMatch selectedMerge selectedLoop
      refine ⟨selected, ?_, ⟨selectedSatisfied, selectedRuntime⟩⟩
      have leftUndefinedBeq :=
        toLeaTTaAtom_beq_undefined_eq_false left leftNotUndefined
      have rightUndefinedBeq :=
        toLeaTTaAtom_beq_undefined_eq_false right rightNotUndefined
      cases left <;> cases right
      all_goals
        simp only [toLeaTTaAtom] at leftUndefinedBeq rightUndefinedBeq ⊢
      all_goals
        simp [ReducedTypeLeafShape] at leafShape
      all_goals
        rw [Metta.Minimal.matchReduced.eq_2 bindings _ _ (by
          intro lefts rights leftExpression rightExpression
          cases leftExpression <;> cases rightExpression)]
        rw [leftUndefinedBeq, rightUndefinedBeq]
        change candidates.head? = some selected
        rw [candidatesEquation]
        rfl

private abbrev ReducedRuntimeComplete
    (valuation : String → Atom) (bindings : Metta.Bindings)
    (left right : Atom) : Prop :=
  ∃ output,
    Metta.Minimal.matchReduced bindings
        (toLeaTTaAtom left) (toLeaTTaAtom right) = some output ∧
      RuntimeValuationState valuation output

private abbrev ReducedListRuntimeComplete
    (valuation : String → Atom) (bindings : Metta.Bindings)
    (left right : List Atom) : Prop :=
  ∃ output,
    Metta.Minimal.matchReducedList bindings
        (toLeaTTaAtoms left) (toLeaTTaAtoms right) = some output ∧
      RuntimeValuationState valuation output

mutual

private theorem reduced_runtime_complete
    (valuation : String → Atom)
    {substitution outputPresentation : TypeSubst}
    {bindings : Metta.Bindings}
    (normal : substitution.Normal)
    (outputSatisfied : TypeSubstSatisfied valuation outputPresentation)
    {left right : Atom}
    (derivation : ReducedTypePresentationMatchRel
      substitution left right outputPresentation)
    (state : RuntimeValuationState valuation bindings)
    (disjoint : VarsDisjoint left right) :
    ReducedRuntimeComplete valuation bindings left right := by
  have theory := ReducedTypePresentationMatchRel.solutions
    derivation normal valuation
  have parts := theory.mp outputSatisfied
  cases derivation with
  | undefinedLeft substitution right =>
      have same :
          (Metta.Atom.sym "%Undefined%" ==
            Metta.Atom.sym "%Undefined%") = true := by decide
      exact ⟨bindings, by simp [Metta.Minimal.matchReduced,
        toLeaTTaAtom, Atom.undefinedType, same], state⟩
  | undefinedRight substitution left =>
      have same :
          (Metta.Atom.sym "%Undefined%" ==
            Metta.Atom.sym "%Undefined%") = true := by decide
      exact ⟨bindings, by simp [Metta.Minimal.matchReduced,
        toLeaTTaAtom, Atom.undefinedType, same], state⟩
  | @expression substitution output lefts rights children =>
      have listsDisjoint : AtomListsVarsDisjoint lefts rights :=
        varsDisjoint_expression_iff.mp disjoint
      obtain ⟨runtimeOutput, runtimeSuccess, outputState⟩ :=
        reduced_list_runtime_complete valuation normal outputSatisfied
          children state listsDisjoint
      have leftUndefinedBeq :
          (Metta.Atom.expr (toLeaTTaAtoms lefts) ==
            Metta.Atom.sym "%Undefined%") = false := rfl
      have rightUndefinedBeq :
          (Metta.Atom.expr (toLeaTTaAtoms rights) ==
            Metta.Atom.sym "%Undefined%") = false := rfl
      exact ⟨runtimeOutput, by
        simp only [toLeaTTaAtom]
        rw [Metta.Minimal.matchReduced.eq_1,
          leftUndefinedBeq, rightUndefinedBeq]
        exact runtimeSuccess,
        outputState⟩
  | @ordinary substitution output left right resolvedLeft resolvedRight
      leftNotUndefined rightNotUndefined leafShape leftApply rightApply applied =>
      have equation : applyTypeValuation valuation left =
          applyTypeValuation valuation right :=
        (reducedTypeConsistent_iff_applied_eq_of_leaf
          valuation left right leafShape leftNotUndefined
            rightNotUndefined).mp parts.2
      exact matchReduced_leaf_exists valuation state leftNotUndefined
        rightNotUndefined leafShape disjoint equation

private theorem reduced_list_runtime_complete
    (valuation : String → Atom)
    {substitution outputPresentation : TypeSubst}
    {bindings : Metta.Bindings}
    (normal : substitution.Normal)
    (outputSatisfied : TypeSubstSatisfied valuation outputPresentation)
    {left right : List Atom}
    (derivation : ReducedTypePresentationListMatchRel
      substitution left right outputPresentation)
    (state : RuntimeValuationState valuation bindings)
    (disjoint : AtomListsVarsDisjoint left right) :
    ReducedListRuntimeComplete valuation bindings left right := by
  cases derivation with
  | nil substitution =>
      exact ⟨bindings, by simp [Metta.Minimal.matchReducedList,
        toLeaTTaAtoms], state⟩
  | @cons substitution next output left right lefts rights head tail =>
      have nextNormal : next.Normal := head.output_normal normal
      have tailTheory :=
        ReducedTypePresentationListMatchRel.solutions
          tail nextNormal valuation
      have nextSatisfied := (tailTheory.mp outputSatisfied).1
      obtain ⟨runtimeNext, headSuccess, nextState⟩ :=
        reduced_runtime_complete valuation normal nextSatisfied head state
          disjoint.head
      obtain ⟨runtimeOutput, tailSuccess, outputState⟩ :=
        reduced_list_runtime_complete valuation nextNormal outputSatisfied
          tail nextState disjoint.tail
      exact ⟨runtimeOutput, by
        simp only [toLeaTTaAtoms,
          Metta.Minimal.matchReducedList]
        rw [headSuccess]
        exact tailSuccess,
        outputState⟩

end

/-- One published-core-plus-R2 presentation step is realized by repaired
LeaTTa's deterministic type matcher. -/
theorem matchType_complete
    (valuation : String → Atom)
    {substitution outputPresentation : TypeSubst}
    {bindings : Metta.Bindings}
    (normal : substitution.Normal)
    (outputSatisfied : TypeSubstSatisfied valuation outputPresentation)
    {left right : Atom}
    (derivation : CorePlusR2TypePresentationMatchRel
      substitution left right outputPresentation)
    (state : RuntimeValuationState valuation bindings)
    (disjoint : VarsDisjoint left right) :
    ∃ output,
      Metta.Minimal.matchType bindings
          (toLeaTTaAtom left) (toLeaTTaAtom right) = some output ∧
        RuntimeValuationState valuation output := by
  cases derivation with
  | undefinedLeft right =>
      have same :
          (Metta.Atom.sym "%Undefined%" ==
            Metta.Atom.sym "%Undefined%") = true := by decide
      exact ⟨bindings, by simp [Metta.Minimal.matchType,
        toLeaTTaAtom, Atom.undefinedType, same], state⟩
  | undefinedRight left =>
      have same :
          (Metta.Atom.sym "%Undefined%" ==
            Metta.Atom.sym "%Undefined%") = true := by decide
      exact ⟨bindings, by simp [Metta.Minimal.matchType,
        toLeaTTaAtom, Atom.undefinedType, same], state⟩
  | atomLeft right =>
      have same :
          (Metta.Atom.sym "Atom" == Metta.Atom.sym "Atom") = true := by
        decide
      exact ⟨bindings, by simp [Metta.Minimal.matchType,
        toLeaTTaAtom, Atom.atomType, same], state⟩
  | atomRight left =>
      have same :
          (Metta.Atom.sym "Atom" == Metta.Atom.sym "Atom") = true := by
        decide
      exact ⟨bindings, by simp [Metta.Minimal.matchType,
        toLeaTTaAtom, Atom.atomType, same], state⟩
  | reduced leftNotUndefined rightNotUndefined leftNotAtom rightNotAtom reduced =>
      have leftUndefinedBeq :=
        toLeaTTaAtom_beq_undefined_eq_false left leftNotUndefined
      have rightUndefinedBeq :=
        toLeaTTaAtom_beq_undefined_eq_false right rightNotUndefined
      have leftAtomBeq :=
        toLeaTTaAtom_beq_atomType_eq_false left leftNotAtom
      have rightAtomBeq :=
        toLeaTTaAtom_beq_atomType_eq_false right rightNotAtom
      obtain ⟨runtimeOutput, reducedSuccess, outputState⟩ :=
        reduced_runtime_complete valuation normal outputSatisfied
          reduced state disjoint
      exact ⟨runtimeOutput, by
        simpa [Metta.Minimal.matchType, leftUndefinedBeq,
          rightUndefinedBeq, leftAtomBeq, rightAtomBeq] using
            reducedSuccess,
        outputState⟩

/-- A complete presentation argument fold has the conjunction of every
pointwise core-plus-R2 constraint as its exact solution theory. -/
theorem PresentationArgumentListMatchRel.solutions
    {expected actual : List Atom}
    {incoming output : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual incoming output)
    (normal : incoming.Normal)
    (valuation : String → Atom) :
    TypeSubstSatisfied valuation output ↔
      TypeSubstSatisfied valuation incoming ∧
        List.Forall₂
          (CorePlusR2TypeConsistent valuation) expected actual := by
  induction derivation with
  | nil substitution => simp
  | @cons expected actual expecteds actuals incoming next output head tail ih =>
      have nextNormal := head.output_normal normal
      rw [ih nextNormal,
        Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
          head normal valuation]
      constructor
      · rintro ⟨⟨incomingSatisfied, headConsistent⟩, tailConsistent⟩
        exact ⟨incomingSatisfied,
          List.Forall₂.cons headConsistent tailConsistent⟩
      · rintro ⟨incomingSatisfied, allConsistent⟩
        cases allConsistent with
        | cons headConsistent tailConsistent =>
            exact ⟨⟨incomingSatisfied, headConsistent⟩,
              tailConsistent⟩

/-- Every complete, scope-disjoint finite presentation argument fold is
realized by repaired LeaTTa from empty bindings. -/
theorem matchApplicationTypeArguments_complete
    {expected actual : List Atom} {outputPresentation : TypeSubst}
    (derivation : PresentationArgumentListMatchRel
      expected actual [] outputPresentation)
    (disjoint : AtomListsVarsDisjoint expected actual) :
    ∃ output,
      Metta.Minimal.matchApplicationTypeArguments Metta.Bindings.empty
        (toLeaTTaAtoms expected) (toLeaTTaAtoms actual) = some output := by
  let valuation := presentedValuation outputPresentation
  have outputNormal : outputPresentation.Normal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      derivation TypeSubst.normal_empty
  have outputSatisfied : TypeSubstSatisfied valuation outputPresentation :=
    normal_presentedValuation_satisfied outputNormal
  have complete : ∀ {expected actual : List Atom}
      {incoming outputPresentation : TypeSubst}
      {bindings : Metta.Bindings},
      PresentationArgumentListMatchRel
          expected actual incoming outputPresentation →
      incoming.Normal →
      TypeSubstSatisfied valuation outputPresentation →
      RuntimeValuationState valuation bindings →
      AtomListsVarsDisjoint expected actual →
      ∃ output,
        Metta.Minimal.matchApplicationTypeArguments bindings
          (toLeaTTaAtoms expected) (toLeaTTaAtoms actual) = some output ∧
          RuntimeValuationState valuation output := by
    intro expected actual incoming finalPresentation bindings fold
      incomingNormal finalSatisfied state scopes
    induction fold generalizing bindings with
    | nil substitution =>
        exact ⟨bindings, by simp [toLeaTTaAtoms,
          Metta.Minimal.matchApplicationTypeArguments], state⟩
    | @cons expected actual expecteds actuals incoming next output head tail ih =>
        have nextNormal := head.output_normal incomingNormal
        have tailTheory := PresentationArgumentListMatchRel.solutions
          tail nextNormal valuation
        have nextSatisfied := (tailTheory.mp finalSatisfied).1
        obtain ⟨runtimeNext, headSuccess, nextState⟩ :=
          matchType_complete valuation incomingNormal nextSatisfied
            head state scopes.head
        obtain ⟨runtimeOutput, tailSuccess, outputState⟩ :=
          ih nextNormal finalSatisfied nextState scopes.tail
        exact ⟨runtimeOutput, by
          simp only [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments]
          rw [headSuccess]
          exact tailSuccess,
          outputState⟩
  obtain ⟨output, success, _state⟩ :=
    complete derivation TypeSubst.normal_empty outputSatisfied
      (runtimeValuationState_empty valuation) disjoint
  exact ⟨output, success⟩

/-! ## Boundary examples -/

/-- Positive: the empty presentation fold is realized by the empty runtime
fold. -/
theorem empty_fold_complete :
    ∃ output,
      Metta.Minimal.matchApplicationTypeArguments Metta.Bindings.empty
        [] [] = some output := by
  exact ⟨Metta.Bindings.empty, rfl⟩

/-- Negative: completeness deliberately requires disjoint fresh type scopes;
the same variable spelling on both sides does not satisfy that premise. -/
theorem shared_variable_not_disjoint :
    ¬VarsDisjoint (.var "t") (.var "t") := by
  simp [VarsDisjoint, toLeaTTaAtom, Metta.Atom.vars]

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationCompleteness
