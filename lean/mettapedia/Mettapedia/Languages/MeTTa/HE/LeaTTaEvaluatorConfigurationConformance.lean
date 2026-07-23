import Mettapedia.Languages.MeTTa.HE.LeaTTaGroundedDispatchConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalInstructionConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeServiceConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Outcome

/-!
# LeaTTa evaluator configuration boundary

This module contains the data relation consumed by the evaluator simulation.
It deliberately does not identify the two evaluators' internal plans:
upstream uses private `call-native` frames, whereas LeaTTa implements the same
public evaluator directly.

Exactness remains available inside either representation.  Across the
boundary, one coherent permutation relates private variable spellings in
every observable binding solution.  Result atoms are compared after applying
the runtime result binding: the specification may retain `$t` together with
`t = B`, while LeaTTa eagerly emits `B`.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open LeaTTaBranchLocalTypeScanConformance
open LeaTTaMinimalInstructionConformance
open LeaTTaSpecTypeService
open LeaTTaTypeServiceConformance
open LeaTTaTypeConformance
open LeaTTaTypePresentationApplicationExact
open LeaTTaTypePresentationFoldConformance
open Spec.Eval.Minimal
open Spec.Eval.Outcome
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.ScopeObservation
open Spec.Type.RuntimeRefinement

/-- The specification and runtime recognize exactly the same syntactic error
results across the atom carrier.  The extra runtime-only grounded-error
constructor cannot occur in `AtomRuntimeRel`; ordinary specification grounded
values translate through `toLeaTTaGround`, while binding payloads use their
separate opaque constructor. -/
theorem atomRuntimeRel_isError_iff
    {services : Services} {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom) :
    Spec.Eval.IsErrorRel atom ↔ runtimeAtom.isError = true := by
  constructor
  · rintro ⟨tail, rfl⟩
    cases relation with
    | expression _ _ related =>
        cases related with
        | cons head _ =>
            cases head
            all_goals rfl
  · intro runtimeError
    cases relation
    · simp [Metta.Atom.isError] at runtimeError
    · simp [Metta.Atom.isError] at runtimeError
    · rename_i value notPayload
      cases value <;>
        simp [toLeaTTaGround, Metta.Atom.isError] at runtimeError
    · simp [Metta.Atom.isError] at runtimeError
    · rename_i atoms runtimeAtoms related
      cases related with
      | nil => simp [Metta.Atom.isError] at runtimeError
      | cons head tail =>
          cases head
          · rename_i name
            have hname : name = "Error" := by
              by_contra hne
              simp [Metta.Atom.isError, hne] at runtimeError
            subst name
            exact ⟨_, rfl⟩
          · simp [Metta.Atom.isError] at runtimeError
          · rename_i value notPayload
            cases value <;>
              simp [Metta.Atom.isError] at runtimeError
          · simp [Metta.Atom.isError] at runtimeError
          · simp [Metta.Atom.isError] at runtimeError

/-- Equality with a symbol is exact across the atom carrier.  This restricted
law is valid even though grounded host floats make the runtime atom `BEq`
non-lawful in general. -/
theorem atomRuntimeRel_eq_symbol_iff
    {services : Services} {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom) (name : String) :
    atom = .symbol name ↔ runtimeAtom == .sym name := by
  change atom = .symbol name ↔
    Metta.Atom.beq runtimeAtom (.sym name) = true
  cases relation
  · simp [Metta.Atom.beq]
  · simp [Metta.Atom.beq]
  · rename_i value notPayload
    cases value <;>
      simp [Metta.Atom.beq]
  · simp [Metta.Atom.beq]
  · rename_i atoms runtimeAtoms related
    cases related <;>
      simp [Metta.Atom.beq]

/-- Empty-expression recognition is exact across the atom carrier. -/
theorem atomRuntimeRel_isEmpty_iff
    {services : Services} {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom) :
    atom = Atom.empty ↔ runtimeAtom == Metta.Minimal.emptyA := by
  simpa [Atom.empty, Metta.Minimal.emptyA] using
    atomRuntimeRel_eq_symbol_iff relation "Empty"

/-- The undefined type designator is recognized exactly across the atom
carrier. -/
theorem atomRuntimeRel_isUndefined_iff
    {services : Services} {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom) :
    atom = Atom.undefinedType ↔
      runtimeAtom == Metta.Atom.sym "%Undefined%" := by
  simpa [Atom.undefinedType] using
    atomRuntimeRel_eq_symbol_iff relation "%Undefined%"

/-- Intrinsic meta-type atoms translate exactly for every related atom,
including the opaque binding-payload grounded case. -/
theorem atomRuntimeRel_metaType
    {services : Services} {atom metaType : Atom}
    {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom)
    (metaTypeRelation : Spec.Eval.MetaTypeRel atom metaType) :
    toLeaTTaAtom metaType =
      Metta.Atom.typeAtomOfMetaType runtimeAtom.metaType := by
  cases relation <;> cases metaTypeRelation <;>
    simp [toLeaTTaAtom, Atom.symbolType, Atom.variableType,
      Atom.groundedType, Atom.expressionType,
      Metta.Atom.symbolType, Metta.Atom.variableType,
      Metta.Atom.groundedType, Metta.Atom.expressionType,
      Metta.Atom.typeAtomOfMetaType, Metta.Atom.metaType]

/-- Empty/error passthrough is one exact Boolean boundary, rather than two
independently supplied premises in every evaluator constructor proof. -/
theorem atomRuntimeRel_isEmptyOrError_iff
    {services : Services} {atom : Atom} {runtimeAtom : Metta.Atom}
    (relation : AtomRuntimeRel services atom runtimeAtom) :
    Spec.Eval.IsEmptyOrErrorRel atom ↔
      (runtimeAtom == Metta.Minimal.emptyA || runtimeAtom.isError) = true := by
  rw [Bool.or_eq_true]
  exact or_congr (atomRuntimeRel_isEmpty_iff relation)
    (atomRuntimeRel_isError_iff relation)

/-- The published meta-type passthrough disjunction is exactly LeaTTa's
three-way Boolean gate for structurally related source and expected atoms.
The proof does not use a global `LawfulBEq Metta.Atom`; only the symbol and
constructor comparisons forced by the two atom relations are reduced. -/
theorem atomRuntimeRel_typePass_iff
    {services : Services} {atom expectedType metaType : Atom}
    {runtimeAtom runtimeExpected : Metta.Atom}
    (atomRelation : AtomRuntimeRel services atom runtimeAtom)
    (expectedRelation : AtomRuntimeRel services expectedType runtimeExpected)
    (metaTypeRelation : Spec.Eval.MetaTypeRel atom metaType) :
    (expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) ↔
      (runtimeExpected == Metta.Atom.atomType ||
        runtimeExpected ==
          Metta.Atom.typeAtomOfMetaType runtimeAtom.metaType ||
        runtimeAtom.metaType == .variable) = true := by
  change _ ↔
    (Metta.Atom.beq runtimeExpected Metta.Atom.atomType ||
      Metta.Atom.beq runtimeExpected
        (Metta.Atom.typeAtomOfMetaType runtimeAtom.metaType) ||
      Metta.instBEqMetaType.beq runtimeAtom.metaType .variable) = true
  have symbolNotVariable :
      Metta.instBEqMetaType.beq .symbol .variable = false := by decide
  have variableIsVariable :
      Metta.instBEqMetaType.beq .variable .variable = true := by decide
  have groundedNotVariable :
      Metta.instBEqMetaType.beq .grounded .variable = false := by decide
  have expressionNotVariable :
      Metta.instBEqMetaType.beq .expression .variable = false := by decide
  cases atomRelation <;> cases metaTypeRelation <;>
    cases expectedRelation <;>
      simp [Atom.atomType, Atom.symbolType, Atom.variableType,
        Atom.groundedType, Atom.expressionType, toLeaTTaGround,
        Metta.Atom.atomType, Metta.Atom.symbolType,
        Metta.Atom.variableType, Metta.Atom.groundedType,
        Metta.Atom.expressionType, Metta.Atom.typeAtomOfMetaType,
        Metta.Atom.metaType, Metta.Atom.beq, symbolNotVariable,
        variableIsVariable, groundedNotVariable, expressionNotVariable]

/-- Structural atom correspondence up to one coherent private alpha
presentation.  Constructors and public symbols remain exact; only variable
spellings may differ. -/
def AlphaAtomRuntimeRel (services : Services)
    (atom : Atom) (runtimeAtom : Metta.Atom) : Prop :=
  ∃ observed,
    ObservedTypeAlphaRel atom observed ∧
      AtomRuntimeRel services observed runtimeAtom

/-- One result atom after accounting for its specification presentation and
the runtime binding that will be used to observe it.  Both atoms are
instantiated by the same runtime result binding before comparison, so this
also covers a runtime that emits an already-instantiated result. -/
def EvaluatorAtomObservationRel (services : Services)
    (presentation : TypeSubst) (runtimeBindings : Metta.Bindings)
    (atom : Atom) (runtimeAtom : Metta.Atom) : Prop :=
  ∃ observed presented,
    ObservedTypeAlphaRel (presentation.apply atom) observed ∧
    AtomRuntimeRel services observed presented ∧
    Metta.instantiate runtimeBindings presented =
      Metta.instantiate runtimeBindings runtimeAtom

/-- Structural observation for fields embedded in diagnostics.  Diagnostic
payloads are already-constructed printed syntax, not evaluator values: they
are decoded directly and compared up to private alpha, without applying the
result binding presentation a second time.  This keeps literal public fields
literal while permitting only generated type-variable spellings to differ. -/
def StructuralAtomObservationRel
    (_presentation : TypeSubst) (_runtimeBindings : Metta.Bindings)
    (atom : Atom) (runtimeAtom : Metta.Atom) : Prop :=
  ObservedTypeAlphaRel atom (fromLeaTTaAtom runtimeAtom)

/-- Context-specific observation of structured evaluator diagnostics.
Ordinary evaluator atoms keep `AtomRuntimeRel`; only diagnostic fields use
the structural readout above. -/
inductive EvaluatorDiagnosticAtomObservationRel (services : Services)
    (presentation : TypeSubst) (runtimeBindings : Metta.Bindings) :
    Atom → Metta.Atom → Prop where
  | incorrectNumberOfArguments {source : Atom}
      {runtimeSource : Metta.Atom} :
      EvaluatorAtomObservationRel services presentation runtimeBindings
        source runtimeSource →
      EvaluatorDiagnosticAtomObservationRel services presentation
        runtimeBindings
        (mkError source .incorrectNumberOfArguments)
        (.expr [.sym "Error", runtimeSource,
          .sym "IncorrectNumberOfArguments"])
  | badArgType {source expected actual : Atom} {position : Nat}
      {runtimeSource runtimeExpected runtimeActual : Metta.Atom}
      {runtimePosition : Nat} :
      position = runtimePosition →
      EvaluatorAtomObservationRel services presentation runtimeBindings
        source runtimeSource →
      StructuralAtomObservationRel presentation runtimeBindings
        expected runtimeExpected →
      StructuralAtomObservationRel presentation runtimeBindings
        actual runtimeActual →
      EvaluatorDiagnosticAtomObservationRel services presentation
        runtimeBindings
        (mkError source (.badArgType position expected actual))
        (.expr [.sym "Error", runtimeSource,
          .expr [.sym "BadArgType",
            .gnd (.int (Int.ofNat runtimePosition)),
            runtimeExpected, runtimeActual]])
  | badType {source expected actual : Atom}
      {runtimeSource runtimeExpected runtimeActual : Metta.Atom} :
      EvaluatorAtomObservationRel services presentation runtimeBindings
        source runtimeSource →
      StructuralAtomObservationRel presentation runtimeBindings
        expected runtimeExpected →
      StructuralAtomObservationRel presentation runtimeBindings
        actual runtimeActual →
      EvaluatorDiagnosticAtomObservationRel services presentation
        runtimeBindings (mkError source (.badType expected actual))
        (Metta.Minimal.badTypeAtom
          runtimeSource runtimeExpected runtimeActual)

/-- A specification binding result and one runtime binding result agree
through an exact finite presentation on the specification side and scoped
model equivalence across the implementation boundary.

Exactness is deliberately intra-side: `specSolutions` identifies the finite
presentation with the specification binding theory.  Runtime private names
are compared only through `ScopedTypePresentationSimulationState`; no
canonical-resolver spelling is imposed across independently freshened
implementations. -/
def ScopedEvaluatorBindingRuntimeRel
    (scope : List String) (specBindings : Bindings)
    (runtimeBindings : Metta.Bindings) : Prop :=
  ∃ presentation : TypeSubst,
    (∀ valuation,
      TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation specBindings) ∧
    ScopedTypePresentationSimulationState
      scope presentation runtimeBindings

namespace ScopedEvaluatorBindingRuntimeRel

/-- An exact presentation simulation is the reflexive scoped case. -/
theorem ofExact
    {scope : List String} {presentation : TypeSubst}
    {specBindings : Bindings} {runtimeBindings : Metta.Bindings}
    (state : TypePresentationSimulationState
      presentation specBindings runtimeBindings) :
    ScopedEvaluatorBindingRuntimeRel scope specBindings runtimeBindings :=
  ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state⟩

/-- Binding observation restricts contravariantly with its public scope. -/
theorem mono
    {large small : List String} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    (relation : ScopedEvaluatorBindingRuntimeRel
      large specBindings runtimeBindings)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedEvaluatorBindingRuntimeRel small specBindings runtimeBindings := by
  rcases relation with ⟨presentation, specSolutions, runtimeState⟩
  exact ⟨presentation, specSolutions, runtimeState.mono subset⟩

end ScopedEvaluatorBindingRuntimeRel

/-- A successful candidate scan exposes the selected runtime binding theory
as a scoped realization of the complete specification applicability output.
The exact solution equation is supplied by the singleton classifier that
produced the scan success; consumers do not reconstruct it from a bare
presentation extension. -/
theorem FunctionCandidateScanOutcomeRuntimeRel.successBinding
    {observationScope : List String} {expression : Atom}
    {incoming output : Bindings} {policy : Spec.Eval.SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : FunctionCandidateScanOutcomeRuntimeRel observationScope
      expression incoming (.success policy output) (.selected runtime)) :
    ScopedEvaluatorBindingRuntimeRel observationScope output
      runtime.typeBindings := by
  cases relation with
  | success coherent _extension solutions =>
      exact ⟨_, solutions, coherent.scopedPresentation⟩

/-- Present one semantic core-plus-R2 match from a normal finite input
presentation.  This is the executable-independent part of
`TypePresentationSimulationState.presentCorePlusR2`: consumers that compare
two specification branches need no runtime state for the input side. -/
theorem TypeBindingPresentationRel.presentCorePlusR2
    {presentation : TypeSubst} {bindings output : Bindings}
    {expected actual : Atom}
    (state : TypeBindingPresentationRel presentation bindings)
    (derivation : CorePlusR2TypeMatchRel
      expected actual bindings output) :
    ∃ presentationOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        presentationOutput.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentationOutput ↔
            TypeBindingSatisfied valuation output := by
  obtain ⟨valuation, outputSatisfied⟩ := derivation.satisfiable
  obtain ⟨inputSatisfied, consistent⟩ :=
    (derivation.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.solutions valuation).mpr inputSatisfied
  obtain ⟨presentationOutput, presentationMatch,
      outputNormal, _outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual consistent
  refine ⟨presentationOutput, presentationMatch, outputNormal, ?_⟩
  intro otherValuation
  rw [CorePlusR2TypePresentationMatchRel.solutions
        presentationMatch state.normal otherValuation,
    state.solutions otherValuation, ← derivation.solutions otherValuation]

/-- Equivalent one-step constraint theories preserve existence of a semantic
match.  The output binding record is the canonical carrier of the recovered
finite presentation; no runtime spelling is selected. -/
theorem typeBindingPresentationRel_constraintMatch_exists
    {scope : List String}
    {leftPresentation rightPresentation : TypeSubst}
    {leftBindings rightBindings leftOutput : Bindings}
    {leftExpected leftActual rightExpected rightActual : Atom}
    (leftState : TypeBindingPresentationRel
      leftPresentation leftBindings)
    (rightState : TypeBindingPresentationRel
      rightPresentation rightBindings)
    (constraints : TypeConstraintTheoryEquivAt scope
      leftPresentation leftExpected leftActual
      rightPresentation rightExpected rightActual)
    (leftMatch : CorePlusR2TypeMatchRel
      leftExpected leftActual leftBindings leftOutput) :
    ∃ rightOutput,
      CorePlusR2TypeMatchRel
        rightExpected rightActual rightBindings rightOutput := by
  obtain ⟨leftModel, leftOutputSatisfied⟩ := leftMatch.satisfiable
  obtain ⟨leftBindingsSatisfied, leftConsistent⟩ :=
    (leftMatch.solutions leftModel).mp leftOutputSatisfied
  have leftPresentationSatisfied :
      TypeSubstSatisfied leftModel leftPresentation :=
    (leftState.solutions leftModel).mpr leftBindingsSatisfied
  obtain ⟨rightModel, rightPresentationSatisfied,
      rightConsistent, _agrees⟩ :=
    constraints.leftToRight leftModel leftPresentationSatisfied
      leftConsistent
  obtain ⟨rightOutputPresentation, rightPresentationMatch,
      rightOutputNormal, rightOutputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      rightState.normal rightPresentationSatisfied
        rightExpected rightActual rightConsistent
  let rightOutput := typeSubstAsBindings rightOutputPresentation
  refine ⟨rightOutput, ?_⟩
  constructor
  · exact ⟨rightModel,
      (typeBindingSatisfied_asBindings_iff
        rightModel rightOutputPresentation).mpr rightOutputSatisfied⟩
  · intro valuation
    rw [typeBindingSatisfied_asBindings_iff,
      CorePlusR2TypePresentationMatchRel.solutions
        rightPresentationMatch rightState.normal valuation,
      rightState.solutions valuation]

/-- Two semantic matches whose complete constraint theories agree at a
public scope have output presentations related at that scope.  Exactness is
retained separately on each specification side; only the comparison with the
selected runtime presentation is scoped. -/
theorem typeBindingPresentationRel_constraintOutputsScoped
    {scope : List String}
    {leftPresentation rightPresentation selectedPresentation : TypeSubst}
    {leftBindings rightBindings leftOutput rightOutput : Bindings}
    {runtimeOutput : Metta.Bindings}
    {leftExpected leftActual rightExpected rightActual : Atom}
    (leftState : TypeBindingPresentationRel
      leftPresentation leftBindings)
    (rightState : TypeBindingPresentationRel
      rightPresentation rightBindings)
    (selectedState : TypePresentationSimulationState selectedPresentation
      rightOutput runtimeOutput)
    (leftMatch : CorePlusR2TypeMatchRel
      leftExpected leftActual leftBindings leftOutput)
    (rightMatch : CorePlusR2TypeMatchRel
      rightExpected rightActual rightBindings rightOutput)
    (constraints : TypeConstraintTheoryEquivAt scope
      leftPresentation leftExpected leftActual
      rightPresentation rightExpected rightActual) :
    ∃ leftOutputPresentation,
      (∀ valuation,
        TypeSubstSatisfied valuation leftOutputPresentation ↔
          TypeBindingSatisfied valuation leftOutput) ∧
      ScopedTypePresentationSimulationState
        scope leftOutputPresentation runtimeOutput := by
  obtain ⟨leftOutputPresentation, leftPresentationMatch,
      leftOutputNormal, leftSolutions⟩ :=
    TypeBindingPresentationRel.presentCorePlusR2 leftState leftMatch
  obtain ⟨rightOutputPresentation, rightPresentationMatch,
      rightOutputNormal, rightSolutions⟩ :=
    TypeBindingPresentationRel.presentCorePlusR2 rightState rightMatch
  have outputsEquiv : TypePresentationTheoryEquivAt scope
      leftOutputPresentation rightOutputPresentation :=
    CorePlusR2TypePresentationMatchRel.outputTheoryEquivAt
      leftState.normal rightState.normal leftPresentationMatch
        rightPresentationMatch constraints
  have selectedEquiv : TypePresentationTheoryEquivAt scope
      rightOutputPresentation selectedPresentation := by
    constructor
    · intro valuation satisfied
      exact ⟨valuation,
        (selectedState.specSolutions valuation).mpr
          ((rightSolutions valuation).mp satisfied),
        fun _ _ => rfl⟩
    · intro valuation satisfied
      exact ⟨valuation,
        (rightSolutions valuation).mpr
          ((selectedState.specSolutions valuation).mp satisfied),
        fun _ _ => rfl⟩
  exact ⟨leftOutputPresentation, leftSolutions,
    ⟨leftOutputNormal, selectedPresentation, rightOutput, selectedState,
      outputsEquiv.trans selectedEquiv⟩⟩

/-- Declaration-ordered first-success scans transport across any pointwise
equivalence of their complete input-plus-constraint theories.  This is the
generic order-preserving induction; private-candidate and selected-arrow
alpha transports are instances rather than separate scan proofs. -/
theorem FirstTypeCastSuccessRel.outputsScoped_of_constraints
    {scope : List String}
    {leftPresentation rightPresentation selectedPresentation : TypeSubst}
    {leftBindings rightBindings leftOutput rightOutput : Bindings}
    {runtimeOutput : Metta.Bindings}
    {leftExpected rightExpected : Atom}
    {leftCandidates rightCandidates : List Atom}
    (leftState : TypeBindingPresentationRel
      leftPresentation leftBindings)
    (rightState : TypeBindingPresentationRel
      rightPresentation rightBindings)
    (selectedState : TypePresentationSimulationState selectedPresentation
      rightOutput runtimeOutput)
    (candidateConstraints : List.Forall₂ (fun leftActual rightActual =>
      TypeConstraintTheoryEquivAt scope
        leftPresentation leftExpected leftActual
        rightPresentation rightExpected rightActual)
      leftCandidates rightCandidates)
    (leftSuccess : FirstTypeCastSuccessRel
      leftExpected leftBindings leftCandidates leftOutput)
    (rightSuccess : FirstTypeCastSuccessRel
      rightExpected rightBindings rightCandidates rightOutput) :
    ∃ leftOutputPresentation,
      (∀ valuation,
        TypeSubstSatisfied valuation leftOutputPresentation ↔
          TypeBindingSatisfied valuation leftOutput) ∧
      ScopedTypePresentationSimulationState
        scope leftOutputPresentation runtimeOutput := by
  induction candidateConstraints generalizing leftOutput rightOutput with
  | nil => cases leftSuccess
  | @cons leftActual rightActual leftCandidates rightCandidates
      headConstraints tailConstraints inductionHypothesis =>
      cases leftSuccess with
      | head leftMatch =>
          cases rightSuccess with
          | head rightMatch =>
              exact typeBindingPresentationRel_constraintOutputsScoped
                leftState rightState selectedState leftMatch rightMatch
                  headConstraints
          | tail rightFailure _rightTail =>
              obtain ⟨competingOutput, competingMatch⟩ :=
                typeBindingPresentationRel_constraintMatch_exists
                  leftState rightState headConstraints leftMatch
              exact (rightFailure competingOutput competingMatch).elim
      | tail leftFailure leftTail =>
          cases rightSuccess with
          | head rightMatch =>
              obtain ⟨competingOutput, competingMatch⟩ :=
                typeBindingPresentationRel_constraintMatch_exists
                  rightState leftState headConstraints.symm rightMatch
              exact (leftFailure competingOutput competingMatch).elim
          | tail _rightFailure rightTail =>
              exact inductionHypothesis selectedState leftTail rightTail

/-- A declaration-ordered successful cast transports from the right family
to the left family under pointwise constraint-theory equivalence.  The
selected left output is exact for its native derivation; only its comparison
with the runtime-selected right output is scoped. -/
theorem FirstTypeCastSuccessRel.exists_left_outputsScoped_of_constraints
    {scope : List String}
    {leftPresentation rightPresentation selectedPresentation : TypeSubst}
    {leftBindings rightBindings rightOutput : Bindings}
    {runtimeOutput : Metta.Bindings}
    {leftExpected rightExpected : Atom}
    {leftCandidates rightCandidates : List Atom}
    (leftState : TypeBindingPresentationRel
      leftPresentation leftBindings)
    (rightState : TypeBindingPresentationRel
      rightPresentation rightBindings)
    (selectedState : TypePresentationSimulationState selectedPresentation
      rightOutput runtimeOutput)
    (candidateConstraints : List.Forall₂ (fun leftActual rightActual =>
      TypeConstraintTheoryEquivAt scope
        leftPresentation leftExpected leftActual
        rightPresentation rightExpected rightActual)
      leftCandidates rightCandidates)
    (rightSuccess : FirstTypeCastSuccessRel
      rightExpected rightBindings rightCandidates rightOutput) :
    ∃ leftOutput leftOutputPresentation,
      FirstTypeCastSuccessRel
          leftExpected leftBindings leftCandidates leftOutput ∧
        (∀ valuation,
          TypeSubstSatisfied valuation leftOutputPresentation ↔
            TypeBindingSatisfied valuation leftOutput) ∧
        ScopedTypePresentationSimulationState
          scope leftOutputPresentation runtimeOutput := by
  induction candidateConstraints generalizing rightOutput with
  | nil => cases rightSuccess
  | @cons leftActual rightActual leftCandidates rightCandidates
      headConstraints tailConstraints inductionHypothesis =>
      cases rightSuccess with
      | head rightMatch =>
          obtain ⟨leftOutput, leftMatch⟩ :=
            typeBindingPresentationRel_constraintMatch_exists
              rightState leftState headConstraints.symm rightMatch
          obtain ⟨leftOutputPresentation, leftSolutions, outputState⟩ :=
            typeBindingPresentationRel_constraintOutputsScoped
              leftState rightState selectedState leftMatch rightMatch
                headConstraints
          exact ⟨leftOutput, leftOutputPresentation,
            .head leftMatch, leftSolutions, outputState⟩
      | tail rightHeadFailure rightTail =>
          obtain ⟨leftOutput, leftOutputPresentation, leftTail,
              leftSolutions, outputState⟩ :=
            inductionHypothesis selectedState rightTail
          have leftHeadFailure : ∀ competingOutput,
              ¬CorePlusR2TypeMatchRel leftExpected leftActual
                leftBindings competingOutput := by
            intro competingOutput competingMatch
            obtain ⟨rightCompetingOutput, rightCompetingMatch⟩ :=
              typeBindingPresentationRel_constraintMatch_exists
                leftState rightState headConstraints competingMatch
            exact rightHeadFailure rightCompetingOutput rightCompetingMatch
          exact ⟨leftOutput, leftOutputPresentation,
            .tail leftHeadFailure leftTail, leftSolutions, outputState⟩

/-- Existence of a native core-plus-R2 match is invariant under replacing one
private candidate by a sibling presentation fresh from the incoming theory
and expected type.  The output binding record is constructed from the exact
finite presentation; no executable matcher or choice principle is used. -/
theorem typePresentationSimulationState_privateCandidateMatch_exists
    {inputPresentation : TypeSubst} {incoming leftOutput : Bindings}
    {runtimeIncoming : Metta.Bindings} {fixedScope : List String}
    {expected leftActual rightActual : Atom}
    (inputState : TypePresentationSimulationState inputPresentation
      incoming runtimeIncoming)
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ fixedScope)
    (expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (leftMatch : CorePlusR2TypeMatchRel
      expected leftActual incoming leftOutput) :
    ∃ rightOutput,
      CorePlusR2TypeMatchRel
        expected rightActual incoming rightOutput := by
  obtain ⟨leftModel, leftOutputSatisfied⟩ := leftMatch.satisfiable
  obtain ⟨leftIncomingSatisfied, leftConsistent⟩ :=
    (leftMatch.solutions leftModel).mp leftOutputSatisfied
  have leftPresentationSatisfied :
      TypeSubstSatisfied leftModel inputPresentation :=
    (inputState.specSolutions leftModel).mpr leftIncomingSatisfied
  obtain ⟨rightModel, rightPresentationSatisfied,
      rightConsistent, _agrees⟩ :=
    alpha.transport_model inputCovered expectedCovered
      (observationScope := []) (by simp) leftModel
        leftPresentationSatisfied leftConsistent
  obtain ⟨rightPresentation, rightPresentationMatch,
      _rightNormal, _rightSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      inputState.normal rightPresentationSatisfied expected rightActual
        rightConsistent
  refine ⟨typeSubstAsBindings rightPresentation, ?_⟩
  constructor
  · obtain ⟨valuation, satisfied⟩ :=
      corePlusR2_output_satisfiable rightPresentationMatch inputState.normal
    exact ⟨valuation,
      (typeBindingSatisfied_asBindings_iff
        valuation rightPresentation).mpr satisfied⟩
  · intro valuation
    rw [typeBindingSatisfied_asBindings_iff,
      CorePlusR2TypePresentationMatchRel.solutions
        rightPresentationMatch inputState.normal valuation,
      inputState.specSolutions valuation]

/-- Two native type matches against private-alpha sibling candidates yield
output presentations that agree at every declared public observation.  The
left presentation is exact for the left specification output; the selected
right presentation remains exact for the runtime output.  Only their
cross-boundary comparison is scoped.

This is the reusable completeness bridge for relational type-candidate
preparation: it never identifies independently generated private names. -/
theorem typePresentationSimulationState_privateCandidateOutputsScoped
    {inputPresentation selectedPresentation : TypeSubst}
    {incoming leftOutput rightOutput : Bindings}
    {runtimeIncoming runtimeOutput : Metta.Bindings}
    {fixedScope observationScope : List String}
    {expected leftActual rightActual : Atom}
    (inputState : TypePresentationSimulationState inputPresentation
      incoming runtimeIncoming)
    (selectedState : TypePresentationSimulationState selectedPresentation
      rightOutput runtimeOutput)
    (alpha : PrivateCandidateAlphaRel fixedScope leftActual rightActual)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ fixedScope)
    (expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (observationCovered : ∀ name,
      name ∈ observationScope → name ∈ fixedScope)
    (leftMatch : CorePlusR2TypeMatchRel
      expected leftActual incoming leftOutput)
    (rightMatch : CorePlusR2TypeMatchRel
      expected rightActual incoming rightOutput) :
    ∃ leftPresentation,
      (∀ valuation,
        TypeSubstSatisfied valuation leftPresentation ↔
          TypeBindingSatisfied valuation leftOutput) ∧
      ScopedTypePresentationSimulationState
        observationScope leftPresentation runtimeOutput := by
  have constraints : TypeConstraintTheoryEquivAt observationScope
      inputPresentation expected leftActual
      inputPresentation expected rightActual :=
    TypeConstraintTheoryEquivAt.of_privateCandidateAlpha alpha
      inputCovered expectedCovered observationCovered
  exact typeBindingPresentationRel_constraintOutputsScoped
    (LeaTTaTypeServiceConformance.TypePresentationSimulationState.toTypeBindingPresentationRel
      inputState)
      (LeaTTaTypeServiceConformance.TypePresentationSimulationState.toTypeBindingPresentationRel
        inputState) selectedState
        leftMatch rightMatch constraints

/-- Two lawful recoveries and freshenings of one prepared type list yield
pointwise private-alpha sibling candidate families.  Functionality is used
only to align the prepared source; order and multiplicity are retained by
`Forall₂`. -/
theorem preparedTypeCastCandidateFamilies_privateAlpha
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {atom expectedType : Atom} {bindings : Bindings}
    {leftSources rightSources leftCandidates rightCandidates : List Atom}
    (leftPresent : PreparedPackagesPresent
      oracle space atom leftSources)
    (rightPresent : PreparedPackagesPresent
      oracle space atom rightSources)
    (leftVariants : ArgumentAlphaVariantsRel
      (typeServicePrivateAvoid space atom expectedType bindings)
      leftSources leftCandidates)
    (rightVariants : ArgumentAlphaVariantsRel
      (typeServicePrivateAvoid space atom expectedType bindings)
      rightSources rightCandidates) :
    PrivateCandidateFamilyAlphaRel
      (typeServicePrivateAvoid space atom expectedType bindings)
      leftCandidates rightCandidates := by
  have sourcesAlpha : List.Forall₂ ObservedTypeAlphaRel
      leftSources rightSources :=
    leftPresent.alpha_unique functional index rightPresent
  have rightVariantsFromLeft : ArgumentAlphaVariantsRel
      (typeServicePrivateAvoid space atom expectedType bindings)
      leftSources rightCandidates :=
    ArgumentAlphaVariantsRel.transport_left sourcesAlpha rightVariants
  exact privateCandidateFamilyAlpha_of_variants
    (argumentAlphaVariantsRel_toForall₂ leftVariants)
    (argumentAlphaVariantsRel_toForall₂ rightVariantsFromLeft)

/-- Pointwise private-alpha correspondence preserves membership from the
left candidate family to a sibling at the same list position on the right. -/
theorem PrivateCandidateFamilyAlphaRel.exists_right_of_mem_left
    {fixedScope : List String} {leftCandidates rightCandidates : List Atom}
    (relation : PrivateCandidateFamilyAlphaRel
      fixedScope leftCandidates rightCandidates) :
    ∀ {left}, left ∈ leftCandidates →
      ∃ right, right ∈ rightCandidates ∧
        PrivateCandidateAlphaRel fixedScope left right := by
  intro left member
  induction relation with
  | nil => simp at member
  | @cons leftHead rightHead leftTail rightTail head tail
      inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨rightHead, by simp, head⟩
      · obtain ⟨right, rightMember, related⟩ :=
          inductionHypothesis tailMember
        exact ⟨right, by simp [rightMember], related⟩

/-- Declaration-ordered first-success scans over pointwise private-alpha
candidate families commit at the same position.  Their selected output
theories are exact within each specification derivation and scoped-equivalent
at the runtime boundary. -/
theorem FirstTypeCastSuccessRel.outputsScoped
    {inputPresentation selectedPresentation : TypeSubst}
    {incoming leftOutput rightOutput : Bindings}
    {runtimeIncoming runtimeOutput : Metta.Bindings}
    {fixedScope observationScope : List String}
    {expected : Atom} {leftCandidates rightCandidates : List Atom}
    (inputState : TypePresentationSimulationState inputPresentation
      incoming runtimeIncoming)
    (selectedState : TypePresentationSimulationState selectedPresentation
      rightOutput runtimeOutput)
    (candidatesAlpha : PrivateCandidateFamilyAlphaRel
      fixedScope leftCandidates rightCandidates)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ fixedScope)
    (expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (observationCovered : ∀ name,
      name ∈ observationScope → name ∈ fixedScope)
    (leftSuccess : FirstTypeCastSuccessRel
      expected incoming leftCandidates leftOutput)
    (rightSuccess : FirstTypeCastSuccessRel
      expected incoming rightCandidates rightOutput) :
    ∃ leftPresentation,
      (∀ valuation,
        TypeSubstSatisfied valuation leftPresentation ↔
          TypeBindingSatisfied valuation leftOutput) ∧
      ScopedTypePresentationSimulationState
        observationScope leftPresentation runtimeOutput := by
  induction candidatesAlpha generalizing leftOutput rightOutput with
  | nil => cases leftSuccess
  | @cons leftActual rightActual leftCandidates rightCandidates
      headAlpha tailAlpha inductionHypothesis =>
      cases leftSuccess with
      | head leftMatch =>
          cases rightSuccess with
          | head rightMatch =>
              exact typePresentationSimulationState_privateCandidateOutputsScoped
                inputState selectedState headAlpha inputCovered expectedCovered
                  observationCovered leftMatch rightMatch
          | tail rightFailure _rightTail =>
              obtain ⟨competingOutput, competingMatch⟩ :=
                typePresentationSimulationState_privateCandidateMatch_exists
                  inputState headAlpha inputCovered expectedCovered leftMatch
              exact (rightFailure competingOutput competingMatch).elim
      | tail leftFailure leftTail =>
          cases rightSuccess with
          | head rightMatch =>
              have reverseAlpha : PrivateCandidateAlphaRel
                  fixedScope rightActual leftActual := by
                rcases headAlpha with ⟨source, leftVariant, rightVariant⟩
                exact ⟨source, rightVariant, leftVariant⟩
              obtain ⟨competingOutput, competingMatch⟩ :=
                typePresentationSimulationState_privateCandidateMatch_exists
                  inputState reverseAlpha inputCovered expectedCovered
                    rightMatch
              exact (leftFailure competingOutput competingMatch).elim
          | tail _rightFailure rightTail =>
              exact inductionHypothesis selectedState leftTail rightTail

/-- A first-success scan on one private-alpha presentation rules out an
all-failure scan on its sibling presentation. -/
theorem FirstTypeCastSuccessRel.not_allFailures_of_privateAlpha
    {inputPresentation : TypeSubst} {incoming output : Bindings}
    {runtimeIncoming : Metta.Bindings} {fixedScope : List String}
    {expected : Atom} {leftCandidates rightCandidates : List Atom}
    (inputState : TypePresentationSimulationState inputPresentation
      incoming runtimeIncoming)
    (candidatesAlpha : PrivateCandidateFamilyAlphaRel
      fixedScope leftCandidates rightCandidates)
    (inputCovered : ∀ name,
      name ∈ specBindingVars (⟨inputPresentation, []⟩ : Bindings) →
        name ∈ fixedScope)
    (expectedCovered : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (success : FirstTypeCastSuccessRel
      expected incoming leftCandidates output)
    (allFailed : ∀ candidateType ∈ rightCandidates, ∀ candidate,
      ¬CorePlusR2TypeMatchRel
        expected candidateType incoming candidate) : False := by
  induction candidatesAlpha generalizing output with
  | nil => cases success
  | @cons leftActual rightActual leftCandidates rightCandidates
      headAlpha _tailAlpha inductionHypothesis =>
      cases success with
      | head leftMatch =>
          obtain ⟨rightOutput, rightMatch⟩ :=
            typePresentationSimulationState_privateCandidateMatch_exists
              inputState headAlpha inputCovered expectedCovered leftMatch
          exact allFailed rightActual (by simp) rightOutput rightMatch
      | tail _leftFailure leftTail =>
          apply inductionHypothesis leftTail
          intro candidateType member candidate
          exact allFailed candidateType (by simp [member]) candidate

/-- One specification result and one LeaTTa result agree at a finite public
scope.  The specification atom is first interpreted by the exact finite
presentation of its result binding.  Only residual private variables may then
change spelling, and the presented and emitted runtime atoms must become equal
under the runtime result binding.  This preserves the dependent case
`$t, t = B` versus the eagerly emitted `B` without fixing a private gensym
spelling. -/
def ScopedEvaluatorResultRuntimeRel
    (services : Services) (scope : List String)
    (result : ResultPair) (runtimeResult : Metta.Atom × Metta.Bindings) : Prop :=
  ∃ presentation : TypeSubst,
    (∀ valuation,
      TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation result.2) ∧
    ScopedTypePresentationSimulationState
      scope presentation runtimeResult.2 ∧
    (EvaluatorAtomObservationRel services presentation runtimeResult.2
        result.1 runtimeResult.1 ∨
      EvaluatorDiagnosticAtomObservationRel services presentation
        runtimeResult.2 result.1 runtimeResult.1) ∧
    (Spec.Eval.IsErrorRel result.1 ↔
      runtimeResult.1.isError = true)

namespace ScopedEvaluatorResultRuntimeRel

/-- Project the binding-state component without reopening the atom witness. -/
theorem bindingState
    {services : Services} {scope : List String}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ScopedEvaluatorResultRuntimeRel services scope
      result runtimeResult) :
    ScopedEvaluatorBindingRuntimeRel scope result.2 runtimeResult.2 := by
  rcases relation with
    ⟨presentation, specSolutions, runtimeState, _atomPresentation,
      _errorShape⟩
  exact ⟨presentation, specSolutions, runtimeState⟩

/-- Error classification is an observable part of the result boundary.
Post-instantiation atom equality alone is insufficient here: the runtime
success filter inspects the emitted atom before applying its binding. -/
theorem isError_iff
    {services : Services} {scope : List String}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ScopedEvaluatorResultRuntimeRel services scope
      result runtimeResult) :
    Spec.Eval.IsErrorRel result.1 ↔ runtimeResult.1.isError = true := by
  rcases relation with
    ⟨_presentation, _specSolutions, _runtimeState, _atomPresentation,
      errorShape⟩
  exact errorShape

/-- Observation can be restricted to any smaller public scope without
changing the coherent atom witness. -/
theorem mono
    {services : Services} {large small : List String}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (relation : ScopedEvaluatorResultRuntimeRel services large
      result runtimeResult)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ScopedEvaluatorResultRuntimeRel services small
      result runtimeResult := by
  rcases relation with
    ⟨presentation, specSolutions, runtimeState, atomPresentation,
      errorShape⟩
  exact ⟨presentation, specSolutions, runtimeState.mono subset,
    atomPresentation, errorShape⟩

/-- Exact structural translation is a diagnostic observation under every
result presentation because diagnostic fields are not re-instantiated. -/
theorem structuralAtom
    {presentation : TypeSubst}
    {runtimeBindings : Metta.Bindings}
    (atom : Atom) :
    StructuralAtomObservationRel presentation runtimeBindings atom
      (toLeaTTaAtom atom) := by
  unfold StructuralAtomObservationRel
  rw [fromLeaTTaAtom_toLeaTTaAtom]

/-- A private-alpha sibling is observed structurally under every result
presentation.  Its freshness scope remains explicit in the alpha witness;
the diagnostic readout itself performs no binding substitution. -/
theorem structuralPrivateCandidate
    {presentation : TypeSubst}
    {runtimeBindings : Metta.Bindings} {fixedScope : List String}
    {left right : Atom}
    (alpha : PrivateCandidateAlphaRel fixedScope left right) :
    StructuralAtomObservationRel presentation runtimeBindings left
      (toLeaTTaAtom right) := by
  unfold StructuralAtomObservationRel
  rw [fromLeaTTaAtom_toLeaTTaAtom]
  exact PrivateCandidateAlphaRel.toObservedTypeAlphaRel alpha

/-- Construct a structured `BadType` result without treating its expected
and actual fields as semantic grounded payloads. -/
theorem ofBadType
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {source expected actual : Atom}
    {runtimeSource runtimeExpected runtimeActual : Metta.Atom}
    (state : TypePresentationSimulationState
      presentation specBindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings source runtimeSource)
    (expectedObservation : StructuralAtomObservationRel presentation
      runtimeBindings expected runtimeExpected)
    (actualObservation : StructuralAtomObservationRel presentation
      runtimeBindings actual runtimeActual) :
    ScopedEvaluatorResultRuntimeRel services scope
      (mkError source (.badType expected actual), specBindings)
      (Metta.Minimal.badTypeAtom runtimeSource runtimeExpected runtimeActual,
        runtimeBindings) := by
  refine ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state, Or.inr ?_, ?_⟩
  · exact EvaluatorDiagnosticAtomObservationRel.badType sourceObservation
      expectedObservation actualObservation
  · simp [Spec.Eval.IsErrorRel, mkError, Atom.error,
      Metta.Minimal.badTypeAtom, Metta.Atom.isError]

/-- Construct the literal arity diagnostic while retaining the same scoped
binding presentation as the source expression. -/
theorem ofIncorrectNumberOfArguments
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {source : Atom} {runtimeSource : Metta.Atom}
    (state : TypePresentationSimulationState
      presentation specBindings runtimeBindings)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings source runtimeSource) :
    ScopedEvaluatorResultRuntimeRel services scope
      (mkError source .incorrectNumberOfArguments, specBindings)
      (.expr [.sym "Error", runtimeSource,
          .sym "IncorrectNumberOfArguments"], runtimeBindings) := by
  refine ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state, Or.inr ?_, ?_⟩
  · exact EvaluatorDiagnosticAtomObservationRel.incorrectNumberOfArguments
      sourceObservation
  · simp [Spec.Eval.IsErrorRel, mkError, Atom.error,
      Metta.Atom.isError]

/-- Construct a field-wise argument diagnostic.  The argument index is
literal; only the two type fields pass through structural presentation
observation. -/
theorem ofBadArgType
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings}
    {source expected actual : Atom} {position : Nat}
    {runtimeSource runtimeExpected runtimeActual : Metta.Atom}
    {runtimePosition : Nat}
    (state : TypePresentationSimulationState
      presentation specBindings runtimeBindings)
    (positionEquation : position = runtimePosition)
    (sourceObservation : EvaluatorAtomObservationRel services presentation
      runtimeBindings source runtimeSource)
    (expectedObservation : StructuralAtomObservationRel presentation
      runtimeBindings expected runtimeExpected)
    (actualObservation : StructuralAtomObservationRel presentation
      runtimeBindings actual runtimeActual) :
    ScopedEvaluatorResultRuntimeRel services scope
      (mkError source (.badArgType position expected actual), specBindings)
      (.expr [.sym "Error", runtimeSource,
          .expr [.sym "BadArgType",
            .gnd (.int (Int.ofNat runtimePosition)),
            runtimeExpected, runtimeActual]], runtimeBindings) := by
  refine ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state, Or.inr ?_, ?_⟩
  · exact EvaluatorDiagnosticAtomObservationRel.badArgType positionEquation
      sourceObservation expectedObservation actualObservation
  · simp [Spec.Eval.IsErrorRel, mkError, Atom.error,
      Metta.Atom.isError]

/-- Exact same-spelling atom output is the smallest constructor for a result
boundary.  The finite presentation may still carry bindings for other atoms;
the explicit fixed-point equation records that this result atom is outside
that private support. -/
theorem ofExactUnchangedAtom
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings} {atom : Atom}
    {runtimeAtom : Metta.Atom}
    (state : TypePresentationSimulationState
      presentation specBindings runtimeBindings)
    (atomRelation : AtomRuntimeRel services atom runtimeAtom)
    (unchanged : presentation.apply atom = atom) :
    ScopedEvaluatorResultRuntimeRel services scope
      (atom, specBindings) (runtimeAtom, runtimeBindings) := by
  refine ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state, ?_,
    atomRuntimeRel_isError_iff atomRelation⟩
  apply Or.inl
  refine ⟨atom, runtimeAtom, ?_, atomRelation, rfl⟩
  simpa [unchanged] using (ObservedTypeAlphaRel.refl atom)

/-- General exact-state constructor when the runtime source already realizes
the presentation-applied specification atom.  Error classification remains
an explicit observable because applying a binding can change an expression's
head; reachable evaluator constructors must prove that classification rather
than receive an unsound global preservation lemma. -/
theorem ofExactAppliedAtom
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings} {atom : Atom}
    {runtimeAtom : Metta.Atom}
    (state : TypePresentationSimulationState
      presentation specBindings runtimeBindings)
    (atomRelation : AtomRuntimeRel services
      (presentation.apply atom) runtimeAtom)
    (errorShape : Spec.Eval.IsErrorRel atom ↔
      runtimeAtom.isError = true) :
    ScopedEvaluatorResultRuntimeRel services scope
      (atom, specBindings) (runtimeAtom, runtimeBindings) := by
  refine ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state, ?_, errorShape⟩
  exact Or.inl ⟨presentation.apply atom, runtimeAtom,
    ObservedTypeAlphaRel.refl _, atomRelation, rfl⟩

/-- Scoped-state constructor for a result atom fixed by the finite
specification presentation.  This is the cast-success boundary: binding
theories may differ on private names, while the symbol/grounded/unit result
remains literal before both sides are observed under the runtime binding. -/
theorem ofScopedUnchangedAtom
    {services : Services} {scope : List String}
    {presentation : TypeSubst} {specBindings : Bindings}
    {runtimeBindings : Metta.Bindings} {atom : Atom}
    {runtimeAtom : Metta.Atom}
    (specSolutions : ∀ valuation,
      TypeSubstSatisfied valuation presentation ↔
        TypeBindingSatisfied valuation specBindings)
    (runtimeState : ScopedTypePresentationSimulationState
      scope presentation runtimeBindings)
    (atomRelation : AtomRuntimeRel services atom runtimeAtom)
    (presentationUnchanged : presentation.apply atom = atom) :
    ScopedEvaluatorResultRuntimeRel services scope
      (atom, specBindings) (runtimeAtom, runtimeBindings) := by
  refine ⟨presentation, specSolutions, runtimeState, ?_,
    atomRuntimeRel_isError_iff atomRelation⟩
  apply Or.inl
  refine ⟨atom, runtimeAtom, ?_, atomRelation, rfl⟩
  simpa [presentationUnchanged] using (ObservedTypeAlphaRel.refl atom)

end ScopedEvaluatorResultRuntimeRel

/-- Exact input configuration for one expected-evaluator call.  The finite
presentation is shared by the binding state and the instantiated source
observation.  Raw atoms and expected types are only alpha-related because
function-signature and argument preparation use independent private names. -/
def EvaluatorInputRuntimeRel
    (services : Services)
    (atom expectedType : Atom) (bindings : Bindings)
    (runtimeAtom runtimeExpected : Metta.Atom)
    (runtimeBindings : Metta.Bindings) : Prop :=
  ∃ presentation : TypeSubst,
    TypePresentationSimulationState presentation bindings runtimeBindings ∧
    AlphaAtomRuntimeRel services atom runtimeAtom ∧
    AlphaAtomRuntimeRel services expectedType runtimeExpected ∧
    EvaluatorAtomObservationRel services presentation runtimeBindings atom
      (Metta.instantiate runtimeBindings runtimeAtom) ∧
    (Spec.Eval.IsErrorRel atom ↔
      (Metta.instantiate runtimeBindings runtimeAtom).isError = true)

namespace EvaluatorInputRuntimeRel

/-- The exact binding presentation carried by an input configuration. -/
theorem bindingState
    {services : Services}
    {atom expectedType : Atom} {bindings : Bindings}
    {runtimeAtom runtimeExpected : Metta.Atom}
    {runtimeBindings : Metta.Bindings}
    (relation : EvaluatorInputRuntimeRel services atom expectedType
      bindings runtimeAtom runtimeExpected runtimeBindings) :
    ∃ presentation,
      TypePresentationSimulationState
        presentation bindings runtimeBindings := by
  rcases relation with ⟨presentation, state, _atom, _expected, _source, _error⟩
  exact ⟨presentation, state⟩

/-- The instantiated runtime source is already a related passthrough result.
This is the constructor consumed by the empty/error and meta-type arms. -/
theorem sourceResult
    {services : Services} {scope : List String}
    {atom expectedType : Atom} {bindings : Bindings}
    {runtimeAtom runtimeExpected : Metta.Atom}
    {runtimeBindings : Metta.Bindings}
    (relation : EvaluatorInputRuntimeRel services atom expectedType
      bindings runtimeAtom runtimeExpected runtimeBindings) :
    ScopedEvaluatorResultRuntimeRel services scope (atom, bindings)
      (Metta.instantiate runtimeBindings runtimeAtom, runtimeBindings) := by
  rcases relation with
    ⟨presentation, state, _atom, _expected, source, errorShape⟩
  exact ⟨presentation, state.specSolutions,
    ScopedTypePresentationSimulationState.ofExact state, Or.inl source,
      errorShape⟩

end EvaluatorInputRuntimeRel

/-- A canonical state-free runtime configuration for one spec space.

The runtime environment contains the structural translation of the spec
space, while the mutable runtime world starts empty.  Preparation remains a
relational oracle; functionality and concrete realization are explicit laws
at this boundary rather than fields of the oracle itself. -/
structure RuntimeConfigurationRel
    (services : Services) (oracle : TypePreparationOracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    (env : Metta.Minimal.MinEnv) (state : Metta.Minimal.St) : Prop where
  serviceLaws : ServiceLaws services
  environment : env = Metta.Minimal.MinEnv.ofAtomsGT
    (toLeaTTaAtoms space.atoms) groundingTable
  emptyWorld : state.world = Metta.Minimal.World.empty
  contextPayload :
    toLeaTTaGround (services.contextPayload space) =
      .external "SpaceType" env.contextName
  preparationFunctional : TypePreparationFunctional oracle
  preparationRuntime : TypePreparationRuntimeRealization oracle space state.world

namespace RuntimeConfigurationRel

/-- The bundled A1 type-service theorem derived from one evaluator
configuration; no type-service field is repeated in the carrier. -/
theorem typeService
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state) :
    PreparedPackageTypeServiceRuntimeConformance
      oracle space groundingTable state.world :=
  preparedPackageTypeService_runtimeConformance_ofAtomsGT
    configuration.preparationFunctional space groundingTable
      configuration.preparationRuntime

/-- Direct lookup field at the environment carried by the configuration.
This eliminates repeated rewriting through the canonical `ofAtomsGT`
equation in evaluator constructor proofs. -/
theorem typesOf
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state) (atom : Atom) :
    (preparedPackageTypeService oracle).typesOf space atom
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep state.world (toLeaTTaAtom atom)))) := by
  have lookup := configuration.typeService.typesOf atom
  simpa [configuration.environment] using lookup

/-- Direct seeded expected-aware candidate-scan field at the environment
carried by the configuration.  The finite presentation, native binding
theory, and runtime binding list are one input state.  Binding-support
coverage lets both signature and argument freshening protect every name live
when applicability begins. -/
theorem candidateScanFrom
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation incoming
      runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep state.world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  have scan := configuration.typeService.candidateScan operator expectedType
    arguments incoming initial inputState bindingSupport
  simpa [configuration.environment] using scan

/-- Evaluator-facing candidate selection at the full service scope.  The
runtime fresh signature list is also the specification's existential
presentation, so a successful result retains literal agreement of the
selected arrow fields in addition to the ordinary scan correspondence. -/
theorem candidateScanFrom_aligned
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation incoming
      runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep state.world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRelWith
        SelectedTypePolicyRuntimeExactRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  have scan :=
    preparedPackageTypeService_candidateScan_runtime_ofAtomsGT_aligned
    configuration.preparationFunctional space groundingTable
      configuration.preparationRuntime operator expectedType arguments incoming
      initial inputState bindingSupport
  simpa [configuration.environment] using scan

/-- Candidate selection specialized to the evaluator-visible seed scope.
The full type-service scope remains available for freshness proofs, but the
application worker observes only variables of the post-instantiation
expression and expected type. -/
theorem candidateScanFrom_seedScope
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation incoming
      runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep state.world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (typeServiceRuntimeSeedScope expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  obtain ⟨outcome, scan, runtime⟩ :=
    configuration.candidateScanFrom operator expectedType arguments incoming
      initial inputState bindingSupport
  exact ⟨outcome, scan, runtime.mono
    (typeServiceRuntimeSeedScope_subset_observationScope space
      (Atom.expression (.symbol operator :: arguments)) expectedType)⟩

/-- Seed-scope specialization of the evaluator-aligned candidate scan. -/
theorem candidateScanFrom_seedScope_aligned
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation incoming
      runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep state.world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRelWith
        SelectedTypePolicyRuntimeExactRel
        (typeServiceRuntimeSeedScope expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env state.world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  obtain ⟨outcome, scan, runtime⟩ :=
    configuration.candidateScanFrom_aligned operator expectedType arguments
      incoming initial inputState bindingSupport
  exact ⟨outcome, scan, runtime.mono
    (typeServiceRuntimeSeedScope_subset_observationScope space
      (Atom.expression (.symbol operator :: arguments)) expectedType)⟩

/-- Direct type-cast field at the environment carried by the configuration. -/
theorem typeCast
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state)
    {presentation : TypeSubst} {incoming : Bindings}
    {runtimeBindings : Metta.Bindings}
    (simulation : TypePresentationSimulationState
      presentation incoming runtimeBindings)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeBindings.vars)
    (protectedScope : List String) (atom expectedType : Atom) :
    PreparedTypeCastOutcomeRuntimeRel oracle space atom expectedType incoming
      (Metta.Minimal.mettaTypeCastAvoiding protectedScope env state.world
        runtimeBindings (toLeaTTaAtom atom) (toLeaTTaAtom expectedType))
      protectedScope := by
  have cast := configuration.typeService.typeCast simulation bindingSupport
    protectedScope atom expectedType
  simpa [configuration.environment] using cast

/-- The abstract context-space payload is realized by LeaTTa's opaque
`SpaceType` handle in the related runtime environment. -/
theorem contextAtom
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {groundingTable : Metta.GroundingTable}
    {env : Metta.Minimal.MinEnv} {state : Metta.Minimal.St}
    (configuration : RuntimeConfigurationRel services oracle space
      groundingTable env state) :
    AtomRuntimeRel services
      (.grounded (services.contextPayload space))
      (Metta.Minimal.contextSpaceAtom env.contextName) := by
  have related := contextPayload_runtime configuration.serviceLaws space
  rw [configuration.contextPayload] at related
  simpa [Metta.Minimal.contextSpaceAtom] using related

end RuntimeConfigurationRel

/-! ## Carrier canaries -/

/-- Positive: the empty binding solution and an inert symbol agree. -/
example (services : Services) (scope : List String) :
    ScopedEvaluatorResultRuntimeRel services scope
      (.symbol "a", Bindings.empty) (.sym "a", Metta.Bindings.empty) := by
  refine ⟨[], typePresentationSimulationState_empty.specSolutions,
    ScopedTypePresentationSimulationState.ofExact
      typePresentationSimulationState_empty, ?_, ?_⟩
  · apply Or.inl
    refine ⟨.symbol "a", .sym "a", ?_, ?_, rfl⟩
    · simpa [TypeSubst.apply] using
        ObservedTypeAlphaRel.refl (Atom.symbol "a")
    · exact AtomRuntimeRel.symbol (services := services) "a"
  · simp [Spec.Eval.IsErrorRel, Metta.Atom.isError]

/-- Negative: a symbol result cannot be related to an expression result by
private variable renaming. -/
theorem symbol_not_runtime_expression
    (services : Services) (scope : List String) :
    ¬ScopedEvaluatorResultRuntimeRel services scope
      (.symbol "a", Bindings.empty) (.expr [], Metta.Bindings.empty) := by
  intro relation
  rcases relation with
    ⟨presentation, _specSolutions, _runtimeState, atomPresentation,
      _errorShape⟩
  rcases atomPresentation with atomPresentation | diagnostic
  · obtain ⟨observed, presented, alpha, atom, observation⟩ := atomPresentation
    have applied : presentation.apply (Atom.symbol "a") =
        Atom.symbol "a" := by simp [TypeSubst.apply]
    rw [applied] at alpha
    obtain ⟨permutation, observedEquation⟩ :=
      ObservedTypeAlphaRel.exists_permutation alpha
    have observedEq : observed = Atom.symbol "a" := by
      simpa [renameTypeVars] using observedEquation
    have atomSymbol : AtomRuntimeRel services (Atom.symbol "a") presented := by
      simpa [observedEq] using atom
    cases atomSymbol
    simp [Metta.instantiate, Metta.Bindings.resolveAtom] at observation
  · cases diagnostic

end Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance
