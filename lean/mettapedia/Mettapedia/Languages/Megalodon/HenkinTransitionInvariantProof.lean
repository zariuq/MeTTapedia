import Mettapedia.Languages.Megalodon.HenkinTermInterpretation
import Mettapedia.Logic.HOL.Syntax.TypeSubstitution
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHOLInvariant

/-!
# A native Megalodon proof of the call-guard invariant rule

The source proof uses the existing Mathdata proof constructors to derive
preservation by a relation from refinement into another preserving relation.
Its proposition and hypotheses are independently checked for formation, and
the actual native checker accepts its proof object. Existing HOL type
substitution and partial erasure identify the statements exactly with the
intrinsic proof used by the call-guard consumer.

This is a paired proof specimen, not a translation of arbitrary native proofs
or a soundness theorem for the complete native checker. The call-guard model
satisfies the assumptions independently. The altered-model control retains
native acceptance while refuting those assumptions and the open conclusion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTransitionInvariantProof

open MathdataKernel
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.TransitionInvariant
open HenkinTermInterpretation

open Mettapedia.Languages.MeTTa.PeTTa

/-- Three typed symbols and no named axioms or transparent definitions. -/
def environment : Environment :=
  { primitives :=
      [.arr (.base 0) (.arr (.base 0) .prop),
        .arr (.base 0) (.arr (.base 0) .prop), .arr (.base 0) .prop] }

/-- Native syntax for the two independently justified relational assumptions. -/
def nativeRefinement : Tm :=
  .all (.base 0) (.all (.base 0)
    (.imp (.app (.app (.prim 0) (.db 1)) (.db 0))
      (.app (.app (.prim 1) (.db 1)) (.db 0))))

def nativePreservation (relation : Nat) : Tm :=
  .all (.base 0) (.all (.base 0)
    (.imp (.app (.app (.prim relation) (.db 1)) (.db 0))
      (.imp (.app (.prim 2) (.db 1)) (.app (.prim 2) (.db 0)))))

def nativeAssumptions : List Tm := [nativeRefinement, nativePreservation 1]

def nativeConclusion : Tm := nativePreservation 0

/-- Instantiate both hypotheses at the two bound states, compose the
implications, and discharge the transition and property assumptions. -/
def nativeProof : Pf :=
  .termLam (.base 0) (.termLam (.base 0)
    (.proofLam (.app (.app (.prim 0) (.db 1)) (.db 0))
      (.proofLam (.app (.prim 2) (.db 1))
        (.proofApp
          (.proofApp (.termApp (.termApp (.hyp 3) (.db 1)) (.db 0))
            (.proofApp (.termApp (.termApp (.hyp 2) (.db 1)) (.db 0)) (.hyp 1)))
          (.hyp 0)))))

/-- Closing both assumptions yields a theorem without named axioms. -/
def nativeTheorem : Tm :=
  .imp (nativePreservation 1) (.imp nativeRefinement nativeConclusion)

def closedNativeProof : Pf :=
  .proofLam (nativePreservation 1) (.proofLam nativeRefinement nativeProof)

theorem native_formation :
    environment.primitives.all (Tp.plainWellFormed 0) = true ∧
      nativeAssumptions.all (checkProposition environment 0 []) = true ∧
      checkProposition environment 0 [] nativeConclusion = true ∧
      checkProposition environment 0 [] nativeTheorem = true := by decide

theorem native_proof_inferred :
    inferProof environment 4 0 [] nativeAssumptions nativeProof = some nativeConclusion := by
  simp [nativeProof, nativeAssumptions, nativeRefinement, nativePreservation,
    nativeConclusion, environment, inferProof, inferTerm, MathdataKernel.normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate, Tm.instantiateAt,
    Tp.plainWellFormed]

theorem native_conclusion_normalized :
    normalize environment 4 nativeConclusion = some nativeConclusion := by
  simp [nativeConclusion, nativePreservation, MathdataKernel.normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne]

theorem native_proof_accepted :
    checkProof environment 4 0 [] nativeAssumptions nativeProof nativeConclusion = true := by
  simp [checkProof, checkNormalizedProof, native_conclusion_normalized, native_proof_inferred]

theorem closed_native_proof_accepted :
    checkProof environment 4 0 [] [] closedNativeProof nativeTheorem = true := by
  simp [closedNativeProof, nativeTheorem, nativeProof, nativeRefinement,
    nativePreservation, nativeConclusion, environment, checkProof, checkNormalizedProof,
    inferProof, inferTerm, MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne,
    Tm.shift, Tm.instantiate, Tm.instantiateAt, Tp.plainWellFormed]

/-! ## Exact statement correspondence through existing HOL syntax maps -/

def stateInterpretation (_ : Unit) : Ty Base := .base (.inr 0)

def constantInterpretation : {type : Ty Unit} → MainlineCallGuardHOLInvariant.Constant type →
    Constant environment (Ty.substitute stateInterpretation type)
  | _, .step => .primitive 0 rfl
  | _, .sameResult => .primitive 1 rfl
  | _, .property => .primitive 2 rfl

def interpretFormula (formula : ClosedFormula MainlineCallGuardHOLInvariant.Constant) :
    ClosedFormula (Constant environment) :=
  mapTypes stateInterpretation constantInterpretation formula

/-- Both the hypotheses and conclusion match the consumer's actual HOL
formulas, not a second specification invented from the source proof output. -/
theorem statement_correspondence :
    (MainlineCallGuardHOLInvariant.assumptions.map
        (fun formula => erase (interpretFormula formula))) =
        nativeAssumptions.map some ∧
      erase (interpretFormula MainlineCallGuardHOLInvariant.conclusion) =
        some nativeConclusion := by
  constructor <;> rfl

/-- The separately constructed intrinsic proof closes the very same two
assumptions as the accepted native proof. -/
theorem closed_statement_correspondence :
    erase (interpretFormula
      (.imp (preservationFormula (.const .sameResult) (.const .property))
        (.imp (refinementFormula (.const .step) (.const .sameResult))
          MainlineCallGuardHOLInvariant.conclusion))) = some nativeTheorem := rfl

theorem intrinsic_closed_derivation :
    Derivation MainlineCallGuardHOLInvariant.Constant []
      (.imp (preservationFormula (.const .sameResult) (.const .property))
        (.imp (refinementFormula (.const .step) (.const .sameResult))
          MainlineCallGuardHOLInvariant.conclusion)) :=
  .impI (.impI MainlineCallGuardHOLInvariant.preservation_derived)

/-! ## Independent negative controls -/

/-- Removing the refinement assumption does not leave an accepted proof of
the invariant. The missing premise cannot be supplied by proof syntax alone. -/
theorem missing_refinement_rejected :
    checkProof environment 4 0 [] [nativePreservation 1] nativeProof nativeConclusion = false := by
  simp only [checkProof, native_conclusion_normalized]
  simp [checkNormalizedProof, nativeProof,
    nativePreservation, environment, inferProof, inferTerm, MathdataKernel.normalize,
    deltaNormalize, Tm.normalize, Tm.normalizeOne, Tm.shift, Tm.instantiate,
    Tm.instantiateAt, Tp.plainWellFormed]

/-- The accepted source sequent and its exact statement interpretation remain
unchanged when the operational predicate is altered, but model satisfaction
and the desired operational conclusion then fail. -/
theorem native_acceptance_does_not_supply_model_assumptions :
    checkProof environment 4 0 [] nativeAssumptions nativeProof nativeConclusion = true ∧
      ¬ Soundness.SatisfiesHyps
        (MainlineCallGuardHOLInvariant.model MainlineCallGuardHOLInvariant.runningPredicate)
        (MainlineCallGuardHOLInvariant.emptyValuation _)
        MainlineCallGuardHOLInvariant.assumptions ∧
      ¬ HenkinModel.models
        (MainlineCallGuardHOLInvariant.model MainlineCallGuardHOLInvariant.runningPredicate)
        MainlineCallGuardHOLInvariant.conclusion :=
  ⟨native_proof_accepted, MainlineCallGuardHOLInvariant.altered_interpretation_not_satisfying,
    MainlineCallGuardHOLInvariant.altered_interpretation_not_valid⟩

#print axioms native_formation
#print axioms native_proof_accepted
#print axioms closed_native_proof_accepted
#print axioms statement_correspondence
#print axioms intrinsic_closed_derivation
#print axioms missing_refinement_rejected
#print axioms native_acceptance_does_not_supply_model_assumptions

end Mettapedia.Languages.Megalodon.HenkinTransitionInvariantProof
