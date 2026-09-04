import Mettapedia.Languages.Metamath.MM2VerifierProgram
import Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
import Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
import Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
import Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup

/-!
# Composition of the two Metamath-to-MM2 transformation outputs

The verifier output is database- and proof-independent.  The source-data
output contains admitted passive rows derived from the ordered source event
stream without checking a theorem proof.  This module keeps both outputs
separate and defines their executable composition as list concatenation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2TwoTransformProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionPlan
open Mettapedia.Languages.Metamath.MM2SourceAssertionExecution
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.MM2SourceDVPairPlan
open Mettapedia.Languages.Metamath.MM2SourceDVOccurrenceLookup
open Mettapedia.Languages.Metamath.MM2SourceEssentialDeclaration
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.MM2SourceVariableTypecodeLookup
open Mettapedia.Languages.Metamath.MM2SourceVariableDeclaration
open Mettapedia.Languages.Metamath.MM2VerifierProgram
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTOperations

/-- Source operations already handled by the native declaration and scope
rules rather than by the residual action-plan path. -/
def usesNativeSourceStatement : RawStatement → Bool
  | .constDecl _ _ _ => true
  | .varDecl _ _ _ => true
  | .openScope _ => true
  | .closeScope _ => true
  | .floating _ _ _ _ _ => true
  | .djDecl _ _ _ => true
  | .essential _ _ _ _ _ => true
  | .axiomatic _ _ _ _ _ => true
  | _ => false

def usesNativeSourceOperation (plan : StatementActionPlan) : Bool :=
  usesNativeSourceStatement plan.statement

@[simp] theorem usesNativeSourceStatement_closeScope
    (span : LocatedByteSpan) :
    usesNativeSourceStatement (.closeScope span) = true := by
  rfl

/-- Plans retained for the residual source-action path. -/
def residualSourceActionPlans {owner : Atom}
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) :
    List StatementActionPlan :=
  actions.plans.filter fun plan => !usesNativeSourceOperation plan

def residualSourceActionRows {owner : Atom}
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) : List Atom :=
  StatementActionPlan.preparedRowsList owner
    (residualSourceActionPlans actions)

def residualSourceActionKindRows {owner : Atom}
    {statements : List RawStatement}
    (actions : AdmittedSourceActionPlans owner statements) : List Atom :=
  (residualSourceActionPlans actions).flatMap
    (statementActionPlanActionKindRows owner)

/-- Wrapping a normal or compressed proof control for ordered activation
preserves proof-neutrality of the source row. -/
theorem deferProofControlRow_preserves_proofNeutral
    (row : Atom) (neutral : isProofNeutralInitialAtom row = true) :
    isProofNeutralInitialAtom (deferProofControlRow row) = true := by
  unfold deferProofControlRow
  split <;> simp_all [isProofNeutralInitialAtom,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

/-- Deferring normal and compressed proof controls preserves an all-neutral
source artifact. -/
theorem deferProofControls_all_proofNeutral
    (rows : List Atom) (neutral : rows.all isProofNeutralInitialAtom = true) :
    (deferProofControls rows).all isProofNeutralInitialAtom = true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [deferProofControls, List.mem_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := member
  exact deferProofControlRow_preserves_proofNeutral source
    ((List.all_eq_true.mp neutral) source sourceMember)

/-- Withholding compressed header controls preserves proof-neutrality. -/
theorem deferCompressedHeaderControlRow_preserves_proofNeutral
    (row : Atom) (neutral : isProofNeutralInitialAtom row = true) :
    isProofNeutralInitialAtom (deferCompressedHeaderControlRow row) = true := by
  unfold deferCompressedHeaderControlRow
  split <;> simp_all [isProofNeutralInitialAtom,
    isVerifierTerminalObservation, isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

/-- Deferring every compressed header control preserves an all-neutral source
artifact. -/
theorem deferCompressedHeaderControls_all_proofNeutral
    (rows : List Atom) (neutral : rows.all isProofNeutralInitialAtom = true) :
    (deferCompressedHeaderControls rows).all isProofNeutralInitialAtom =
      true := by
  apply List.all_eq_true.mpr
  intro row member
  rw [deferCompressedHeaderControls, List.mem_map] at member
  obtain ⟨source, sourceMember, rfl⟩ := member
  exact deferCompressedHeaderControlRow_preserves_proofNeutral source
    ((List.all_eq_true.mp neutral) source sourceMember)

/-- The proof-neutral source-data transformation output.  The rows are passive
at the composition boundary; verifier-owned rules activate them in source
order during execution. -/
def sourceDataProgram {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) : List Atom :=
  let dvPlans := admitSourceDVPairPlans actions
  let assertionCandidates := admitSourceAssertionCandidatesFromActions actions
  deferCompressedHeaderControls (deferProofControls input.initialRows) ++
    objectInventoryRows owner [] ++ activeVariableRows owner [] ++
      variableTypecodeLedgerRows owner [] ++ emptyScopedActivityRows owner ++
      dvOccurrenceRows owner [] ++ dvPlans.rows ++ dvPlans.witnessRows ++
      AdmittedSourceAssertionCandidates.rows assertionCandidates ++
      nativeAssertionPublicationRows owner assertionCandidates.candidates ++
      essentialCandidateRows owner actions.plans ++
      residualSourceActionRows actions ++
      residualSourceActionKindRows actions

/-- Every row emitted by the source-data transformation is proof-neutral at
the composition boundary.  In particular, the source side contributes no
executable shell, verdict, verifier-owned code carrier, or normal body cursor. -/
theorem sourceDataProgram_all_proofNeutral {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    (sourceDataProgram input actions).all isProofNeutralInitialAtom = true := by
  simp [sourceDataProgram,
    deferCompressedHeaderControls_all_proofNeutral,
    deferProofControls_all_proofNeutral,
    input.initialRows_all_proofNeutral,
    residualSourceActionRows, residualSourceActionKindRows,
    residualSourceActionPlans, objectInventoryRows,
    nativeAssertionPublicationRows_all_proofNeutral,
    objectInventoryRowsFrom, objectFrontierAtom, activeVariableRows,
    variableTypecodeLedgerRows, variableTypecodeInventoryRows,
    variableTypecodeBindingRows, emptyScopedActivityRows,
    sourceActivityFrontierAtom, dvOccurrenceRows, dvOccurrenceRowsFrom,
    dvOccurrenceFrontierAtom, dvOccurrenceFrontierAtAtom,
    isProofNeutralInitialAtom, isVerifierTerminalObservation,
    isVerifierOwnedInternalRowShape,
    Mettapedia.Languages.ProcessCalculi.MORK.extractRawExecFact]

/-- Executable composition of the two independently constructed outputs. -/
def composeProgram (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) : List Atom :=
  genericVerifierProgram source ++ sourceDataProgram input actions

@[simp] theorem composeProgram_eq_two_outputs
    (source : MetamathVerifierGSLT) {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    composeProgram source input actions =
      genericVerifierProgram source ++ sourceDataProgram input actions := by
  rfl

/-- Expanding composition reveals only the fixed verifier output followed by
the passive rows derived from the admitted source and its exact action plans. -/
theorem composeProgram_eq_generic (source : MetamathVerifierGSLT)
    {owner : Atom}
    (input : AdmittedSourceEventInput owner)
    (actions : AdmittedSourceActionPlans owner input.statements) :
    composeProgram source input actions =
      let dvPlans := admitSourceDVPairPlans actions
      let assertionCandidates := admitSourceAssertionCandidatesFromActions actions
      (genericVerifierProgram source ++
        deferCompressedHeaderControls (deferProofControls input.initialRows) ++
          objectInventoryRows owner [] ++ activeVariableRows owner [] ++
            variableTypecodeLedgerRows owner [] ++
              emptyScopedActivityRows owner ++
                dvOccurrenceRows owner [] ++ dvPlans.rows ++
                  dvPlans.witnessRows ++
            AdmittedSourceAssertionCandidates.rows assertionCandidates ++
            nativeAssertionPublicationRows owner assertionCandidates.candidates ++
            essentialCandidateRows owner actions.plans ++
            residualSourceActionRows actions ++
              residualSourceActionKindRows actions) := by
  simp [composeProgram, sourceDataProgram, List.append_assoc]

#print axioms usesNativeSourceStatement_closeScope
#print axioms deferProofControlRow_preserves_proofNeutral
#print axioms deferProofControls_all_proofNeutral
#print axioms deferCompressedHeaderControlRow_preserves_proofNeutral
#print axioms deferCompressedHeaderControls_all_proofNeutral
#print axioms sourceDataProgram_all_proofNeutral
#print axioms composeProgram_eq_two_outputs
#print axioms composeProgram_eq_generic

end Mettapedia.Languages.Metamath.MM2TwoTransformProgram
