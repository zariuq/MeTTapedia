import Mettapedia.Languages.Megalodon.HenkinProofSoundness
import Mettapedia.Languages.Megalodon.NativeDefinitionModel

/-!
# Native proof soundness with real definition unfolding

The existing mixed environment contains `q := id p`, where `id` is a
transparent identity function. Both implication introduction at `q` and
universal elimination with argument `q` exercise the actual definition and
beta normalization used by the source checker.

The same accepted proof has an invalid submitted goal when the model violates
the declaration equations. Separately, insufficient fuel rejects a valid goal,
and raw hypothesis lookup accepts an unscoped proposition that cannot satisfy
the exact typed-hypothesis interface. These are distinct boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinProofSoundnessExamples

open MathdataKernel
open Mettapedia.Logic.HOL
open HenkinTermInterpretation
open HenkinTermInterpretation.DeltaTypingExamples
open NativeDefinitionModel

def goal : ClosedFormula NativeConstant :=
  .imp (.const propositionConstant) (.const parameterConstant)

def rawGoal : Tm := .imp (.named "q") (.named "p")

def normalizedGoal : Tm := .imp (.named "p") (.named "p")

def identityAtDefinition : Pf := .proofLam (.named "q") (.hyp 0)

/-- Universal elimination supplies a definition-bearing proposition as the
actual native argument; the instantiated body must subsequently normalize. -/
def instantiatedIdentity : Pf :=
  .termApp (.termLam .prop (.proofLam (.db 0) (.hyp 0))) (.named "q")

theorem goal_erased : erase goal = some rawGoal := rfl

theorem goal_formed : checkProposition environment 0 [] rawGoal = true := by decide

private theorem proposition_lookups : PlainLookups environment 0 (.named "q") := by
  simp [PlainLookups, environment, Environment.lookupTerm?, lookupTermList?,
    identityDeclaration, propositionDeclaration, Tp.plainWellFormed]

theorem identity_fragment : NativeProof.Fragment environment 0 identityAtDefinition :=
  .proofLam rfl proposition_lookups (.hyp 0)

theorem instantiated_fragment : NativeProof.Fragment environment 0 instantiatedIdentity :=
  .termApp (.termLam (.proofLam rfl (by trivial) (.hyp 0))) rfl proposition_lookups

theorem goal_normalizes : normalize environment 2 rawGoal = some normalizedGoal := by
  simp [rawGoal, normalizedGoal, MathdataKernel.normalize, deltaNormalize,
    environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
    propositionDeclaration, parameterDeclaration, Tm.normalize, Tm.normalizeOne,
    Tm.instantiate, Tm.instantiateAt, Tm.shift]

theorem goal_normalization_changes_syntax : rawGoal ≠ normalizedGoal := by decide

theorem identity_inferred :
    inferProof environment 2 0 [] [] identityAtDefinition = some normalizedGoal := by
  simp [identityAtDefinition, normalizedGoal, inferProof, inferTerm, MathdataKernel.normalize,
    deltaNormalize, environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
    propositionDeclaration, parameterDeclaration, Tm.normalize, Tm.normalizeOne,
    Tm.instantiate, Tm.instantiateAt, Tm.shift]

theorem identity_accepted :
    checkProof environment 2 0 [] [] identityAtDefinition rawGoal = true := by
  simp [checkProof, checkNormalizedProof, goal_normalizes, identity_inferred]

theorem instantiated_inferred :
    inferProof environment 2 0 [] [] instantiatedIdentity = some normalizedGoal := by
  simp [instantiatedIdentity, normalizedGoal, inferProof, inferTerm, MathdataKernel.normalize,
    deltaNormalize, environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
    propositionDeclaration, parameterDeclaration, Tm.normalize, Tm.normalizeOne,
    Tm.instantiate, Tm.instantiateAt, Tm.shift, Tp.plainWellFormed]

theorem instantiated_accepted :
    checkProof environment 2 0 [] [] instantiatedIdentity rawGoal = true := by
  simp [checkProof, checkNormalizedProof, goal_normalizes, instantiated_inferred]

private theorem knownValidity (parameter proposition : Prop) :
    NativeProof.KnownValidity (model parameter proposition) := by
  intro name raw lookup
  simp [environment, Environment.lookupKnown?, lookupKnownList?] at lookup

/-- Validity follows from the generic native proof-soundness theorem, with
the independent declaration equations supplied by the existing model. -/
theorem accepted_goal_valid (parameter : Prop) : (model parameter parameter).models goal := by
  exact NativeProof.checkProof_sound checkedDefinitions (model parameter parameter)
    (definitionEquations parameter) (knownValidity parameter parameter)
    (Γ := []) (hypotheses := []) (rawHypotheses := [])
    identity_fragment rfl goal goal_erased identity_accepted (fun v => nomatch v)
    (by intro type index; nomatch index) (by intro formula member; nomatch member)

/-- The term-application branch yields the same source validity through the
generic theorem, rather than a separately supplied intrinsic proof. -/
theorem instantiated_goal_valid (parameter : Prop) :
    (model parameter parameter).models goal := by
  exact NativeProof.checkProof_sound checkedDefinitions (model parameter parameter)
    (definitionEquations parameter) (knownValidity parameter parameter)
    (Γ := []) (hypotheses := []) (rawHypotheses := [])
    instantiated_fragment rfl goal goal_erased instantiated_accepted (fun v => nomatch v)
    (by intro type index; nomatch index) (by intro formula member; nomatch member)

theorem altered_model_refutes_goal : ¬ (model False True).models goal := by
  change ¬ (True → False)
  exact fun holds => holds trivial

theorem altered_model_refutes_definitions :
    ¬ DefinitionEquations checkedDefinitions (model False True) := by
  rw [definitionEquations_iff]
  exact fun equal => equal.mp trivial

/-- Formation and native acceptance do not supply the declaration equations
needed to interpret the submitted source proposition. -/
theorem acceptance_does_not_supply_model_validity :
    checkProposition environment 0 [] rawGoal = true ∧
      checkProof environment 2 0 [] [] identityAtDefinition rawGoal = true ∧
      ¬ DefinitionEquations checkedDefinitions (model False True) ∧
      ¬ (model False True).models goal :=
  ⟨goal_formed, identity_accepted, altered_model_refutes_definitions, altered_model_refutes_goal⟩

theorem insufficient_fuel_rejects :
    checkProof environment 1 0 [] [] identityAtDefinition rawGoal = false := by
  simp [checkProof, rawGoal, MathdataKernel.normalize, deltaNormalize,
    environment, Environment.lookupTerm?, lookupTermList?, identityDeclaration,
    propositionDeclaration]

/-- Resource failure is compatible with validity in a satisfying model; it
is not a proof of the proposition's negation. -/
theorem insufficient_fuel_rejects_valid_goal (parameter : Prop) :
    checkProof environment 1 0 [] [] identityAtDefinition rawGoal = false ∧
      (model parameter parameter).models goal :=
  ⟨insufficient_fuel_rejects, accepted_goal_valid parameter⟩

/-! ## Raw hypothesis lookup does not establish scope -/

theorem unscoped_hypothesis_raw_accepted :
    checkProof environment 2 0 [] [.db 0] (.hyp 0) (.db 0) = true ∧
      checkProposition environment 0 [] (.db 0) = false := by
  simp [checkProof, checkNormalizedProof, inferProof, checkProposition, inferTerm,
    MathdataKernel.normalize, deltaNormalize, Tm.normalize, Tm.normalizeOne]

theorem no_typed_unscoped_hypothesis
    (hypotheses : List (ClosedFormula NativeConstant)) :
    ¬ NativeProof.ErasedHypotheses hypotheses [.db 0] := by
  intro erased
  obtain ⟨formula, _, formulaErased⟩ :=
    erased.lookup (index := 0) (proposition := .db 0) rfl
  obtain ⟨index, _, _⟩ := erase_db_inv formulaErased
  nomatch index

#print axioms identity_accepted
#print axioms goal_normalization_changes_syntax
#print axioms instantiated_accepted
#print axioms accepted_goal_valid
#print axioms instantiated_goal_valid
#print axioms acceptance_does_not_supply_model_validity
#print axioms insufficient_fuel_rejects_valid_goal
#print axioms unscoped_hypothesis_raw_accepted
#print axioms no_typed_unscoped_hypothesis

end Mettapedia.Languages.Megalodon.HenkinProofSoundnessExamples
