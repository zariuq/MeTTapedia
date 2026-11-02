import Mettapedia.Languages.HOLLight.CachedSubstitution
import Mettapedia.Languages.HOLLight.ParameterSchemaCompilation
import Mettapedia.Languages.HOLLight.CertifiedBlockAppend

/-!
# Typed parameter schemas installed once and reused from cache

Installation retains the existing closed certificate. Each later instance
checks the expected cached theorem and appends only the two substitution
inferences. Its exact typed hypothesis and conclusion images reuse the
existing parameter-schema correspondence. These receipt counts do not bound
substitution time or term sizes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedParameterCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation VariableSchema RetainedCompilation GraphExpansion

variable {policy : AxiomPolicy} [DecidablePred policy]
    {Γ Δ : HOL.Ctx AtomicTy} {conclusion : ParameterTerm Γ .prop}
    {assumptions : List (ParameterTerm Γ .prop)}

def install (state : ProofExecution.State) (sourceNames : Naming Γ)
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion)) :
    ProofExecution.State × Nat :=
  CertifiedBlockAppend.append state [] schema.proof.certificate rfl schema.proof.blockChecked

theorem install_checked {premises : List Theorem} (state : ProofExecution.State)
    (sourceNames : Naming Γ)
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (earlier : BuildChecked policy premises state) :
    let installed := install state sourceNames schema
    BuildChecked policy premises installed.1 ∧ installed.1.cache[installed.2]? = some schema.proof.result ∧
      installed.1.receipts.toList = state.receipts.toList ++
        (expandBlock [] state.cache.size schema.proof.certificate).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → installed.1.cache[index]? = some fact :=
  CertifiedBlockAppend.preserves state [] schema.proof.certificate rfl schema.proof.blockChecked earlier

variable (types : TypeSubst) (sourceNames : Naming Γ) (targetNames : Naming Δ)
    (theta : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute types.baseInstance)) Δ)

def result (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion)) : Theorem :=
  substituteTheorem (ParameterSchemaCompilation.mapping types sourceNames targetNames theta) schema.proof.result

theorem result_hypotheses
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (distinct : Instantiation.KeysDistinct types sourceNames) :
    (result types sourceNames targetNames theta schema).sequent.hyp =
      reverseHypotheses targetNames
        (assumptions.map (ParameterSchemaCompilation.image types sourceNames targetNames theta)) := by
  change (ParameterSchemaCompilation.mapping types sourceNames targetNames theta).applyHypotheses
    schema.proof.result.sequent.hyp = _
  rw [schema.hypotheses_exact]
  exact ParameterSchemaCompilation.hypotheses types sourceNames targetNames theta assumptions distinct

theorem result_conclusion
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (distinct : Instantiation.KeysDistinct types sourceNames) :
    (result types sourceNames targetNames theta schema).sequent.concl =
      reverseCanonical targetNames (ParameterSchemaCompilation.image types sourceNames targetNames theta conclusion) := by
  change (ParameterSchemaCompilation.mapping types sourceNames targetNames theta).apply
    schema.proof.result.sequent.concl = _
  rw [schema.conclusion_exact]
  exact ParameterSchemaCompilation.canonical types sourceNames targetNames theta conclusion distinct

theorem result_axioms
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion)) :
    (result types sourceNames targetNames theta schema).axioms = schema.proof.result.axioms := rfl

def specialize? (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (_distinct : Instantiation.KeysDistinct types sourceNames) (state : ProofExecution.State)
    (sourceRoot : Nat) (origin : ProofExecution.Origin) : Option (ProofExecution.State × Nat) :=
  CachedSubstitution.applyExpected? policy state sourceRoot schema.proof.result
    (ParameterSchemaCompilation.mapping types sourceNames targetNames theta) origin

theorem specialize_checked {premises : List Theorem} {state : ProofExecution.State} {sourceRoot : Nat}
    (schema : Compiled policy sourceNames (assumptions.map embed) (embed conclusion))
    (distinct : Instantiation.KeysDistinct types sourceNames)
    (earlier : BuildChecked policy premises state) (found : state.cache[sourceRoot]? = some schema.proof.result)
    (origin : ProofExecution.Origin) :
    ∃ after root, specialize? types sourceNames targetNames theta schema distinct state sourceRoot origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (result types sourceNames targetNames theta schema) ∧
      after.receipts.size = state.receipts.size + 2 ∧
      after.receipts.toList = state.receipts.toList ++
        (expandBlock [sourceRoot] state.cache.size (PrimitiveTransport.substitutionBlock
          (ParameterSchemaCompilation.mapping types sourceNames targetNames theta) schema.proof.result origin)).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact :=
  CachedSubstitution.applyExpected_checked earlier found _ origin

def expandedImages : HOL.Subst Symbol (Γ.map (HOL.Ty.substitute types.baseInstance)) Δ :=
  fun index => HOL.ImpredicativeConnectives.expand (theta index)

def expandedResult
    (schema : Compiled policy sourceNames
      ((assumptions.map HOL.ImpredicativeConnectives.expand).map embed)
      (embed (HOL.ImpredicativeConnectives.expand conclusion))) : Theorem :=
  result types sourceNames targetNames (expandedImages types theta) schema

theorem expandedResult_hypotheses
    (schema : Compiled policy sourceNames
      ((assumptions.map HOL.ImpredicativeConnectives.expand).map embed)
      (embed (HOL.ImpredicativeConnectives.expand conclusion)))
    (distinct : Instantiation.KeysDistinct types sourceNames) :
    (expandedResult types sourceNames targetNames theta schema).sequent.hyp =
      reverseHypotheses targetNames
        ((assumptions.map (ParameterSchemaCompilation.image types sourceNames targetNames theta)).map
          HOL.ImpredicativeConnectives.expand) := by
  rw [expandedResult, result_hypotheses types sourceNames targetNames _ schema distinct]
  apply congrArg (reverseHypotheses targetNames)
  clear schema
  induction assumptions with
  | nil => rfl
  | cons formula rest previous =>
      exact congrArg₂ List.cons (ParameterSchemaCompilation.image_expand types sourceNames targetNames theta formula) previous

theorem expandedResult_conclusion
    (schema : Compiled policy sourceNames
      ((assumptions.map HOL.ImpredicativeConnectives.expand).map embed)
      (embed (HOL.ImpredicativeConnectives.expand conclusion)))
    (distinct : Instantiation.KeysDistinct types sourceNames) :
    (expandedResult types sourceNames targetNames theta schema).sequent.concl =
      reverseCanonical targetNames
        (HOL.ImpredicativeConnectives.expand (ParameterSchemaCompilation.image types sourceNames targetNames theta conclusion)) := by
  rw [expandedResult, result_conclusion types sourceNames targetNames _ schema distinct]
  exact congrArg (reverseCanonical targetNames)
    (ParameterSchemaCompilation.image_expand types sourceNames targetNames theta conclusion)

def specializeExpanded?
    (schema : Compiled policy sourceNames
      ((assumptions.map HOL.ImpredicativeConnectives.expand).map embed)
      (embed (HOL.ImpredicativeConnectives.expand conclusion)))
    (distinct : Instantiation.KeysDistinct types sourceNames) (state : ProofExecution.State)
    (sourceRoot : Nat) (origin : ProofExecution.Origin) : Option (ProofExecution.State × Nat) :=
  specialize? types sourceNames targetNames (expandedImages types theta) schema distinct state sourceRoot origin

theorem specializeExpanded_checked {premises : List Theorem} {state : ProofExecution.State} {sourceRoot : Nat}
    (schema : Compiled policy sourceNames
      ((assumptions.map HOL.ImpredicativeConnectives.expand).map embed)
      (embed (HOL.ImpredicativeConnectives.expand conclusion)))
    (distinct : Instantiation.KeysDistinct types sourceNames)
    (earlier : BuildChecked policy premises state) (found : state.cache[sourceRoot]? = some schema.proof.result)
    (origin : ProofExecution.Origin) :
    ∃ after root, specializeExpanded? types sourceNames targetNames theta schema distinct state sourceRoot origin = some (after, root) ∧
      BuildChecked policy premises after ∧ after.cache[root]? = some (expandedResult types sourceNames targetNames theta schema) ∧
      after.receipts.size = state.receipts.size + 2 ∧
      after.receipts.toList = state.receipts.toList ++
        (expandBlock [sourceRoot] state.cache.size (PrimitiveTransport.substitutionBlock
          (ParameterSchemaCompilation.mapping types sourceNames targetNames (expandedImages types theta)) schema.proof.result origin)).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact :=
  specialize_checked types sourceNames targetNames (expandedImages types theta) schema distinct earlier found origin

#print axioms install_checked
#print axioms result_conclusion
#print axioms specialize_checked
#print axioms expandedResult_conclusion
#print axioms specializeExpanded_checked

end Mettapedia.Languages.HOLLight.CachedParameterCompilation
