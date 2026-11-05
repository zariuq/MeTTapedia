import Mettapedia.Languages.HOLLight.SourceIndexedVectorTreeStoredConstructorRecoveryCompilation
import Mettapedia.Logic.HOL.ConstructorArgumentRecoveryLaws

/-!
# Source-backed universal recovery of stored Vector-tree payloads

The original full solved/branch admission domain is quantified over its
tag, payload and child function. The universal recovery proof is built from
the actual substitution-stable recovery callback and the same three source
provider premises used by guarded constructor uniqueness.

Compilation retains the original element and numeric predicates and uses
the common retained compiler under the empty axiom policy. Provider-root
discharge, whole-family/source-context interpretation and external native
replay remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SourceIndexedVectorTreeStoredPayloadRecoveryCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef
open SourceIndexedVectorTreeStoredConstructorRecoveryCompilation (inputs premises tags bottom domain)

variable {policy : AxiomPolicy} [DecidablePred policy] {before : ProofExecution.Registered.State}
  {operations : RecursiveSpaceSourceReadback.Operations} {parameter : Name}
  (element : Ty)
  (admitted : AdmittedSourcePayloads.Instance policy before operations parameter
    (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element))
  (numberSame : (AdmittedSourcePayloads.targetOperations operations parameter
    (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)).number = operations.number)
  (source : HOL.ClosedTerm Symbol (element.toHOL.arr .prop))
  (numbers : HOL.ClosedTerm Symbol (operations.number.toHOL.arr .prop))

theorem premises_exact : premises element admitted numberSame =
    [SourceSelectionProfile.native
      (AdmittedSourcePayloads.payload (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)),
      SourceSelectionProfile.native element,
      ConstructorInjectivityProfile.native (AdmittedSourcePayloads.targetOperations operations parameter
        (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)).recursive] :=
  SourceIndexedVectorTreeStoredConstructorRecoveryCompilation.premises_exact element admitted numberSame

theorem premise_count : (premises element admitted numberSame).length = 3 :=
  SourceIndexedVectorTreeStoredConstructorRecoveryCompilation.premise_count element admitted numberSame

def statement : HOL.ClosedFormula Symbol :=
  HOL.ConstructorArgumentMap.recoveryStatement
    (HOL.VectorTreePayloadMaps.lowerProgram (inputs element admitted numberSame))
    (HOL.VectorTreePayloadMaps.raiseProgram (inputs element admitted numberSame))
    (domain element admitted numberSame source numbers)

@[irreducible] def admittedRecovery : HOL.ConstructorArgumentMap.Recovery (premises element admitted numberSame)
    (HOL.VectorTreePayloadMaps.lowerProgram (inputs element admitted numberSame))
    (HOL.VectorTreePayloadMaps.raiseProgram (inputs element admitted numberSame))
    (domain element admitted numberSame source numbers) :=
  IndexedVectorTreeStoredConstructorRecovery.recovery (inputs element admitted numberSame)
    source numbers operations.natural.zero (.app operations.natural.successor operations.natural.zero)
    operations.natural.successor (tags (operations := operations)) (bottom (parameter := parameter) element)
    (SourceFiniteConstructorFieldEmbeddingCompilation.payloadProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.fieldProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.constructorProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))

theorem admittedRecovery_free :
    HOL.ConstructorArgumentMap.Recovery.Free (admittedRecovery element admitted numberSame source numbers) := by
  unfold admittedRecovery
  exact IndexedVectorTreeStoredConstructorRecovery.recovery_free (inputs element admitted numberSame)
    source numbers operations.natural.zero (.app operations.natural.successor operations.natural.zero)
    operations.natural.successor (tags (operations := operations)) (bottom (parameter := parameter) element)
    (SourceFiniteConstructorFieldEmbeddingCompilation.payloadProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.fieldProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.constructorProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.payloadProof_free
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.fieldProof_free
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.constructorProof_free
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))

@[irreducible] def recoveryProof : HOL.ProofSyntax Symbol (premises element admitted numberSame)
    (statement element admitted numberSame source numbers) :=
  HOL.ConstructorArgumentMap.recoveryLaw
    (HOL.VectorTreePayloadMaps.lowerProgram (inputs element admitted numberSame))
    (HOL.VectorTreePayloadMaps.raiseProgram (inputs element admitted numberSame))
    (domain element admitted numberSame source numbers)
    (admittedRecovery element admitted numberSame source numbers)

theorem recoveryProof_free :
    (recoveryProof element admitted numberSame source numbers).FunctionExtensionalityFree := by
  unfold recoveryProof
  exact HOL.ConstructorArgumentMap.recoveryLaw_free
    (HOL.VectorTreePayloadMaps.lowerProgram (inputs element admitted numberSame))
    (HOL.VectorTreePayloadMaps.raiseProgram (inputs element admitted numberSame))
    (domain element admitted numberSame source numbers)
    (admittedRecovery element admitted numberSame source numbers)
    (admittedRecovery_free element admitted numberSame source numbers)

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

@[irreducible, noinline] def compile :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (recoveryProof element admitted numberSame source numbers)
    (recoveryProof_free element admitted numberSame source numbers)
    ReverseTranslation.Naming.empty ("source-vector-tree-stored-payload-recovery", 0)

theorem compile_accepted :
    (ProofSystem.checker emptyAxiomPolicy).check (compile element admitted numberSame source numbers).proof.result
      (compile element admitted numberSame source numbers).proof.certificate = true :=
  (compile element admitted numberSame source numbers).proof.accepted

theorem compile_hypotheses :
    (compile element admitted numberSame source numbers).proof.result.sequent.hyp =
      ReverseTranslation.reverseHypotheses ReverseTranslation.Naming.empty
        ((premises element admitted numberSame).map HOL.ImpredicativeConnectives.expand) :=
  (compile element admitted numberSame source numbers).hypotheses_exact

theorem compile_conclusion :
    (compile element admitted numberSame source numbers).proof.result.sequent.concl =
      ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
        (HOL.ImpredicativeConnectives.expand (statement element admitted numberSame source numbers)) :=
  (compile element admitted numberSame source numbers).conclusion_exact

theorem compile_refuses_changed_conclusion (claim : Theorem)
    (different : claim.sequent.concl ≠ ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
      (HOL.ImpredicativeConnectives.expand (statement element admitted numberSame source numbers))) :
    (ProofSystem.checker emptyAxiomPolicy).check claim
      (compile element admitted numberSame source numbers).proof.certificate = false := by
  apply (compile element admitted numberSame source numbers).proof.refuses_changed_conclusion claim
  exact (compile_conclusion element admitted numberSame source numbers) ▸ different

#print axioms premises_exact
#print axioms admittedRecovery
#print axioms admittedRecovery_free
#print axioms recoveryProof
#print axioms recoveryProof_free
#print axioms compile_accepted
#print axioms compile_hypotheses
#print axioms compile_conclusion
#print axioms compile_refuses_changed_conclusion

end Mettapedia.Languages.HOLLight.SourceIndexedVectorTreeStoredPayloadRecoveryCompilation
