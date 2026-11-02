import Mettapedia.Languages.HOLLight.SourceFiniteConstructorFieldEmbeddingCompilation
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecovery
import Mettapedia.Logic.HOL.NaturalNumeralProofs

/-!
# Source-backed compilation of full stored Vector-tree uniqueness

The admitted source payload supplies the complete solved/branch raw
signature. Its existing field embedding, source selections and constructor
law produce guarded uniqueness for the actual parsed stored constructor.
The original element predicate and numeric predicate remain explicit.

Compilation uses the common retained-proof compiler under the empty axiom
policy. Its three provider hypotheses remain exact: source selection for
the complete raw payload, source selection for the independent element type,
and the source constructor law. The admitted payload instance alone does
not discharge those hypotheses. Source-profile installation and cuts against
checked provider roots, then external native replay, remain separate joins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SourceIndexedVectorTreeStoredConstructorRecoveryCompilation

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef

variable {policy : AxiomPolicy} [DecidablePred policy] {before : ProofExecution.Registered.State}
  {operations : RecursiveSpaceSourceReadback.Operations} {parameter : Name}
  (element : Ty)
  (admitted : AdmittedSourcePayloads.Instance policy before operations parameter
    (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element))
  (numberSame : (AdmittedSourcePayloads.targetOperations operations parameter
    (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)).number = operations.number)

abbrev inputs := SourceFiniteConstructorFieldEmbeddingCompilation.nativeInputs element admitted numberSame

def premises : List (HOL.ClosedFormula Symbol) :=
  SourceFiniteConstructorFieldEmbeddingCompilation.premises
    (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame)

theorem premises_exact : premises element admitted numberSame =
    [SourceSelectionProfile.native
      (AdmittedSourcePayloads.payload (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)),
      SourceSelectionProfile.native element,
      ConstructorInjectivityProfile.native (AdmittedSourcePayloads.targetOperations operations parameter
        (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)).recursive] :=
  SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted_premises element admitted numberSame

theorem premise_count : (premises element admitted numberSame).length = 3 := rfl

def tags (number : Nat) : HOL.ClosedTerm Symbol operations.number.toHOL :=
  HOL.NaturalNumeralProofs.numeral operations.natural.zero operations.natural.successor number

def bottom : HOL.ClosedTerm Symbol
    (AdmittedSourcePayloads.targetOperations operations parameter
      (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)).space.toHOL :=
  (AdmittedSourcePayloads.targetOperations operations parameter
    (SourceFiniteConstructorFieldEmbeddingCompilation.vectorFields operations element)).recursive.bottom

variable (source : HOL.ClosedTerm Symbol (element.toHOL.arr .prop))
  (numbers : HOL.ClosedTerm Symbol (operations.number.toHOL.arr .prop))

def domain := IndexedVectorTreeStoredConstructorRecovery.domain (inputs element admitted numberSame)
  source numbers operations.natural.zero (.app operations.natural.successor operations.natural.zero)
  operations.natural.successor (tags (operations := operations)) (bottom (parameter := parameter) element)

def fieldLaw : HOL.ClosedFormula Symbol :=
  HOL.GuardedConstructorProjections.fieldInjective
    (IndexedVectorTreeStoredConstructorRecovery.storedConstructor (inputs element admitted numberSame))
    (domain element admitted numberSame source numbers)

@[irreducible] def fieldInjectivityProof : HOL.ProofSyntax Symbol (premises element admitted numberSame)
    (fieldLaw element admitted numberSame source numbers) :=
  IndexedVectorTreeStoredConstructorRecovery.fieldInjective (inputs element admitted numberSame)
    source numbers operations.natural.zero (.app operations.natural.successor operations.natural.zero)
    operations.natural.successor (tags (operations := operations)) (bottom (parameter := parameter) element)
    (SourceFiniteConstructorFieldEmbeddingCompilation.payloadProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.fieldProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))
    (SourceFiniteConstructorFieldEmbeddingCompilation.constructorProof
      (SourceFiniteConstructorFieldEmbeddingCompilation.fromAdmitted element admitted numberSame))

theorem fieldInjectivityProof_free :
    (fieldInjectivityProof element admitted numberSame source numbers).FunctionExtensionalityFree := by
  unfold fieldInjectivityProof
  exact IndexedVectorTreeStoredConstructorRecovery.fieldInjective_free (inputs element admitted numberSame)
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

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

@[irreducible, noinline] def compile :=
  RetainedCompilation.compileWithoutFunctionExtensionality emptyAxiomPolicy
    (fieldInjectivityProof element admitted numberSame source numbers)
    (fieldInjectivityProof_free element admitted numberSame source numbers)
    ReverseTranslation.Naming.empty ("source-vector-tree-stored-constructor-uniqueness", 0)

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
        (HOL.ImpredicativeConnectives.expand (fieldLaw element admitted numberSame source numbers)) :=
  (compile element admitted numberSame source numbers).conclusion_exact

theorem compile_refuses_changed_conclusion (claim : Theorem)
    (different : claim.sequent.concl ≠ ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty
      (HOL.ImpredicativeConnectives.expand (fieldLaw element admitted numberSame source numbers))) :
    (ProofSystem.checker emptyAxiomPolicy).check claim
      (compile element admitted numberSame source numbers).proof.certificate = false := by
  apply (compile element admitted numberSame source numbers).proof.refuses_changed_conclusion claim
  exact (compile_conclusion element admitted numberSame source numbers) ▸ different

#print axioms premises_exact
#print axioms fieldInjectivityProof
#print axioms fieldInjectivityProof_free
#print axioms compile_accepted
#print axioms compile_hypotheses
#print axioms compile_conclusion
#print axioms compile_refuses_changed_conclusion

end Mettapedia.Languages.HOLLight.SourceIndexedVectorTreeStoredConstructorRecoveryCompilation
