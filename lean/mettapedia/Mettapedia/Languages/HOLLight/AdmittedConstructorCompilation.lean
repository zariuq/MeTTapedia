import Mettapedia.GSLT.LanguageDef.AdmittedContainerHOLControls
import Mettapedia.Languages.HOLLight.InterpretedCompilation
import Mettapedia.Tools.StageData

/-!
# Retained constructor proofs at supplied native operations

The Vector panel uses the finite descriptor whose equality to the complete
admitted source inventory is checked in `AdmittedContainerHOLControls`.
Semantic evaluation of the source natural carrier is not executed by the
proof producer. The explicit interpretation supplies actual closed arithmetic
terms; native symbol admission and provenance remain separate checks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Mettapedia.Languages.HOLLight.AdmittedConstructorCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef
open AdmittedContainerHOLControls
open ReverseTranslation

local macro "stageVector% " value:term : term =>
  `(stageValue% [Mettapedia.GSLT.LanguageDef.AdmittedContainerHOLControls,
    Mettapedia.Logic.HOL.IndexedContainerPositionTerms,
    Mettapedia.Logic.HOL.IndexedConstructorTerms,
    Mettapedia.TypeTheory.IndexedPositiveContainer,
    Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge,
    Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL,
    Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTerms,
    Mettapedia.Logic.HOL.ConstructorDataPredicates,
    Mettapedia.Logic.HOL.FiniteConstructorEncoding,
    Mettapedia.Logic.HOL.CurriedPredicates,
    Mettapedia.Logic.HOL.IndexedConstructorGuards,
    List, Fin] $value)

def computationProof := stageVector% AdmittedVector.computationProof
def payloadProof := stageVector% AdmittedVector.payloadProof
def indexedProof := stageVector% AdmittedVector.indexedProof

theorem computationProof_source : HEq computationProof AdmittedVector.computationProof :=
  stagedHEq% computationProof, AdmittedVector.computationProof
theorem payloadProof_source : HEq payloadProof AdmittedVector.payloadProof :=
  stagedHEq% payloadProof, AdmittedVector.payloadProof
theorem indexedProof_source : HEq indexedProof AdmittedVector.indexedProof :=
  stagedHEq% indexedProof, AdmittedVector.indexedProof

theorem computationProof_free : computationProof.FunctionExtensionalityFree :=
  stagedProof% AdmittedVector.computationProof_free
theorem payloadProof_free : payloadProof.FunctionExtensionalityFree :=
  stagedProof% AdmittedVector.payloadProof_free
theorem indexedProof_free : indexedProof.FunctionExtensionalityFree :=
  stagedProof% AdmittedVector.indexedProof_free

abbrev Arithmetic := IndexedInductiveHOLTerms.Arithmetic Symbol
variable (operations : Arithmetic)

def types : IndexedInductiveHOLTerms.Controls.SortCode → HOL.Ty AtomicTy
  | .number => operations.number
  | .element => operations.element

def constants : {type : HOL.Ty IndexedInductiveHOLTerms.Controls.SortCode} →
    IndexedInductiveHOLTerms.Controls.Symbol type → HOL.ClosedTerm Symbol (HOL.Ty.substitute (types operations) type)
  | _, .zero => operations.zero
  | _, .successor => operations.successor
  | _, .addition => operations.addition

def interpretation : HOL.TermInterpretation IndexedInductiveHOLTerms.Controls.SortCode
    IndexedInductiveHOLTerms.Controls.Symbol AtomicTy Symbol :=
  ⟨types operations, constants operations⟩

def names : Naming (AdmittedVector.context.map (HOL.Ty.substitute (types operations))) :=
  Naming.cons (Name.global "__constructor_head")
    (Naming.cons (Name.global "__constructor_length") Naming.empty)

def vectorComputation := InterpretedCompilation.compile (interpretation operations)
  computationProof computationProof_free (names operations) ("admitted-vector-result", 0)
def vectorPayload := InterpretedCompilation.compile (interpretation operations)
  payloadProof payloadProof_free (names operations) ("admitted-vector-payload", 0)
def vectorIndexed := InterpretedCompilation.compile (interpretation operations)
  indexedProof indexedProof_free (names operations) ("admitted-vector-indexed", 0)

theorem vectorComputation_accepted :
    (ProofSystem.checker emptyAxiomPolicy).check (vectorComputation operations).proof.result
      (vectorComputation operations).proof.certificate = true := (vectorComputation operations).proof.accepted

theorem vectorIndexed_accepted :
    (ProofSystem.checker emptyAxiomPolicy).check (vectorIndexed operations).proof.result
      (vectorIndexed operations).proof.certificate = true := (vectorIndexed operations).proof.accepted

def parameterInterpretation : HOL.TermInterpretation Unit
    IndexedContainerPositionTermsControls.Symbol AtomicTy Symbol where
  types _ := operations.number
  constants := fun {_} symbol => match symbol with
    | .zero => operations.zero
    | .successor => operations.successor

def parameterField := InterpretedCompilation.compile (parameterInterpretation operations)
  Parameter.fieldProof Parameter.fieldProof_free Naming.empty ("parameter-field", 0)
def parameterPayload := InterpretedCompilation.compile (parameterInterpretation operations)
  Parameter.payloadProof Parameter.payloadProof_free Naming.empty ("parameter-payload", 0)
def parameterIndexed := InterpretedCompilation.compile (parameterInterpretation operations)
  Parameter.indexedProof Parameter.indexedProof_free Naming.empty ("parameter-indexed", 0)

theorem parameterIndexed_accepted :
    (ProofSystem.checker emptyAxiomPolicy).check (parameterIndexed operations).proof.result
      (parameterIndexed operations).proof.certificate = true := (parameterIndexed operations).proof.accepted

#print axioms vectorIndexed_accepted
#print axioms parameterIndexed_accepted
end Mettapedia.Languages.HOLLight.AdmittedConstructorCompilation
