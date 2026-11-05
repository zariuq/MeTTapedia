import Mettapedia.Logic.HOL.PairingSchemaParameters
import Mettapedia.Languages.HOLLight.InterpretedCompilation
import Mettapedia.Languages.HOLLight.CachedSubstitution
import Mettapedia.Languages.HOLLight.CertifiedBlockAppend

/-!
# Cached native pairing reconstruction at explicit typed operations

The generic certificate is compiled with small operation parameters. Native
substitution supplies the actual operation terms in two primitive inferences.
Its membership premise remains to be discharged. The exact native substitution
image is retained; concrete representations also require their beta conversions.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.PairingSchemaCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open ReverseTranslation
def label (scope : String) : {type : HOL.Ty Unit} → HOL.PairingSchemaParameters.Symbol type → String
  | _, .membership => scope++"/membership"
  | _, .pairing => scope++"/pairing"
  | _, .left => scope++"/left"
  | _, .right => scope++"/right"
  | _, .first => scope++"/first"
  | _, .second => scope++"/second"

def parameter (name : String) (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol type :=
  .const (.variable ⟨.global name,reverseTy type⟩ (toHOL_reverseTy type))

def reading (object : HOL.Ty AtomicTy) (scope : String) :
    HOL.TermInterpretation Unit HOL.PairingSchemaParameters.Symbol AtomicTy Symbol where
  types := fun _ => object
  constants := fun {type} symbol =>
    parameter (label scope symbol) (HOL.Ty.substitute (fun _ => object) type)

@[irreducible, noinline] def compiled (object : HOL.Ty AtomicTy) (scope : String) :=
  InterpretedCompilation.compile (reading object scope) HOL.PairingSchemaParameters.proof
    HOL.PairingSchemaParameters.proof_free Naming.empty (scope,0)

/-- The cache key is computed from the statement, without constructing its proof. -/
def expected (object : HOL.Ty AtomicTy) (scope : String) : Theorem :=
  Theorem.emptyResult
    (reverseHypotheses Naming.empty
      (([HOL.PairingSchemaParameters.schema].map (reading object scope).term).map HOL.ImpredicativeConnectives.expand))
    (reverseCanonical Naming.empty
      (HOL.ImpredicativeConnectives.expand ((reading object scope).term HOL.PairingSchemaParameters.claim)))

private theorem checked_axioms (proof : RetainedCompilation.CheckedProof emptyAxiomPolicy) :
    proof.result.axioms = ∅ :=
  axioms_eq_empty_of_emptyAxiomPolicy (derives_shared emptyAxiomPolicy
    ((ProofSystem.checker_authority emptyAxiomPolicy).sound _ _ proof.accepted))

theorem compiled_expected (object : HOL.Ty AtomicTy) (scope : String) :
    (compiled object scope).proof.result = expected object scope := by
  apply HasParts.eq
  exact ⟨checked_axioms (compiled object scope).proof,
    (compiled object scope).hypotheses_exact,(compiled object scope).conclusion_exact⟩

structure Arguments (object : HOL.Ty AtomicTy) where
  membership : HOL.ClosedTerm Symbol (.arr object (.arr object .prop))
  pairing : HOL.ClosedTerm Symbol (.arr object (.arr object object))
  left : HOL.ClosedTerm Symbol object
  right : HOL.ClosedTerm Symbol object
  first : HOL.ClosedTerm Symbol object
  second : HOL.ClosedTerm Symbol object

private def replacement {type : HOL.Ty AtomicTy} (name : String) (term : HOL.ClosedTerm Symbol type) :
    {entry : SourceVar × CheckedSourceTerm // entry.2.ty = entry.1.ty} :=
  let canonical := reverseCanonical Naming.empty (HOL.ImpredicativeConnectives.expand term)
  ⟨(⟨.global name,canonical.ty⟩,PrimitiveTransport.checkedSource canonical),
    congrArg CanonicalTerm.ty (PrimitiveTransport.checkedSource_exact canonical)⟩

def entries {object : HOL.Ty AtomicTy} (scope : String) (args : Arguments object) := [
  replacement (scope++"/membership") args.membership,
  replacement (scope++"/pairing") args.pairing,
  replacement (scope++"/left") args.left,
  replacement (scope++"/right") args.right,
  replacement (scope++"/first") args.first,
  replacement (scope++"/second") args.second]

def substitution {object : HOL.Ty AtomicTy} (scope : String) (args : Arguments object) :
    TypeCorrectTermSubstitution where
  raw := ⟨TypeSubst.empty,(entries scope args).map Subtype.val⟩
  typeCorrect := by
    intro entry member
    obtain ⟨typed,_,rfl⟩ := List.mem_map.mp member
    exact typed.property

def result {object : HOL.Ty AtomicTy} (scope : String) (args : Arguments object) : Theorem :=
  substituteTheorem (substitution scope args) (expected object scope)

def specialize? {object : HOL.Ty AtomicTy} (scope : String) (args : Arguments object)
    (state : ProofExecution.State) (sourceRoot : Nat) (origin : ProofExecution.Origin) :
    Option (ProofExecution.State × Nat) :=
  CachedSubstitution.applyExpected? emptyAxiomPolicy state sourceRoot
    (expected object scope) (substitution scope args) origin

theorem specialize_checked {object : HOL.Ty AtomicTy} (scope : String) (args : Arguments object)
    {premises : List Theorem} {state : ProofExecution.State} {sourceRoot : Nat}
    (earlier : GraphExpansion.BuildChecked emptyAxiomPolicy premises state)
    (found : state.cache[sourceRoot]? = some (expected object scope))
    (origin : ProofExecution.Origin) :
    ∃ after root, specialize? scope args state sourceRoot origin = some (after,root) ∧
      GraphExpansion.BuildChecked emptyAxiomPolicy premises after ∧
      after.cache[root]? = some (result scope args) ∧ after.receipts.size = state.receipts.size+2 ∧
      after.receipts.toList = state.receipts.toList ++
        (GraphExpansion.expandBlock [sourceRoot] state.cache.size
          (PrimitiveTransport.substitutionBlock (substitution scope args) (expected object scope) origin)).1 ∧
      ∀ (index : Nat) (fact : Theorem), state.cache[index]? = some fact → after.cache[index]? = some fact :=
  CachedSubstitution.applyExpected_checked earlier found (substitution scope args) origin

theorem result_axioms {object : HOL.Ty AtomicTy} (scope : String) (args : Arguments object) :
    (result scope args).axioms = ∅ := rfl

end Mettapedia.Languages.HOLLight.PairingSchemaCompilation

