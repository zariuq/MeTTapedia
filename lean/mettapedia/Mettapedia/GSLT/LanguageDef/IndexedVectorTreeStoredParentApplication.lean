import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeSourceCaseApplications
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeConstructorFunctions
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchShapeNormalization
import Mettapedia.Logic.HOL.VectorTabulationObservations
import Mettapedia.Logic.HOL.ConstructorChildExtensionality

/-!
# A source case result at the original stored branch

The Vector is the actual tabulation program, rather than a supplied image.
Its guard, original All query and pointwise reconstruction are explicit proof
interfaces discharged by the reverse-representation components. The admitted
shape proof normalizes only the separate zero field. The final arbitrary
parent observation uses the explicit eta-licensed recipe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplication
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
namespace Native
export IndexedVectorTreeSourceCaseGuardReadback.Native (Base Const N E V W original pairs witness selection)
end Native
open Native
variable {Γ : Ctx Base} {A : Ty Base} {Δ : List (Formula Const Γ)}
  (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (one : ClosedTerm Const N) (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)

abbrev arrays := IndexedVectorTreeConstructorFunctions.Native.arrays original elementSelection arraySelection
def family := IndexedVectorTreeStoredFamily.family given source numbers original.zero one original.successor tags bottom
def signature := IndexedVectorTreeStoredFamily.signature given source numbers original.zero one original.successor tags bottom
def program := IndexedVectorTreeConstructorFunctions.Native.branch original elementSelection arraySelection
  given source numbers one tags bottom

variable (tabulationSelection : ClosedTerm Const (VectorTabulation.Shifted.Selection (arrays elementSelection arraySelection).toSignature))

def vector (n : Term Const Γ N) (children : Term Const Γ (N ⇒ E)) : Term Const Γ V :=
  VectorTabulation.Shifted.tabulate (arrays elementSelection arraySelection).toSignature tabulationSelection n children

def rebuilt (n : Term Const Γ N) (children : Term Const Γ (N ⇒ E)) : Term Const Γ (N ⇒ E) :=
  (arrays elementSelection arraySelection).single n (vector elementSelection arraySelection tabulationSelection n children) bottom

def payload (n q : Term Const Γ N) :=
  IndexedVectorTreeBranchActivity.payload given source numbers original.zero one tags n q

def parent (n q : Term Const Γ N) (children : Term Const Γ (N ⇒ E)) : Term Const Γ E :=
  (signature given source numbers one tags bottom).constructValue (tags 1) (payload given source numbers one tags n q) children

private def existsTransport (motive : Term Const Γ (E ⇒ W ⇒ .prop))
    (first second : Term Const Γ E) (equal : ProofSyntax Const Δ (.eq first second))
    (present : ProofSyntax Const Δ (CurriedPredicates.existsValue [] (.app motive first))) :
    ProofSyntax Const Δ (CurriedPredicates.existsValue [] (.app motive second)) :=
  .impE (.eqPropEL (CurriedPredicates.existsValue_nil_congr _ _ (.eqAppArg motive equal))) present

variable (motive : Term Const Γ (E ⇒ W ⇒ .prop)) (branchCase : Term Const Γ (N ⇒ V ⇒ W ⇒ W))
  (n q : Term Const Γ N) (children : Term Const Γ (N ⇒ E))
  (caseGuard : ProofSyntax Const Δ
    (.app (IndexedVectorTreeSourceCaseGuardReadback.branchCaseGuardFor
      (family given source numbers one tags bottom) motive (program elementSelection arraySelection given source numbers one tags bottom)) branchCase))
  (vectorGuard : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
    (family given source numbers one tags bottom) n) (vector elementSelection arraySelection tabulationSelection n children)))
  (all : ProofSyntax Const Δ (NativeVectorAll.Existence.query original pairs witness selection
    (family given source numbers one tags bottom) motive n (vector elementSelection arraySelection tabulationSelection n children)))
  (admitted : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))

@[irreducible] private def reconstructedParent : ProofSyntax Const Δ
    (CurriedPredicates.existsValue [] (.app motive (parent given source numbers one tags bottom n q
      (rebuilt elementSelection arraySelection bottom tabulationSelection n children)))) := by
  have applied := IndexedVectorTreeSourceCaseApplications.branchExists
    (family given source numbers one tags bottom) motive (program elementSelection arraySelection given source numbers one tags bottom)
    branchCase n (vector elementSelection arraySelection tabulationSelection n children) caseGuard vectorGuard all
  have atCanonical := existsTransport motive _ _
    (IndexedVectorTreeConstructorFunctions.Native.branch_apply original elementSelection arraySelection
      given source numbers one tags bottom n (vector elementSelection arraySelection tabulationSelection n children)) applied
  have shape := IndexedVectorTreeBranchShapeNormalization.payload given source numbers original.zero one tags n q admitted
  have changed : ProofSyntax Const Δ (.eq
      (parent given source numbers one tags bottom n (weakenCtx Γ original.zero)
        (rebuilt elementSelection arraySelection bottom tabulationSelection n children))
      (parent given source numbers one tags bottom n q
        (rebuilt elementSelection arraySelection bottom tabulationSelection n children))) :=
    .eqApp (rebuilt elementSelection arraySelection bottom tabulationSelection n children)
      (.eqAppArg (.app (signature given source numbers one tags bottom).construct (tags 1)) (.eqSymm shape))
  exact existsTransport motive _ _ changed atCanonical

@[irreducible] def parentViaEta
    (pointwise : ProofSyntax Const Δ (VectorTabulation.Shifted.pointwiseFormula
      (rebuilt elementSelection arraySelection bottom tabulationSelection n children) children)) :
    ProofSyntax Const Δ (CurriedPredicates.existsValue [] (.app motive (parent given source numbers one tags bottom n q children))) :=
  (signature given source numbers one tags bottom).parentExistsViaEta (tags 1) (payload given source numbers one tags n q)
    (rebuilt elementSelection arraySelection bottom tabulationSelection n children) children pointwise motive
    (reconstructedParent elementSelection arraySelection given source numbers one tags bottom tabulationSelection
      motive branchCase n q children caseGuard vectorGuard all admitted)

theorem parentViaEta_not_free
    (pointwise : ProofSyntax Const Δ (VectorTabulation.Shifted.pointwiseFormula
      (rebuilt elementSelection arraySelection bottom tabulationSelection n children) children)) :
    ¬ (parentViaEta elementSelection arraySelection given source numbers one tags bottom tabulationSelection
      motive branchCase n q children caseGuard vectorGuard all admitted pointwise).FunctionExtensionalityFree := by
  unfold parentViaEta
  exact RecursiveSpacePredicate.Contextual.parentExistsViaEta_not_free _ _ _ _ _ _ _ _

#print axioms parentViaEta
#print axioms parentViaEta_not_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplication
