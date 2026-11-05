import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchTabulation
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredParentApplication
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllFromChildren
import Mettapedia.Logic.HOL.ContextualChildArrayCongruence
import Mettapedia.Logic.HOL.ContextualChildPredicateMonotonicity

/-!
# Applying an original source case to an admitted stored branch

The original strengthened induction contract supplies the children. Its least
projection constructs an actual native Vector, while pointwise reconstruction
transports the complete induction contract to that Vector's child function.
The original All producer then builds the case argument. The final parent
transport retains its explicit eta license. Neither a chosen Vector image nor
All evidence nor the parent conclusion is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchCase
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
namespace Native
export IndexedVectorTreeSourceCaseGuardReadback.Native (Base Const N E V W original pairs witness selection)
end Native
open Native
namespace Reverse
export IndexedVectorTreeStoredBranchTabulation (contract vectorMember childRoundtrip)
end Reverse
namespace All
export IndexedVectorTreeNativeAllFromChildren (inductionPredicate produce)
end All
namespace Parent
export IndexedVectorTreeStoredParentApplication (arrays family signature program vector rebuilt payload parent parentViaEta parentViaEta_not_free)
end Parent

variable {Γ : Ctx Base} {A : Ty Base} {Δ : List (Formula Const Γ)}
  (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (one : ClosedTerm Const N) (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)
  (tabulationSelection : ClosedTerm Const (VectorTabulation.Shifted.Selection (Parent.arrays elementSelection arraySelection).toSignature))
  (motive : Term Const Γ (E ⇒ W ⇒ .prop)) (branchCase : Term Const Γ (N ⇒ V ⇒ W ⇒ W))
  (n q : Term Const Γ N) (children : Term Const Γ (N ⇒ E))

abbrev signature := Parent.signature given source numbers one tags bottom
abbrev predicate := All.inductionPredicate original given source numbers one tags bottom motive
abbrev payload := Parent.payload given source numbers one tags n q
abbrev vector := Parent.vector elementSelection arraySelection tabulationSelection n children
abbrev rebuilt := Parent.rebuilt elementSelection arraySelection bottom tabulationSelection n children

variable
  (admitted : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
  (conditions : ProofSyntax Const Δ ((signature given source numbers one tags bottom).childConditions
    (predicate given source numbers one tags bottom motive) (payload given source numbers one tags n q) children))

@[irreducible] def leastConditions : ProofSyntax Const Δ
    (Reverse.contract (Parent.arrays elementSelection arraySelection) given source numbers one tags bottom n q children) :=
  (signature given source numbers one tags bottom).childConditions_mono
    (predicate given source numbers one tags bottom motive) (signature given source numbers one tags bottom).least
    (payload given source numbers one tags n q) children
    (PredicateFixedPoint.intersection_left _ _) conditions

variable
  (tabulation : VectorTabulation.Shifted.ComputationPremises (Parent.arrays elementSelection arraySelection) tabulationSelection Δ)
  (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
  (arrays : (Parent.arrays elementSelection arraySelection).ComputationPremises Δ)

@[irreducible] def vectorMember : ProofSyntax Const Δ
    ((Parent.arrays elementSelection arraySelection).toSignature.member
      (Parent.family given source numbers one tags bottom) n
      (vector elementSelection arraySelection tabulationSelection n children)) :=
  Reverse.vectorMember (Parent.arrays elementSelection arraySelection) given source numbers one tags bottom
    tabulationSelection n q children tabulation arithmetic.induction admitted
    (leastConditions elementSelection arraySelection given source numbers one tags bottom motive n q children conditions)

@[irreducible] def pointwise : ProofSyntax Const Δ
    (VectorTabulation.Shifted.pointwiseFormula
      (rebuilt elementSelection arraySelection bottom tabulationSelection n children) children) :=
  Reverse.childRoundtrip (Parent.arrays elementSelection arraySelection) given source numbers one tags bottom
    tabulationSelection n q children tabulation arithmetic arrays admitted
    (leastConditions elementSelection arraySelection given source numbers one tags bottom motive n q children conditions)

@[irreducible] def reconstructedConditions : ProofSyntax Const Δ
    (IndexedVectorTreeNativeAllFromChildren.contract original elementSelection arraySelection given source numbers one tags bottom motive
      n q (vector elementSelection arraySelection tabulationSelection n children)) :=
  .impE (.eqPropER ((signature given source numbers one tags bottom).childConditions_array_eq
    (predicate given source numbers one tags bottom motive) (payload given source numbers one tags n q)
    (rebuilt elementSelection arraySelection bottom tabulationSelection n children) children
    (pointwise elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays))) conditions

@[irreducible] def vectorGuard : ProofSyntax Const Δ
    (.app (NativeVectorAll.Reading.vectorCode original selection (Parent.family given source numbers one tags bottom) n)
      (vector elementSelection arraySelection tabulationSelection n children)) :=
  .impE (.eqPropER (IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta original selection
    (Parent.family given source numbers one tags bottom) n (vector elementSelection arraySelection tabulationSelection n children)))
    (vectorMember elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic)

variable
  (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ)
  (caseGuard : ProofSyntax Const Δ (.app (IndexedVectorTreeSourceCaseGuardReadback.branchCaseGuardFor
    (Parent.family given source numbers one tags bottom) motive
    (Parent.program elementSelection arraySelection given source numbers one tags bottom)) branchCase))

@[irreducible] def allEvidence : ProofSyntax Const Δ
    (NativeVectorAll.Existence.query original pairs witness selection (Parent.family given source numbers one tags bottom) motive
      n (vector elementSelection arraySelection tabulationSelection n children)) :=
  All.produce original elementSelection arraySelection given source numbers one tags bottom motive pairs witness selection
    n q (vector elementSelection arraySelection tabulationSelection n children) admitted arrays arithmetic
    (vectorMember elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic)
    (reconstructedConditions elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays) allPremises

@[irreducible] def applyViaEta : ProofSyntax Const Δ
    (CurriedPredicates.existsValue [] (.app motive (Parent.parent given source numbers one tags bottom n q children))) :=
  Parent.parentViaEta elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive branchCase
    n q children caseGuard
    (vectorGuard elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic)
    (allEvidence elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays allPremises) admitted
    (pointwise elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays)

theorem applyViaEta_not_free :
    ¬ (applyViaEta elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive branchCase
      n q children admitted conditions tabulation arithmetic arrays allPremises caseGuard).FunctionExtensionalityFree := by
  unfold applyViaEta
  exact Parent.parentViaEta_not_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem leastConditions_free (conditionsFree : conditions.FunctionExtensionalityFree) :
    (leastConditions elementSelection arraySelection given source numbers one tags bottom motive
      n q children conditions).FunctionExtensionalityFree := by
  unfold leastConditions
  exact (signature given source numbers one tags bottom).childConditions_mono_free _ _ _ _ _ _
    (PredicateFixedPoint.intersection_left_free _ _) conditionsFree

theorem vectorMember_free
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free) :
    (vectorMember elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic).FunctionExtensionalityFree := by
  unfold vectorMember
  apply IndexedVectorTreeStoredBranchTabulation.vectorMember_free
  · exact tabulationFree
  · exact arithmeticFree.2.2
  · exact admittedFree
  · exact leastConditions_free elementSelection arraySelection given source numbers one tags bottom motive
      n q children conditions conditionsFree

theorem pointwise_free
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) :
    (pointwise elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays).FunctionExtensionalityFree := by
  unfold pointwise
  apply IndexedVectorTreeStoredBranchTabulation.childRoundtrip_free
  · exact tabulationFree
  · exact arithmeticFree
  · exact arraysFree
  · exact admittedFree
  · exact leastConditions_free elementSelection arraySelection given source numbers one tags bottom motive
      n q children conditions conditionsFree

theorem reconstructedConditions_free
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) :
    (reconstructedConditions elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays).FunctionExtensionalityFree := by
  unfold reconstructedConditions
  exact ⟨(signature given source numbers one tags bottom).childConditions_array_eq_free _ _ _ _ _
    (pointwise_free elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays admittedFree conditionsFree tabulationFree arithmeticFree arraysFree),
    conditionsFree⟩

theorem vectorGuard_free
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free) :
    (vectorGuard elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic).FunctionExtensionalityFree := by
  unfold vectorGuard
  exact ⟨IndexedVectorTreeNativeChildConditions.ReaderGuard.vector_beta_free _ _ _ _ _,
    vectorMember_free elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic admittedFree conditionsFree tabulationFree arithmeticFree⟩

theorem allEvidence_free
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (allFree : allPremises.FunctionExtensionalityFree) :
    (allEvidence elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays allPremises).FunctionExtensionalityFree := by
  unfold allEvidence
  apply IndexedVectorTreeNativeAllFromChildren.produce_free
  · exact admittedFree
  · exact arraysFree
  · exact arithmeticFree
  · exact vectorMember_free elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic admittedFree conditionsFree tabulationFree arithmeticFree
  · exact reconstructedConditions_free elementSelection arraySelection given source numbers one tags bottom tabulationSelection motive
      n q children admitted conditions tabulation arithmetic arrays admittedFree conditionsFree tabulationFree arithmeticFree arraysFree
  · exact allFree

#print axioms applyViaEta
#print axioms applyViaEta_not_free
#print axioms allEvidence_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchCase
