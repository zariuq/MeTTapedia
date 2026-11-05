import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeJudgmentProofs
import Mettapedia.Logic.HOL.SetSumProjectionProofs

/-!
# Retained source dependent pairs and projections

Pair introduction and both projections use the constructed dependent sum.
The second field is transported along the first projection's explicit
computation and the source family-instantiation equation. Every source
judgment keeps its original context guard.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.SumProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetMembershipProofs
open AbstractionProofs (code opened)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

def pairAt {n : Nat} (left right domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftProof : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code left bound) (code domain bound)))
    (rightProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (member core (code right bound) (code (CTm.inst0 left family) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (member core (code (.pair left right) bound) (code (.sigma domain family) bound)) :=
  transportBound core _ (.eqSymm (SetCodeOperators.binaryBeta core epsilon .sum (code domain bound) (.lam (opened family bound))))
    (transportValue core _ (.eqSymm (SetCodeOperators.binaryBeta core epsilon .pair (code left bound) (code right bound)))
      (SetDependentSumProofs.introduce core epsilon (code domain bound) (.lam (opened family bound))
        (code left bound) (code right bound) sets.pairing sets.union leftProof
        (transportBound core _ (.eqSymm (JudgmentProofs.familyBeta family left bound)) rightProof)))

def fieldsAt {n : Nat} (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code pair bound) (code (.sigma domain family) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (.and
      (member core (SetPairProjectionProofs.first core epsilon (code pair bound)) (code domain bound))
      (.and (member core (SetPairProjectionProofs.second core epsilon (code pair bound))
        (.app (.lam (opened family bound)) (SetPairProjectionProofs.first core epsilon (code pair bound))))
        (.eq (SetPairingProofs.ordered core epsilon (SetPairProjectionProofs.first core epsilon (code pair bound))
          (SetPairProjectionProofs.second core epsilon (code pair bound))) (code pair bound)))) :=
  SetSumProjectionProofs.typedFields core epsilon (code domain bound) (.lam (opened family bound)) (code pair bound)
    sets.pairing sets.union (transportBound core _
      (SetCodeOperators.binaryBeta core epsilon .sum (code domain bound) (.lam (opened family bound))) received)

def firstAt {n : Nat} (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code pair bound) (code (.sigma domain family) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (member core (code (.fst pair) bound) (code domain bound)) :=
  transportValue core _ (.eqSymm (SetCodeOperators.unaryBeta core epsilon .first (code pair bound)))
    (.andEL (fieldsAt pair domain family bound sets received))

def secondAt {n : Nat} (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code pair bound) (code (.sigma domain family) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (member core (code (.snd pair) bound) (code (CTm.inst0 (.fst pair) family) bound)) :=
  transportBound core _ (JudgmentProofs.familyBeta family (.fst pair) bound)
    (transportBound core _ (.eqAppArg (.lam (opened family bound))
      (.eqSymm (SetCodeOperators.unaryBeta core epsilon .first (code pair bound))))
      (transportValue core _ (.eqSymm (SetCodeOperators.unaryBeta core epsilon .second (code pair bound)))
        (.andEL (.andER (fieldsAt pair domain family bound sets received)))))

theorem pairAt_free {n : Nat} (left right domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftProof : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code left bound) (code domain bound)))
    (rightProof : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code right bound) (code (CTm.inst0 left family) bound)))
    (setsFree : sets.Free) (leftFree : leftProof.FunctionExtensionalityFree) (rightFree : rightProof.FunctionExtensionalityFree) :
    (pairAt left right domain family bound sets leftProof rightProof).FunctionExtensionalityFree :=
  transportBound_free core _ _ _ (SetCodeOperators.binaryBeta_free core epsilon .sum _ _)
    (transportValue_free core _ _ _ (SetCodeOperators.binaryBeta_free core epsilon .pair _ _)
      (SetDependentSumProofs.introduce_free core epsilon _ _ _ _ sets.pairing sets.union _ _ setsFree.pairing setsFree.union
        leftFree (transportBound_free core _ _ _ (JudgmentProofs.familyBeta_free family left bound) rightFree)))

theorem fieldsAt_free {n : Nat} (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code pair bound) (code (.sigma domain family) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (fieldsAt pair domain family bound sets received).FunctionExtensionalityFree :=
  SetSumProjectionProofs.typedFields_free core epsilon _ _ _ sets.pairing sets.union _ setsFree.pairing setsFree.union
    (transportBound_free core _ _ _ (SetCodeOperators.binaryBeta_free core epsilon .sum _ _) receivedFree)

theorem firstAt_free {n : Nat} (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code pair bound) (code (.sigma domain family) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (firstAt pair domain family bound sets received).FunctionExtensionalityFree :=
  transportValue_free core _ _ _ (SetCodeOperators.unaryBeta_free core epsilon .first _)
    (fieldsAt_free pair domain family bound sets received setsFree receivedFree)

theorem secondAt_free {n : Nat} (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code pair bound) (code (.sigma domain family) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (secondAt pair domain family bound sets received).FunctionExtensionalityFree :=
  transportBound_free core _ _ _ (JudgmentProofs.familyBeta_free family (.fst pair) bound)
    (transportBound_free core _ _ _ (SetCodeOperators.unaryBeta_free core epsilon .first _)
      (transportValue_free core _ _ _ (SetCodeOperators.unaryBeta_free core epsilon .second _)
        (fieldsAt_free pair domain family bound sets received setsFree receivedFree)))

def pairJudgment {n : Nat} (context : CCtx Head n) (left right domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context left domain) bound)))
    (rightProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context right (CTm.inst0 left family)) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context (.pair left right) (.sigma domain family)) bound)) :=
  JudgmentProofs.closeTyping context (.pair left right) (.sigma domain family) bound
    (pairAt left right domain family bound (sets.prepend _) (JudgmentProofs.openTyping context left domain bound leftProof)
      (JudgmentProofs.openTyping context right (CTm.inst0 left family) bound rightProof))

def firstJudgment {n : Nat} (context : CCtx Head n) (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context pair (.sigma domain family)) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context (.fst pair) domain) bound)) :=
  JudgmentProofs.closeTyping context (.fst pair) domain bound
    (firstAt pair domain family bound (sets.prepend _) (JudgmentProofs.openTyping context pair (.sigma domain family) bound received))

def secondJudgment {n : Nat} (context : CCtx Head n) (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context pair (.sigma domain family)) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context (.snd pair) (CTm.inst0 (.fst pair) family)) bound)) :=
  JudgmentProofs.closeTyping context (.snd pair) (CTm.inst0 (.fst pair) family) bound
    (secondAt pair domain family bound (sets.prepend _) (JudgmentProofs.openTyping context pair (.sigma domain family) bound received))

theorem pairJudgment_free {n : Nat} (context : CCtx Head n) (left right domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (leftProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context left domain) bound)))
    (rightProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context right (CTm.inst0 left family)) bound)))
    (setsFree : sets.Free) (leftFree : leftProof.FunctionExtensionalityFree) (rightFree : rightProof.FunctionExtensionalityFree) :
    (pairJudgment context left right domain family bound sets leftProof rightProof).FunctionExtensionalityFree :=
  JudgmentProofs.closeTyping_free context _ _ bound _
    (pairAt_free left right domain family bound _ _ _ (sets.prepend_free _ setsFree)
      (JudgmentProofs.openTyping_free context left domain bound leftProof leftFree)
      (JudgmentProofs.openTyping_free context right (CTm.inst0 left family) bound rightProof rightFree))

theorem firstJudgment_free {n : Nat} (context : CCtx Head n) (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context pair (.sigma domain family)) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (firstJudgment context pair domain family bound sets received).FunctionExtensionalityFree :=
  JudgmentProofs.closeTyping_free context _ _ bound _
    (firstAt_free pair domain family bound _ _ (sets.prepend_free _ setsFree)
      (JudgmentProofs.openTyping_free context pair (.sigma domain family) bound received receivedFree))

theorem secondJudgment_free {n : Nat} (context : CCtx Head n) (pair domain : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context pair (.sigma domain family)) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (secondJudgment context pair domain family bound sets received).FunctionExtensionalityFree :=
  JudgmentProofs.closeTyping_free context _ _ bound _
    (secondAt_free pair domain family bound _ _ (sets.prepend_free _ setsFree)
      (JudgmentProofs.openTyping_free context pair (.sigma domain family) bound received receivedFree))

def firstBetaAt {n : Nat} (left right : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ) :
    ProofSyntax (PrimitiveSymbol Head) Δ (.eq (code (.fst (.pair left right)) bound) (code left bound)) :=
  .eqTrans (.eqAppArg (weakenCtx Γ (SetCode.body .first))
    (SetCodeOperators.binaryBeta core epsilon .pair (code left bound) (code right bound)))
    (.eqTrans (SetCodeOperators.unaryBeta core epsilon .first (SetPairingProofs.ordered core epsilon (code left bound) (code right bound)))
      (.andEL (SetPairProjectionProofs.beta core epsilon (code left bound) (code right bound) sets)))

def secondBetaAt {n : Nat} (left right : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ) :
    ProofSyntax (PrimitiveSymbol Head) Δ (.eq (code (.snd (.pair left right)) bound) (code right bound)) :=
  .eqTrans (.eqAppArg (weakenCtx Γ (SetCode.body .second))
    (SetCodeOperators.binaryBeta core epsilon .pair (code left bound) (code right bound)))
    (.eqTrans (SetCodeOperators.unaryBeta core epsilon .second (SetPairingProofs.ordered core epsilon (code left bound) (code right bound)))
      (.andER (SetPairProjectionProofs.beta core epsilon (code left bound) (code right bound) sets)))

theorem firstBetaAt_free {n : Nat} (left right : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ) (free : sets.Free) :
    (firstBetaAt left right bound sets).FunctionExtensionalityFree :=
  ⟨SetCodeOperators.binaryBeta_free core epsilon .pair _ _,
    SetCodeOperators.unaryBeta_free core epsilon .first _,SetPairProjectionProofs.beta_free core epsilon _ _ sets free⟩

theorem secondBetaAt_free {n : Nat} (left right : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ) (free : sets.Free) :
    (secondBetaAt left right bound sets).FunctionExtensionalityFree :=
  ⟨SetCodeOperators.binaryBeta_free core epsilon .pair _ _,
    SetCodeOperators.unaryBeta_free core epsilon .second _,SetPairProjectionProofs.beta_free core epsilon _ _ sets free⟩

def firstBetaJudgment {n : Nat} (context : CCtx Head n) (left right domain : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context left domain) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context (.fst (.pair left right)) left domain) bound)) :=
  JudgmentProofs.closeEquality context (.fst (.pair left right)) left domain bound
    (firstBetaAt left right bound (sets.prepend _))
    (transportValue core _ (.eqSymm (firstBetaAt left right bound (sets.prepend _)))
      (JudgmentProofs.openTyping context left domain bound received))

def secondBetaJudgment {n : Nat} (context : CCtx Head n) (left right : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context right (CTm.inst0 left family)) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt
      (.equality context (.snd (.pair left right)) right (CTm.inst0 left family)) bound)) :=
  JudgmentProofs.closeEquality context (.snd (.pair left right)) right (CTm.inst0 left family) bound
    (secondBetaAt left right bound (sets.prepend _))
    (transportValue core _ (.eqSymm (secondBetaAt left right bound (sets.prepend _)))
      (JudgmentProofs.openTyping context right (CTm.inst0 left family) bound received))

theorem firstBetaJudgment_free {n : Nat} (context : CCtx Head n) (left right domain : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context left domain) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (firstBetaJudgment context left right domain bound sets received).FunctionExtensionalityFree :=
  JudgmentProofs.closeEquality_free context _ _ _ bound _ _
    (firstBetaAt_free left right bound _ (sets.prepend_free _ setsFree))
    (transportValue_free core _ _ _ (firstBetaAt_free left right bound _ (sets.prepend_free _ setsFree))
      (JudgmentProofs.openTyping_free context left domain bound received receivedFree))

theorem secondBetaJudgment_free {n : Nat} (context : CCtx Head n) (left right : CTm Head n) (family : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetPairingProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context right (CTm.inst0 left family)) bound)))
    (setsFree : sets.Free) (receivedFree : received.FunctionExtensionalityFree) :
    (secondBetaJudgment context left right family bound sets received).FunctionExtensionalityFree :=
  JudgmentProofs.closeEquality_free context _ _ _ bound _ _
    (secondBetaAt_free left right bound _ (sets.prepend_free _ setsFree))
    (transportValue_free core _ _ _ (secondBetaAt_free left right bound _ (sets.prepend_free _ setsFree))
      (JudgmentProofs.openTyping_free context right (CTm.inst0 left family) bound received receivedFree))

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.SumProofs
