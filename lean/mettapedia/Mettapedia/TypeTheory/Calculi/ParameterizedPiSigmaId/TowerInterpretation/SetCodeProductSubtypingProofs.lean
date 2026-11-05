import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeSubtypingProofs
import Mettapedia.Logic.HOL.SetTraceProductInclusionProofs

/-!
# Retained source dependent-product subtyping

The source rule requires equality of domains and fibre inclusion under the
original domain. The retained product construction preserves its support
bound and application guard, then transports the destination domain through
the supplied type-code equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.SubtypingProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetInclusionProofs SetTraceProductInclusionProofs
open AbstractionProofs (code opened)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

def productJudgment {n : Nat} (context : CCtx Head n) (beforeDomain afterDomain levelCode : CTm Head n)
    (beforeFamily afterFamily : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context beforeDomain afterDomain levelCode) bound)))
    (fibres : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.sub (.snoc context beforeDomain) beforeFamily afterFamily) (AnnotatedCodedReading.lift bound)))) :
    ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.sub context (.pi beforeDomain beforeFamily) (.pi afterDomain afterFamily)) bound)) := by
  have equalDomain := JudgmentProofs.openEquality context beforeDomain afterDomain levelCode bound domain
  have domainChange : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (.eq (code (.pi beforeDomain afterFamily) bound) (code (.pi afterDomain afterFamily) bound)) :=
    .eqApp (.lam (opened afterFamily bound)) (.eqAppArg (weakenCtx Γ (SetCode.body .product)) (.andEL equalDomain))
  have familyProof := openFamily context beforeDomain beforeFamily afterFamily bound fibres
  have rawInclusion := ProofSyntax.cut familyProof
    (productInclusion core epsilon (code beforeDomain bound) (.lam (opened beforeFamily bound)) (.lam (opened afterFamily bound))
      ((laws.prepend _).prepend _) (.hyp 0))
  exact closeSub context _ _ bound (transportEndpoints core
    (.eqSymm (SetCodeOperators.binaryBeta core epsilon .product (code beforeDomain bound) (.lam (opened beforeFamily bound))))
    (.eqTrans (.eqSymm (SetCodeOperators.binaryBeta core epsilon .product (code beforeDomain bound) (.lam (opened afterFamily bound))))
      domainChange)
    rawInclusion)

theorem productJudgment_free {n : Nat} (context : CCtx Head n) (beforeDomain afterDomain levelCode : CTm Head n)
    (beforeFamily afterFamily : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context beforeDomain afterDomain levelCode) bound)))
    (fibres : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.sub (.snoc context beforeDomain) beforeFamily afterFamily) (AnnotatedCodedReading.lift bound))))
    (lawsFree : laws.Free) (domainFree : domain.FunctionExtensionalityFree) (fibresFree : fibres.FunctionExtensionalityFree) :
    (productJudgment context beforeDomain afterDomain levelCode beforeFamily afterFamily bound laws domain fibres).FunctionExtensionalityFree := by
  unfold productJudgment
  apply closeSub_free
  apply transportEndpoints_free
  · exact SetCodeOperators.binaryBeta_free core epsilon .product _ _
  · exact ⟨SetCodeOperators.binaryBeta_free core epsilon .product _ _,
      JudgmentProofs.openEquality_free context _ _ _ bound domain domainFree⟩
  · apply ProofSyntax.cut_free
    · exact openFamily_free context _ _ _ bound fibres fibresFree
    · exact productInclusion_free core epsilon _ _ _ _ _
        ((laws.prepend _).prepend_free _ (laws.prepend_free _ lawsFree)) trivial

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.SubtypingProofs
