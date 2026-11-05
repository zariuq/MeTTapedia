import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeJudgmentProofs
import Mettapedia.Logic.HOL.SetFamilyInclusionProofs

/-!
# Retained source inclusion and dependent-sum subtyping

Subtyping reads as guarded set inclusion. The source body's inclusion is
opened only under its declared domain, then transported to the actual lambda
family applications. Dependent sums preserve domain and fibre inclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.SubtypingProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetMembershipProofs SetInclusionProofs SetFamilyInclusionProofs
open AbstractionProofs (code opened)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

theorem expanded_sub {n : Nat} (context : CCtx Head n) (before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    expand (judgmentAt (.sub context before after) bound) =
      .imp (expand (contextAt context bound)) (included core (code before bound) (code after bound)) := by
  dsimp only [judgmentAt,statementContext,statementAt,memberAt,expand,HOL.substConst]
  dsimp only [images]
  simp only [HOL.weakenCtx_const,HOL.substConst_weaken]
  change Term.imp (expand (contextAt context bound))
    (included core (expand (AnnotatedCodedReading.readAt CodedHOL.operations bound before))
      (expand (AnnotatedCodedReading.readAt CodedHOL.operations bound after))) = _
  rw [expand_readAt,expand_readAt]
  rfl

def openSub {n : Nat} (context : CCtx Head n) (before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound))) :
    ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ) (included core (code before bound) (code after bound)) :=
  .impE (.castIndices rfl (expanded_sub context before after bound) (received.prepend _)) (.hyp 0)

def closeSub {n : Nat} (context : CCtx Head n) (before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ) (included core (code before bound) (code after bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound)) :=
  .castIndices rfl (expanded_sub context before after bound).symm (.impI proof)

def fromEqualityJudgment {n : Nat} (context : CCtx Head n) (before after levelCode : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context before after levelCode) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound)) :=
  closeSub context before after bound (fromEquality core _ _ (.andEL (JudgmentProofs.openEquality context before after levelCode bound received)))

def transitivityJudgment {n : Nat} (context : CCtx Head n) (first middle last : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (before : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context first middle) bound)))
    (after : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context middle last) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context first last) bound)) :=
  closeSub context first last bound (transitive core _ _ _ (openSub context first middle bound before) (openSub context middle last bound after))

def typingJudgment {n : Nat} (context : CCtx Head n) (value before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (typed : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value before) bound)))
    (inclusion : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value after) bound)) :=
  JudgmentProofs.closeTyping context value after bound
    (subsetElim core _ _ _ (openSub context before after bound inclusion) (JudgmentProofs.openTyping context value before bound typed))

def equalityJudgment {n : Nat} (context : CCtx Head n) (left right before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (typed : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right before) bound)))
    (inclusion : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right after) bound)) :=
  JudgmentProofs.closeEquality context left right after bound
    (.andEL (JudgmentProofs.openEquality context left right before bound typed))
    (subsetElim core _ _ _ (openSub context before after bound inclusion)
      (.andER (JudgmentProofs.openEquality context left right before bound typed)))

def openFamily {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (before after : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.sub (.snoc context domain) before after) (AnnotatedCodedReading.lift bound)))) :
    ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (familyIncluded core (code domain bound) (.lam (opened before bound)) (.lam (opened after bound))) := by
  let guard := expand (contextAt context bound)
  let domainGuard := member core (.var .vz) (HOL.weaken (code domain bound))
  have mapped : (fun index => expand (AnnotatedCodedReading.lift bound index)) =
      AnnotatedCodedReading.lift (fun index => expand (bound index)) := AnnotatedCodedReading.substConst_lift images bound
  have statement : expand (judgmentAt (.sub (.snoc context domain) before after) (AnnotatedCodedReading.lift bound)) =
      Term.imp (.and (HOL.weaken guard) domainGuard) (included core (opened before bound) (opened after bound)) := by
    rw [expanded_sub,ContextProofs.expanded_context_lift]
    dsimp only [code,opened]
    rw [mapped]
  have localProof : ProofSyntax (PrimitiveSymbol Head) (domainGuard :: weakenHyps (σ := object) (guard :: Δ))
      (included core (opened before bound) (opened after bound)) :=
    .impE (.castIndices rfl statement ((received.prepend (HOL.weaken guard)).prepend domainGuard)) (.andI (.hyp 1) (.hyp 0))
  exact .allI (.impI (transportEndpoints core (.eqSymm (ProofSyntax.betaAtFresh (opened before bound)))
    (.eqSymm (ProofSyntax.betaAtFresh (opened after bound))) localProof))

def sumJudgment {n : Nat} (context : CCtx Head n) (beforeDomain afterDomain : CTm Head n) (beforeFamily afterFamily : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context beforeDomain afterDomain) bound)))
    (fibres : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.sub (.snoc context beforeDomain) beforeFamily afterFamily) (AnnotatedCodedReading.lift bound)))) :
    ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.sub context (.sigma beforeDomain beforeFamily) (.sigma afterDomain afterFamily)) bound)) :=
  closeSub context _ _ bound (transportEndpoints core
    (.eqSymm (SetCodeOperators.binaryBeta core epsilon .sum (code beforeDomain bound) (.lam (opened beforeFamily bound))))
    (.eqSymm (SetCodeOperators.binaryBeta core epsilon .sum (code afterDomain bound) (.lam (opened afterFamily bound))))
    (sumInclusion core epsilon _ _ _ _ (laws.prepend _) (openSub context beforeDomain afterDomain bound domain)
      (openFamily context beforeDomain beforeFamily afterFamily bound fibres)))

theorem openSub_free {n : Nat} (context : CCtx Head n) (before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound)))
    (free : received.FunctionExtensionalityFree) : (openSub context before after bound received).FunctionExtensionalityFree := by
  unfold openSub
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ((ProofSyntax.functionExtensionalityFree_mono _ received).mpr free),trivial⟩

theorem closeSub_free {n : Nat} (context : CCtx Head n) (before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ) (included core (code before bound) (code after bound)))
    (free : proof.FunctionExtensionalityFree) : (closeSub context before after bound proof).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem fromEqualityJudgment_free {n : Nat} (context : CCtx Head n) (before after levelCode : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context before after levelCode) bound)))
    (free : received.FunctionExtensionalityFree) : (fromEqualityJudgment context before after levelCode bound received).FunctionExtensionalityFree :=
  closeSub_free context _ _ bound _ (fromEquality_free core _ _ _ (JudgmentProofs.openEquality_free context _ _ _ bound received free))

theorem transitivityJudgment_free {n : Nat} (context : CCtx Head n) (first middle last : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (before : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context first middle) bound)))
    (after : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context middle last) bound)))
    (beforeFree : before.FunctionExtensionalityFree) (afterFree : after.FunctionExtensionalityFree) :
    (transitivityJudgment context first middle last bound before after).FunctionExtensionalityFree :=
  closeSub_free context _ _ bound _ (transitive_free core _ _ _ _ _
    (openSub_free context _ _ bound before beforeFree) (openSub_free context _ _ bound after afterFree))

theorem typingJudgment_free {n : Nat} (context : CCtx Head n) (value before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (typed : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value before) bound)))
    (inclusion : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound)))
    (typedFree : typed.FunctionExtensionalityFree) (inclusionFree : inclusion.FunctionExtensionalityFree) :
    (typingJudgment context value before after bound typed inclusion).FunctionExtensionalityFree :=
  JudgmentProofs.closeTyping_free context _ _ bound _ (eliminate_free core _ _ _ _ _
    (openSub_free context _ _ bound inclusion inclusionFree) (JudgmentProofs.openTyping_free context _ _ bound typed typedFree))

theorem equalityJudgment_free {n : Nat} (context : CCtx Head n) (left right before after : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (typed : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right before) bound)))
    (inclusion : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context before after) bound)))
    (typedFree : typed.FunctionExtensionalityFree) (inclusionFree : inclusion.FunctionExtensionalityFree) :
    (equalityJudgment context left right before after bound typed inclusion).FunctionExtensionalityFree :=
  JudgmentProofs.closeEquality_free context _ _ _ bound _ _
    (JudgmentProofs.openEquality_free context _ _ _ bound typed typedFree)
    (eliminate_free core _ _ _ _ _ (openSub_free context _ _ bound inclusion inclusionFree)
      (JudgmentProofs.openEquality_free context _ _ _ bound typed typedFree))

theorem openFamily_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (before after : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.sub (.snoc context domain) before after) (AnnotatedCodedReading.lift bound))))
    (free : received.FunctionExtensionalityFree) : (openFamily context domain before after bound received).FunctionExtensionalityFree := by
  unfold openFamily
  apply transportEndpoints_free
  · exact ProofSyntax.betaAtFresh_free _
  · exact ProofSyntax.betaAtFresh_free _
  · constructor
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_mono _ received).mpr free
    · exact ⟨trivial,trivial⟩

theorem sumJudgment_free {n : Nat} (context : CCtx Head n) (beforeDomain afterDomain : CTm Head n) (beforeFamily afterFamily : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (laws : SetTraceProofs.Laws core epsilon Δ)
    (domain : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.sub context beforeDomain afterDomain) bound)))
    (fibres : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.sub (.snoc context beforeDomain) beforeFamily afterFamily) (AnnotatedCodedReading.lift bound))))
    (lawsFree : laws.Free) (domainFree : domain.FunctionExtensionalityFree) (fibresFree : fibres.FunctionExtensionalityFree) :
    (sumJudgment context beforeDomain afterDomain beforeFamily afterFamily bound laws domain fibres).FunctionExtensionalityFree :=
  closeSub_free context _ _ bound _ (transportEndpoints_free core _ _ _
    (SetCodeOperators.binaryBeta_free core epsilon .sum _ _) (SetCodeOperators.binaryBeta_free core epsilon .sum _ _)
    (sumInclusion_free core epsilon _ _ _ _ _ _ _ (laws.prepend_free _ lawsFree)
      (openSub_free context _ _ bound domain domainFree) (openFamily_free context _ _ _ bound fibres fibresFree)))

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.SubtypingProofs
