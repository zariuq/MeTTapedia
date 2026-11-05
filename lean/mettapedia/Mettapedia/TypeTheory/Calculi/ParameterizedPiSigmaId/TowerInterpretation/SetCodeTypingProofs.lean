import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeDefinitions

/-!
# Retained source application and reflexivity over expanded set codes

The producer consumes actual retained proofs of the source function and
argument judgments. It retains their context guard, derives dependent
application typing and returns the exact substituted source result type.
Reflexivity reuses the expanded truth-code body and ordinary set-law proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.TypingProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetMembershipProofs
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}
open AnnotatedCodedReading (readAt lift)

def applicationAt {n : Nat} (function argument domain : CTm Head n) (codomain : CTm Head (n+1))
    (bound : Fin n → Term (PrimitiveSymbol Head) Γ object)
    (sets : SetTraceProofs.Laws core epsilon Δ)
    (functionProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (member core (readAt operations bound function) (readAt operations bound (.pi domain codomain))))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (member core (readAt operations bound argument) (readAt operations bound domain))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (member core (readAt operations bound (.app function argument))
      (readAt operations bound (CTm.inst0 argument codomain))) := by
  let a := readAt operations bound domain
  let b := Term.lam (readAt operations (lift bound) codomain)
  let f := readAt operations bound function
  let x := readAt operations bound argument
  have productEquation : ProofSyntax (PrimitiveSymbol Head) Δ (.eq
      (readAt operations bound (.pi domain codomain)) (SetTraceProductProofs.product core epsilon a b)) :=
    SetCodeOperators.binaryBeta core epsilon .product a b
  have admitted := transportBound core f productEquation functionProof
  have typed := SetTraceProductProofs.applicationTyped core epsilon a b f x sets admitted argumentProof
  have applicationEquation : ProofSyntax (PrimitiveSymbol Head) Δ (.eq
      (readAt operations bound (.app function argument)) (SetTraceProofs.application core epsilon f x)) :=
    SetCodeOperators.binaryBeta core epsilon .application f x
  have familyEquation : ProofSyntax (PrimitiveSymbol Head) Δ (.eq (.app b x)
      (readAt operations bound (CTm.inst0 argument codomain))) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta x (readAt operations (lift bound) codomain))
    rw [AnnotatedCodedReading.readAt_inst0]
  exact transportBound core _ familyEquation
    (transportValue core (.app b x) (.eqSymm applicationEquation) typed)

theorem expanded_typing {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    expand (judgmentAt (.typing context value type) bound) =
      .imp (expand (contextAt context bound))
        (member core (readAt operations (fun index => expand (bound index)) value)
          (readAt operations (fun index => expand (bound index)) type)) := by
  dsimp only [judgmentAt,statementContext,statementAt,memberAt,expand,HOL.substConst]
  dsimp only [images]
  rw [HOL.weakenCtx_const]
  change Term.imp (expand (contextAt context bound))
      (member core (expand (readAt CodedHOL.operations bound value))
        (expand (readAt CodedHOL.operations bound type))) = _
  rw [expand_readAt,expand_readAt]
  rfl

def applicationJudgment {n : Nat} (context : CCtx Head n) (function argument domain : CTm Head n)
    (codomain : CTm Head (n+1)) (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (sets : SetTraceProofs.Laws core epsilon Δ)
    (functionProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.typing context function (.pi domain codomain)) bound)))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.typing context argument domain) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.typing context (.app function argument) (CTm.inst0 argument codomain)) bound)) := by
  let guard := expand (contextAt context bound)
  have functionAt := ProofSyntax.impE
    (ProofSyntax.castIndices rfl (expanded_typing context function (.pi domain codomain) bound)
      (functionProof.prepend guard)) (.hyp 0)
  have argumentAt := ProofSyntax.impE
    (ProofSyntax.castIndices rfl (expanded_typing context argument domain bound)
      (argumentProof.prepend guard)) (.hyp 0)
  exact ProofSyntax.castIndices rfl (expanded_typing context (.app function argument) (CTm.inst0 argument codomain) bound).symm
    (.impI (applicationAt function argument domain codomain (fun index => expand (bound index))
      (sets.prepend guard) functionAt argumentAt))

theorem applicationAt_free {n : Nat} (function argument domain : CTm Head n) (codomain : CTm Head (n+1))
    (bound : Fin n → Term (PrimitiveSymbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (functionProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (member core (readAt operations bound function) (readAt operations bound (.pi domain codomain))))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (member core (readAt operations bound argument) (readAt operations bound domain)))
    (setsFree : sets.Free) (functionFree : functionProof.FunctionExtensionalityFree)
    (argumentFree : argumentProof.FunctionExtensionalityFree) :
    (applicationAt function argument domain codomain bound sets functionProof argumentProof).FunctionExtensionalityFree := by
  unfold applicationAt
  apply transportBound_free
  · simp [ProofSyntax.FunctionExtensionalityFree]
  · apply transportValue_free
    · exact SetCodeOperators.binaryBeta_free core epsilon .application _ _
    · apply SetTraceProductProofs.applicationTyped_free
      · exact setsFree
      · exact transportBound_free core _ _ _ (SetCodeOperators.binaryBeta_free core epsilon .product _ _) functionFree
      · exact argumentFree

theorem applicationJudgment_free {n : Nat} (context : CCtx Head n) (function argument domain : CTm Head n)
    (codomain : CTm Head (n+1)) (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (sets : SetTraceProofs.Laws core epsilon Δ)
    (functionProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.typing context function (.pi domain codomain)) bound)))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ
      (expand (judgmentAt (.typing context argument domain) bound)))
    (setsFree : sets.Free) (functionFree : functionProof.FunctionExtensionalityFree)
    (argumentFree : argumentProof.FunctionExtensionalityFree) :
    (applicationJudgment context function argument domain codomain bound sets functionProof argumentProof).FunctionExtensionalityFree := by
  simp only [applicationJudgment,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  apply applicationAt_free
  · exact sets.prepend_free _ setsFree
  · constructor
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono] using functionFree
    · trivial
  · constructor
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono] using argumentFree
    · trivial

def reflexivityAt {n : Nat} (type value : CTm Head n) (bound : Fin n → Term (PrimitiveSymbol Head) Γ object)
    (powerProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.powerLaw))
    (separationProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax (PrimitiveSymbol Head) Δ (member core (readAt operations bound (.refl value))
      (readAt operations bound (.id type value value))) := by
  have emptyEquation : readAt operations bound (.refl value) = Term.const (core Embedding.ZFSetHenkinInterpretation.Symbol.empty) := by
    simp only [readAt,operations,AnnotatedCodedReading.Operations.mapDefinitions,CodedHOL.operations,
      HOL.substConst,images,HOL.weakenCtx_const]
    rfl
  have receipt := transportBound core _ (.eqSymm (SetCodeOperators.unaryBeta core epsilon .truth
    (.eq (readAt operations bound value) (readAt operations bound value))))
    (identityIntro core (readAt operations bound value) powerProof separationProof)
  apply ProofSyntax.castIndices rfl ?_ receipt
  rw [emptyEquation]
  rfl

def reflexivityJudgment {n : Nat} (context : CCtx Head n) (type value : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (powerProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.powerLaw))
    (separationProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.separationLaw)) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context (.refl value) (.id type value value)) bound)) :=
  ProofSyntax.castIndices rfl (expanded_typing context (.refl value) (.id type value value) bound).symm
    (.impI (reflexivityAt type value (fun index => expand (bound index))
      (powerProof.prepend _) (separationProof.prepend _)))

theorem reflexivityAt_free {n : Nat} (type value : CTm Head n) (bound : Fin n → Term (PrimitiveSymbol Head) Γ object)
    (powerProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.powerLaw))
    (separationProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.separationLaw))
    (powerFree : powerProof.FunctionExtensionalityFree) (separationFree : separationProof.FunctionExtensionalityFree) :
    (reflexivityAt type value bound powerProof separationProof).FunctionExtensionalityFree := by
  unfold reflexivityAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply transportBound_free
  · exact SetCodeOperators.unaryBeta_free core epsilon .truth _
  · exact truthIntro_free core _ powerProof separationProof (.eqRefl (readAt operations bound value)) powerFree separationFree trivial

theorem reflexivityJudgment_free {n : Nat} (context : CCtx Head n) (type value : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (powerProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.powerLaw))
    (separationProof : ProofSyntax (PrimitiveSymbol Head) Δ (lawAt core Embedding.ZFSetHenkinInterpretation.separationLaw))
    (powerFree : powerProof.FunctionExtensionalityFree) (separationFree : separationProof.FunctionExtensionalityFree) :
    (reflexivityJudgment context type value bound powerProof separationProof).FunctionExtensionalityFree := by
  simp only [reflexivityJudgment,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  apply reflexivityAt_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ powerProof).mpr powerFree
  · exact (ProofSyntax.functionExtensionalityFree_mono _ separationProof).mpr separationFree

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.TypingProofs
