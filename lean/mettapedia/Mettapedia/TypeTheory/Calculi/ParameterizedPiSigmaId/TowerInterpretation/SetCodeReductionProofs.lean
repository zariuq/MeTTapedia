import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeAbstractionProofs

/-!
# Retained typed source beta equality

Operator expansion, guarded trace beta and source instantiation compose to
the exact source computation equation. The judgment retains result typing.
Its argument receipt is attached once by a retained cut.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.ReductionProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetMembershipProofs
open AbstractionProofs (code opened)
open AnnotatedCodedReading (readAt)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

def betaAt {n : Nat} (domain : CTm Head n) (body : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code argument bound) (code domain bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (.eq (code (.app (.lam domain body) argument) bound)
      (code (CTm.inst0 argument body) bound)) := by
  let a := code domain bound
  let f := Term.lam (opened body bound)
  let x := code argument bound
  have abstractionEquation := SetCodeOperators.binaryBeta (Δ := Δ) core epsilon .abstraction a f
  have first : ProofSyntax (PrimitiveSymbol Head) Δ (.eq (code (.app (.lam domain body) argument) bound)
      (.app (.app (weakenCtx Γ (SetCode.body .application)) (SetTraceProofs.abstraction core epsilon a f)) x)) :=
    .eqApp x (.eqAppArg (weakenCtx Γ (SetCode.body .application)) abstractionEquation)
  have second := SetCodeOperators.binaryBeta (Δ := Δ) core epsilon .application
    (SetTraceProofs.abstraction core epsilon a f) x
  have third := SetTraceProofs.beta core epsilon a f x sets admitted
  have fourth : ProofSyntax (PrimitiveSymbol Head) Δ (.eq (.app f x) (code (CTm.inst0 argument body) bound)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta x (opened body bound))
    dsimp only [code,opened]
    rw [AnnotatedCodedReading.readAt_inst0]
  exact .eqTrans first (.eqTrans second (.eqTrans third fourth))

theorem expanded_equality {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    expand (judgmentAt (.equality context left right type) bound) =
      .imp (expand (contextAt context bound))
        (.and (.eq (code left bound) (code right bound)) (member core (code left bound) (code type bound))) := by
  dsimp only [judgmentAt,statementContext,statementAt,memberAt,expand,HOL.substConst]
  dsimp only [images]
  rw [HOL.weakenCtx_const]
  change Term.imp (expand (contextAt context bound))
      (.and (.eq (expand (readAt CodedHOL.operations bound left)) (expand (readAt CodedHOL.operations bound right)))
        (member core (expand (readAt CodedHOL.operations bound left)) (expand (readAt CodedHOL.operations bound type)))) = _
  simp only [expand_readAt]
  rfl

def betaJudgmentWithPremises {n : Nat} (context : CCtx Head n) (domain : CTm Head n)
    (body codomain : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (bodyProof : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (AnnotatedCodedReading.lift bound))))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context argument domain) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt
      (.equality context (.app (.lam domain body) argument) (CTm.inst0 argument body) (CTm.inst0 argument codomain)) bound)) := by
  let guard := expand (contextAt context bound)
  have functionProof := AbstractionProofs.abstractionJudgment context domain body codomain bound sets bodyProof
  have typed := TypingProofs.applicationJudgment context (.lam domain body) argument domain codomain bound sets functionProof argumentProof
  have argumentAt := ProofSyntax.impE
    (ProofSyntax.castIndices rfl (TypingProofs.expanded_typing context argument domain bound) (argumentProof.prepend guard)) (.hyp 0)
  have computation := betaAt domain body argument bound (sets.prepend guard) argumentAt
  have resultType := ProofSyntax.impE (ProofSyntax.castIndices rfl
    (TypingProofs.expanded_typing context (.app (.lam domain body) argument) (CTm.inst0 argument codomain) bound)
      (typed.prepend guard)) (.hyp 0)
  exact .castIndices rfl (expanded_equality context (.app (.lam domain body) argument)
    (CTm.inst0 argument body) (CTm.inst0 argument codomain) bound).symm (.impI (.andI computation resultType))

def betaJudgment {n : Nat} (context : CCtx Head n) (domain : CTm Head n)
    (body codomain : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (bodyProof : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (AnnotatedCodedReading.lift bound))))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context argument domain) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt
      (.equality context (.app (.lam domain body) argument) (CTm.inst0 argument body) (CTm.inst0 argument codomain)) bound)) :=
  ProofSyntax.cut argumentProof (betaJudgmentWithPremises context domain body codomain argument bound (sets.prepend _)
    (bodyProof.prepend (HOL.weaken (expand (judgmentAt (.typing context argument domain) bound)))) (.hyp 0))

theorem betaAt_free {n : Nat} (domain : CTm Head n) (body : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (admitted : ProofSyntax (PrimitiveSymbol Head) Δ (member core (code argument bound) (code domain bound)))
    (setsFree : sets.Free) (admittedFree : admitted.FunctionExtensionalityFree) :
    (betaAt domain body argument bound sets admitted).FunctionExtensionalityFree := by
  simp only [betaAt,ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices]
  exact ⟨SetCodeOperators.binaryBeta_free core epsilon .abstraction _ _,
    SetCodeOperators.binaryBeta_free core epsilon .application _ _,
    SetTraceProofs.beta_free core epsilon _ _ _ sets admitted setsFree admittedFree,trivial⟩

theorem betaJudgmentWithPremises_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n)
    (body codomain : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (bodyProof : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (AnnotatedCodedReading.lift bound))))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context argument domain) bound)))
    (setsFree : sets.Free) (bodyFree : bodyProof.FunctionExtensionalityFree) (argumentFree : argumentProof.FunctionExtensionalityFree) :
    (betaJudgmentWithPremises context domain body codomain argument bound sets bodyProof argumentProof).FunctionExtensionalityFree := by
  have functionFree := AbstractionProofs.abstractionJudgment_free context domain body codomain bound sets bodyProof setsFree bodyFree
  have typedFree := TypingProofs.applicationJudgment_free context (.lam domain body) argument domain codomain bound sets _ _
    setsFree functionFree argumentFree
  unfold betaJudgmentWithPremises
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  constructor
  · apply betaAt_free
    · exact sets.prepend_free _ setsFree
    · constructor
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact (ProofSyntax.functionExtensionalityFree_mono _ argumentProof).mpr argumentFree
      · trivial
  · constructor
    · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr typedFree
    · trivial

theorem betaJudgment_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n)
    (body codomain : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (bodyProof : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (AnnotatedCodedReading.lift bound))))
    (argumentProof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context argument domain) bound)))
    (setsFree : sets.Free) (bodyFree : bodyProof.FunctionExtensionalityFree) (argumentFree : argumentProof.FunctionExtensionalityFree) :
    (betaJudgment context domain body codomain argument bound sets bodyProof argumentProof).FunctionExtensionalityFree :=
  ProofSyntax.cut_free argumentProof _ argumentFree
    (betaJudgmentWithPremises_free context domain body codomain argument bound _ _ _
      (sets.prepend_free _ setsFree) ((ProofSyntax.functionExtensionalityFree_mono _ bodyProof).mpr bodyFree) trivial)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.ReductionProofs
