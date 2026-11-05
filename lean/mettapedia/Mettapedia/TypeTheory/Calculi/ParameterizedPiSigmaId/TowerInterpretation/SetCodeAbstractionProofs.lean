import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeContextProofs
import Mettapedia.Logic.HOL.ProofSyntaxFreshBeta

/-!
# Retained source abstraction with a shared body receipt

The body judgment is opened under the actual context and argument guards.
Its pointwise result is supplied once to a schema that types the constructed
trace. Implication introduction and elimination perform that retained cut.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.AbstractionProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetMembershipProofs
open AnnotatedCodedReading (readAt lift)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

abbrev code {n : Nat} (source : CTm Head n) (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :=
  readAt operations (fun index => expand (bound index)) source

abbrev opened {n : Nat} (source : CTm Head (n+1)) (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :=
  readAt operations (lift (fun index => expand (bound index))) source

private theorem mappedLift {n : Nat} (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    (fun index => expand (lift bound index)) = lift (fun index => expand (bound index)) :=
  AnnotatedCodedReading.substConst_lift images bound

private def newestBeta {n : Nat} (source : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    {assumptions : List (Formula (PrimitiveSymbol Head) (object :: Γ))} :
    ProofSyntax (PrimitiveSymbol Head) assumptions (.eq
      (.app (HOL.weaken (.lam (opened source bound))) (.var .vz)) (opened source bound)) :=
  ProofSyntax.betaAtFresh (opened source bound)

private theorem newestBeta_free {n : Nat} (source : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    {assumptions : List (Formula (PrimitiveSymbol Head) (object :: Γ))} :
    (newestBeta (assumptions := assumptions) source bound).FunctionExtensionalityFree :=
  ProofSyntax.betaAtFresh_free (opened source bound)

def openBody {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)))) :
    ProofSyntax (PrimitiveSymbol Head)
      (member core (.var .vz) (HOL.weaken (code domain bound)) ::
        weakenHyps (σ := object) (expand (contextAt context bound) :: Δ))
      (member core (opened body bound) (opened codomain bound)) := by
  let guard := expand (contextAt context bound)
  let domainGuard := member core (.var .vz) (HOL.weaken (code domain bound))
  have statement : expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)) =
      Term.imp (.and (HOL.weaken guard) domainGuard) (member core (opened body bound) (opened codomain bound)) := by
    rw [TypingProofs.expanded_typing,ContextProofs.expanded_context_lift,mappedLift]
  have localReceived := (received.prepend (HOL.weaken guard)).prepend domainGuard
  exact .impE (.castIndices rfl statement localReceived) (.andI (.hyp 1) (.hyp 0))

def pointwise {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)))) :
    ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (SetTraceProductProofs.pointwise core (code domain bound) (.lam (opened codomain bound)) (.lam (opened body bound))) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  exact transportBound core _ (.eqSymm (newestBeta codomain bound))
    (transportValue core _ (.eqSymm (newestBeta body bound)) (openBody context domain body codomain bound received))

@[irreducible] def schema {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ) :
    ProofSyntax (PrimitiveSymbol Head)
      (SetTraceProductProofs.pointwise core (code domain bound) (.lam (opened codomain bound)) (.lam (opened body bound)) ::
        expand (contextAt context bound) :: Δ)
      (member core (SetTraceProofs.abstraction core epsilon (code domain bound) (.lam (opened body bound)))
        (SetTraceProductProofs.product core epsilon (code domain bound) (.lam (opened codomain bound)))) :=
  SetTraceProductProofs.abstractionTyped core epsilon (code domain bound) (.lam (opened codomain bound)) (.lam (opened body bound))
    ((sets.prepend _).prepend _) (.hyp 0)

@[irreducible] def abstractionJudgment {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context (.lam domain body) (.pi domain codomain)) bound)) := by
  let guard := expand (contextAt context bound)
  let a := code domain bound
  let b := Term.lam (opened codomain bound)
  let f := Term.lam (opened body bound)
  have typed := ProofSyntax.cut (pointwise context domain body codomain bound received)
    (schema context domain body codomain bound sets)
  have abstractionEquation : ProofSyntax (PrimitiveSymbol Head) (guard :: Δ)
      (.eq (code (.lam domain body) bound) (SetTraceProofs.abstraction core epsilon a f)) :=
    SetCodeOperators.binaryBeta core epsilon .abstraction a f
  have productEquation : ProofSyntax (PrimitiveSymbol Head) (guard :: Δ)
      (.eq (code (.pi domain codomain) bound) (SetTraceProductProofs.product core epsilon a b)) :=
    SetCodeOperators.binaryBeta core epsilon .product a b
  exact .castIndices rfl (TypingProofs.expanded_typing context (.lam domain body) (.pi domain codomain) bound).symm
    (.impI (transportBound core _ (.eqSymm productEquation)
      (transportValue core _ (.eqSymm abstractionEquation) typed)))

theorem openBody_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound))))
    (free : received.FunctionExtensionalityFree) : (openBody context domain body codomain bound received).FunctionExtensionalityFree := by
  unfold openBody
  constructor
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_mono _ received).mpr free
  · exact ⟨trivial,trivial⟩

theorem pointwise_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound))))
    (free : received.FunctionExtensionalityFree) : (pointwise context domain body codomain bound received).FunctionExtensionalityFree := by
  unfold pointwise
  apply transportBound_free
  · exact newestBeta_free codomain bound
  · apply transportValue_free
    · exact newestBeta_free body bound
    · exact openBody_free context domain body codomain bound received free

theorem schema_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ) (free : sets.Free) :
    (schema context domain body codomain bound sets).FunctionExtensionalityFree := by
  unfold schema
  apply SetTraceProductProofs.abstractionTyped_free
  · exact (sets.prepend _).prepend_free _ (sets.prepend_free _ free)
  · trivial

theorem abstractionJudgment_free {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound))))
    (setsFree : sets.Free) (bodyFree : received.FunctionExtensionalityFree) :
    (abstractionJudgment context domain body codomain bound sets received).FunctionExtensionalityFree := by
  unfold abstractionJudgment
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply transportBound_free
  · exact SetCodeOperators.binaryBeta_free core epsilon .product _ _
  · apply transportValue_free
    · exact SetCodeOperators.binaryBeta_free core epsilon .abstraction _ _
    · exact ProofSyntax.cut_free _ _ (pointwise_free context domain body codomain bound received bodyFree)
        (schema_free context domain body codomain bound sets setsFree)

private theorem newestBeta_nodeCount {n : Nat} (source : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    {assumptions : List (Formula (PrimitiveSymbol Head) (object :: Γ))} :
    Derivation.nodeCount (newestBeta (assumptions := assumptions) source bound).observe = 1 :=
  ProofSyntax.betaAtFresh_nodeCount (opened source bound)

private theorem binaryBeta_nodeCount {left right : Ty Unit} (operator : SetCodeOperators.Operator (left ⇒ right ⇒ object))
    (first : Term (PrimitiveSymbol Head) Γ left) (second : Term (PrimitiveSymbol Head) Γ right) :
    Derivation.nodeCount (SetCodeOperators.binaryBeta (Δ := Δ) core epsilon operator first second).observe = 4 := by
  simp [SetCodeOperators.binaryBeta,BinaryOperation.beta,ProofSyntax.observe_nodeCount_castIndices,ProofSyntax.observe]

theorem openBody_nodeCount {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)))) :
    Derivation.nodeCount (openBody context domain body codomain bound received).observe = received.nodeCount + 4 := by
  simp [openBody,ProofSyntax.prepend,ProofSyntax.observe_nodeCount_castIndices,ProofSyntax.observe_mono_nodeCount,
    ProofSyntax.nodeCount,ProofSyntax.observe]
  omega

theorem pointwise_nodeCount {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)))) :
    Derivation.nodeCount (pointwise context domain body codomain bound received).observe = received.nodeCount + 17 := by
  simp [pointwise,transportBound,transportValue,boundCongr,valueCongr,newestBeta_nodeCount,openBody_nodeCount,
    ProofSyntax.nodeCount,ProofSyntax.observe]
  omega

theorem abstractionJudgment_nodeCount {n : Nat} (context : CCtx Head n) (domain : CTm Head n) (body codomain : CTm Head (n+1))
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) (sets : SetTraceProofs.Laws core epsilon Δ)
    (received : ProofSyntax (PrimitiveSymbol Head) (weakenHyps (σ := object) Δ)
      (expand (judgmentAt (.typing (.snoc context domain) body codomain) (lift bound)))) :
    Derivation.nodeCount (abstractionJudgment context domain body codomain bound sets received).observe =
      received.nodeCount + (schema context domain body codomain bound sets).nodeCount + 37 := by
  simp [abstractionJudgment,transportBound,transportValue,boundCongr,valueCongr,
    ProofSyntax.observe_nodeCount_castIndices,ProofSyntax.cut_nodeCount,pointwise_nodeCount,binaryBeta_nodeCount,
    ProofSyntax.nodeCount,ProofSyntax.observe]
  omega

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.AbstractionProofs
