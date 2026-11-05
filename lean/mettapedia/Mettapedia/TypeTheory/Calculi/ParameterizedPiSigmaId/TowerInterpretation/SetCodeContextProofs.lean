import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeTypingProofs

/-!
# Source contexts and retained variable receipts

The encoded context commutes with target substitution. Extending the source
context exposes its earlier guard and the newest variable's membership.
Variable lookup follows the original context recursively and retains the
corresponding membership receipt.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.ContextProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs
open AnnotatedCodedReading (readAt lift)
variable {Head : Type} {Γ Ξ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

theorem contextAt_targetSubst {n : Nat} (theta : Subst (CodedHOL.Symbol Head) Γ Ξ)
    (context : CCtx Head n) (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    HOL.subst theta (contextAt context bound) = contextAt context (fun index => HOL.subst theta (bound index)) := by
  induction context with
  | nil => rfl
  | snoc earlier type previous =>
    simp only [contextAt,memberAt,HOL.subst,previous,AnnotatedCodedReading.readAt_targetSubst]

theorem expanded_context_weaken {n : Nat} (context : CCtx Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    expand (contextAt context (fun index => HOL.weaken (σ := object) (bound index))) =
      HOL.weaken (σ := object) (expand (contextAt context bound)) := by
  have weakened : HOL.weaken (σ := object) (contextAt context bound) =
      contextAt context (fun index => HOL.weaken (σ := object) (bound index)) := by
    simpa only [HOL.subst_ofRename,HOL.weaken] using
      contextAt_targetSubst (Subst.ofRename (Rename.weaken (σ := object))) context bound
  rw [← weakened]
  exact HOL.substConst_weaken images _

theorem expanded_context_snoc {n : Nat} (context : CCtx Head n) (type : CTm Head n)
    (bound : Fin (n+1) → Term (CodedHOL.Symbol Head) Γ object) :
    expand (contextAt (.snoc context type) bound) =
      .and (expand (contextAt context (fun index => bound index.succ)))
        (member core (expand (bound 0)) (readAt operations (fun index => expand (bound index.succ)) type)) := by
  dsimp only [contextAt,memberAt,expand,HOL.substConst]
  dsimp only [images]
  rw [HOL.weakenCtx_const]
  change Term.and (expand (contextAt context (fun index => bound index.succ)))
      (member core (expand (bound 0)) (expand (readAt CodedHOL.operations (fun index => bound index.succ) type))) = _
  rw [expand_readAt]
  rfl

theorem expanded_context_lift {n : Nat} (context : CCtx Head n) (type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    expand (contextAt (.snoc context type) (lift bound)) =
      .and (HOL.weaken (expand (contextAt context bound)))
        (member core (.var .vz) (HOL.weaken (readAt operations (fun index => expand (bound index)) type))) := by
  rw [expanded_context_snoc]
  change Term.and (expand (contextAt context (fun index => HOL.weaken (bound index))))
      (member core (.var .vz) (readAt operations (fun index => expand (HOL.weaken (bound index))) type)) = _
  rw [expanded_context_weaken]
  have mapped : (fun index => expand (HOL.weaken (σ := object) (bound index))) =
      (fun index => HOL.weaken (σ := object) (expand (bound index))) := by
    funext index
    exact HOL.substConst_weaken images _
  rw [mapped,← AnnotatedCodedReading.readAt_weaken]

def variableAt : {n : Nat} → (context : CCtx Head n) → (index : Fin n) →
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) →
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (contextAt context bound)) →
    ProofSyntax (PrimitiveSymbol Head) Δ (member core (expand (bound index))
      (readAt operations (fun position => expand (bound position)) (context.lookup index)))
  | _, .nil, index, _, _ => Fin.elim0 index
  | _, .snoc earlier type, index, bound, received => by
    have parts := ProofSyntax.castIndices rfl (expanded_context_snoc earlier type bound) received
    refine Fin.cases ?_ (fun next => ?_) index
    · apply ProofSyntax.castIndices rfl ?_ (.andER parts)
      simp only [CCtx.lookup_snoc_zero,AnnotatedCodedReading.readAt_rename]
      rfl
    · have earlierReceipt := variableAt earlier next (fun position => bound position.succ) (.andEL parts)
      apply ProofSyntax.castIndices rfl ?_ earlierReceipt
      simp only [CCtx.lookup_snoc_succ,AnnotatedCodedReading.readAt_rename]
      rfl

def variableJudgment {n : Nat} (context : CCtx Head n) (index : Fin n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context (.var index) (context.lookup index)) bound)) :=
  ProofSyntax.castIndices rfl (TypingProofs.expanded_typing context (.var index) (context.lookup index) bound).symm
    (.impI (variableAt context index bound (.hyp 0)))

theorem variableAt_free {n : Nat} (context : CCtx Head n) (index : Fin n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (contextAt context bound)))
    (free : received.FunctionExtensionalityFree) :
    (variableAt context index bound received).FunctionExtensionalityFree := by
  induction context with
  | nil => exact Fin.elim0 index
  | snoc earlier type previous =>
    refine Fin.cases ?_ (fun next => ?_) index
    · simpa only [variableAt,Fin.cases_zero,ProofSyntax.functionExtensionalityFree_castIndices,
        ProofSyntax.FunctionExtensionalityFree] using free
    · simp only [variableAt,Fin.cases_succ,ProofSyntax.functionExtensionalityFree_castIndices]
      apply previous
      simpa only [ProofSyntax.FunctionExtensionalityFree,ProofSyntax.functionExtensionalityFree_castIndices] using free

theorem variableJudgment_free {n : Nat} (context : CCtx Head n) (index : Fin n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    (variableJudgment (Δ := Δ) context index bound).FunctionExtensionalityFree := by
  simp only [variableJudgment,ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.FunctionExtensionalityFree]
  exact variableAt_free (Δ := expand (contextAt context bound) :: Δ) context index bound (.hyp 0) trivial

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.ContextProofs
