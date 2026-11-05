import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeReductionProofs

/-!
# Opening and closing retained guarded source judgments

The original source context is the antecedent of each judgment. Opening a
receipt adds that antecedent as a local hypothesis; closing discharges it.
Typed equality retains both its equation and the left term's membership.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.JudgmentProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs
open AbstractionProofs (code opened)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

def familyBeta {n : Nat} (family : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    ProofSyntax (PrimitiveSymbol Head) Δ (.eq (.app (.lam (opened family bound)) (code argument bound))
      (code (CTm.inst0 argument family) bound)) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta (code argument bound) (opened family bound))
  dsimp only [code,opened]
  rw [AnnotatedCodedReading.readAt_inst0]

theorem familyBeta_free {n : Nat} (family : CTm Head (n+1)) (argument : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object) :
    (familyBeta (Δ := Δ) family argument bound).FunctionExtensionalityFree := by
  unfold familyBeta
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr trivial

def openTyping {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value type) bound))) :
    ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (member core (code value bound) (code type bound)) :=
  .impE (.castIndices rfl (TypingProofs.expanded_typing context value type bound) (proof.prepend _)) (.hyp 0)

def closeTyping {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (member core (code value bound) (code type bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value type) bound)) :=
  .castIndices rfl (TypingProofs.expanded_typing context value type bound).symm (.impI proof)

def openEquality {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right type) bound))) :
    ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (.and (.eq (code left bound) (code right bound)) (member core (code left bound) (code type bound))) :=
  .impE (.castIndices rfl (ReductionProofs.expanded_equality context left right type bound) (proof.prepend _)) (.hyp 0)

def closeEquality {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (equal : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (.eq (code left bound) (code right bound)))
    (typed : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (member core (code left bound) (code type bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right type) bound)) :=
  .castIndices rfl (ReductionProofs.expanded_equality context left right type bound).symm (.impI (.andI equal typed))

theorem openTyping_free {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value type) bound)))
    (free : proof.FunctionExtensionalityFree) : (openTyping context value type bound proof).FunctionExtensionalityFree := by
  unfold openTyping
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ((ProofSyntax.functionExtensionalityFree_mono _ proof).mpr free),trivial⟩

theorem closeTyping_free {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (member core (code value bound) (code type bound)))
    (free : proof.FunctionExtensionalityFree) : (closeTyping context value type bound proof).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

theorem openEquality_free {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (proof : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right type) bound)))
    (free : proof.FunctionExtensionalityFree) : (openEquality context left right type bound proof).FunctionExtensionalityFree := by
  unfold openEquality
  exact ⟨(ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ((ProofSyntax.functionExtensionalityFree_mono _ proof).mpr free),trivial⟩

theorem closeEquality_free {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (equal : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (.eq (code left bound) (code right bound)))
    (typed : ProofSyntax (PrimitiveSymbol Head) (expand (contextAt context bound) :: Δ)
      (member core (code left bound) (code type bound)))
    (equalFree : equal.FunctionExtensionalityFree) (typedFree : typed.FunctionExtensionalityFree) :
    (closeEquality context left right type bound equal typed).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr ⟨equalFree,typedFree⟩

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.JudgmentProofs
