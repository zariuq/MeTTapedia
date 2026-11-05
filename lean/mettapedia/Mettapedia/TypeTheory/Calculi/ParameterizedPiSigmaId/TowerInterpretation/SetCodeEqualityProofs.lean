import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeJudgmentProofs

/-!
# Retained source typed equality and conversion

Equivalence rules preserve the membership part of typed equality. Conversion
uses the supplied equality of type codes. Retained cuts attach each supplied
source-judgment receipt once, while local hypotheses may be cited repeatedly.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.EqualityProofs
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open SetComprehensionProofs SetMembershipProofs
open AbstractionProofs (code)
variable {Head : Type} {Γ : Ctx Unit} {Δ : List (Formula (PrimitiveSymbol Head) Γ)}

def reflexiveJudgment {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value type) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context value value type) bound)) :=
  JudgmentProofs.closeEquality context value value type bound (.eqRefl _)
    (JudgmentProofs.openTyping context value type bound received)

def symmetryJudgment {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right type) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context right left type) bound)) := by
  let premise := expand (judgmentAt (.equality context left right type) bound)
  have premiseProof : ProofSyntax (PrimitiveSymbol Head) (premise :: Δ) premise := .hyp 0
  have parts := JudgmentProofs.openEquality context left right type bound premiseProof
  exact ProofSyntax.cut received (JudgmentProofs.closeEquality context right left type bound
    (.eqSymm (.andEL parts)) (transportValue core _ (.andEL parts) (.andER parts)))

def transitivityJudgment {n : Nat} (context : CCtx Head n) (left middle right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (first : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left middle type) bound)))
    (second : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context middle right type) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right type) bound)) := by
  let firstStatement := expand (judgmentAt (.equality context left middle type) bound)
  let secondStatement := expand (judgmentAt (.equality context middle right type) bound)
  let assumptions := secondStatement :: firstStatement :: Δ
  have firstLocal : ProofSyntax (PrimitiveSymbol Head) assumptions firstStatement := .hyp 1
  have secondLocal : ProofSyntax (PrimitiveSymbol Head) assumptions secondStatement := .hyp 0
  have firstParts := JudgmentProofs.openEquality context left middle type bound firstLocal
  have secondParts := JudgmentProofs.openEquality context middle right type bound secondLocal
  exact ProofSyntax.cut first (ProofSyntax.cut (second.prepend firstStatement)
    (JudgmentProofs.closeEquality context left right type bound
      (.eqTrans (.andEL firstParts) (.andEL secondParts)) (.andER firstParts)))

def conversionJudgment {n : Nat} (context : CCtx Head n) (value before after levelCode : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value before) bound)))
    (equal : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context before after levelCode) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value after) bound)) := by
  let typedStatement := expand (judgmentAt (.typing context value before) bound)
  let equalStatement := expand (judgmentAt (.equality context before after levelCode) bound)
  let assumptions := equalStatement :: typedStatement :: Δ
  have typedLocal : ProofSyntax (PrimitiveSymbol Head) assumptions typedStatement := .hyp 1
  have equalLocal : ProofSyntax (PrimitiveSymbol Head) assumptions equalStatement := .hyp 0
  have typed := JudgmentProofs.openTyping context value before bound typedLocal
  have equality := JudgmentProofs.openEquality context before after levelCode bound equalLocal
  exact ProofSyntax.cut received (ProofSyntax.cut (equal.prepend typedStatement)
    (JudgmentProofs.closeTyping context value after bound (transportBound core _ (.andEL equality) typed)))

def equalityConversionJudgment {n : Nat} (context : CCtx Head n) (left right before after levelCode : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right before) bound)))
    (equal : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context before after levelCode) bound))) :
    ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right after) bound)) := by
  let typedStatement := expand (judgmentAt (.equality context left right before) bound)
  let equalStatement := expand (judgmentAt (.equality context before after levelCode) bound)
  let assumptions := equalStatement :: typedStatement :: Δ
  have typedLocal : ProofSyntax (PrimitiveSymbol Head) assumptions typedStatement := .hyp 1
  have equalLocal : ProofSyntax (PrimitiveSymbol Head) assumptions equalStatement := .hyp 0
  have typed := JudgmentProofs.openEquality context left right before bound typedLocal
  have equality := JudgmentProofs.openEquality context before after levelCode bound equalLocal
  exact ProofSyntax.cut received (ProofSyntax.cut (equal.prepend typedStatement)
    (JudgmentProofs.closeEquality context left right after bound (.andEL typed)
      (transportBound core _ (.andEL equality) (.andER typed))))

theorem reflexiveJudgment_free {n : Nat} (context : CCtx Head n) (value type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value type) bound)))
    (free : received.FunctionExtensionalityFree) : (reflexiveJudgment context value type bound received).FunctionExtensionalityFree :=
  JudgmentProofs.closeEquality_free context _ _ _ bound _ _ trivial
    (JudgmentProofs.openTyping_free context value type bound received free)

theorem symmetryJudgment_free {n : Nat} (context : CCtx Head n) (left right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right type) bound)))
    (free : received.FunctionExtensionalityFree) : (symmetryJudgment context left right type bound received).FunctionExtensionalityFree := by
  unfold symmetryJudgment
  let assumptions := expand (judgmentAt (.equality context left right type) bound) :: Δ
  have partsFree := JudgmentProofs.openEquality_free (Δ := assumptions) context left right type bound (.hyp 0) trivial
  apply ProofSyntax.cut_free _ _ free
  apply JudgmentProofs.closeEquality_free
  · exact partsFree
  · apply transportValue_free
    · exact partsFree
    · exact partsFree

theorem transitivityJudgment_free {n : Nat} (context : CCtx Head n) (left middle right type : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (first : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left middle type) bound)))
    (second : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context middle right type) bound)))
    (firstFree : first.FunctionExtensionalityFree) (secondFree : second.FunctionExtensionalityFree) :
    (transitivityJudgment context left middle right type bound first second).FunctionExtensionalityFree := by
  unfold transitivityJudgment
  let assumptions := expand (judgmentAt (.equality context middle right type) bound) ::
    expand (judgmentAt (.equality context left middle type) bound) :: Δ
  have firstPartsFree := JudgmentProofs.openEquality_free (Δ := assumptions) context left middle type bound (.hyp 1) trivial
  have secondPartsFree := JudgmentProofs.openEquality_free (Δ := assumptions) context middle right type bound (.hyp 0) trivial
  apply ProofSyntax.cut_free _ _ firstFree
  apply ProofSyntax.cut_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ second).mpr secondFree
  · apply JudgmentProofs.closeEquality_free
    · exact ⟨firstPartsFree,secondPartsFree⟩
    · exact firstPartsFree

theorem conversionJudgment_free {n : Nat} (context : CCtx Head n) (value before after levelCode : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.typing context value before) bound)))
    (equal : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context before after levelCode) bound)))
    (receivedFree : received.FunctionExtensionalityFree) (equalFree : equal.FunctionExtensionalityFree) :
    (conversionJudgment context value before after levelCode bound received equal).FunctionExtensionalityFree := by
  unfold conversionJudgment
  let assumptions := expand (judgmentAt (.equality context before after levelCode) bound) ::
    expand (judgmentAt (.typing context value before) bound) :: Δ
  have typedFree := JudgmentProofs.openTyping_free (Δ := assumptions) context value before bound (.hyp 1) trivial
  have typeFree := JudgmentProofs.openEquality_free (Δ := assumptions) context before after levelCode bound (.hyp 0) trivial
  apply ProofSyntax.cut_free _ _ receivedFree
  apply ProofSyntax.cut_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ equal).mpr equalFree
  · apply JudgmentProofs.closeTyping_free
    apply transportBound_free
    · exact typeFree
    · exact typedFree

theorem equalityConversionJudgment_free {n : Nat} (context : CCtx Head n) (left right before after levelCode : CTm Head n)
    (bound : Fin n → Term (CodedHOL.Symbol Head) Γ object)
    (received : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context left right before) bound)))
    (equal : ProofSyntax (PrimitiveSymbol Head) Δ (expand (judgmentAt (.equality context before after levelCode) bound)))
    (receivedFree : received.FunctionExtensionalityFree) (equalFree : equal.FunctionExtensionalityFree) :
    (equalityConversionJudgment context left right before after levelCode bound received equal).FunctionExtensionalityFree := by
  unfold equalityConversionJudgment
  let assumptions := expand (judgmentAt (.equality context before after levelCode) bound) ::
    expand (judgmentAt (.equality context left right before) bound) :: Δ
  have typedFree := JudgmentProofs.openEquality_free (Δ := assumptions) context left right before bound (.hyp 1) trivial
  have typeFree := JudgmentProofs.openEquality_free (Δ := assumptions) context before after levelCode bound (.hyp 0) trivial
  apply ProofSyntax.cut_free _ _ receivedFree
  apply ProofSyntax.cut_free
  · exact (ProofSyntax.functionExtensionalityFree_mono _ equal).mpr equalFree
  · apply JudgmentProofs.closeEquality_free
    · exact typedFree
    · apply transportBound_free
      · exact typeFree
      · exact typedFree

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.CodedHOL.SetCode.EqualityProofs
