import Mettapedia.GSLT.Parsing.PlainBnfScalarOrderSource

/-! Exact canonical admission of the two authored reference-collection sources.
Checked chunks bound kernel reduction without omitting source fields or rows.
This admits source data; it does not establish the behavior of a compiler or runtime. -/

namespace Mettapedia.GSLT.Parsing.PlainBnfReferenceSourceAdmission

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def graphSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/plain_bnf_graph_analysis_v1.metta"
def admissionSyntax : SExpr := PlainBnfScalarOrderSource.sourceSyntax

private def operatorRows : SExpr → List SExpr
  | .list [.atom "gslt-presentation-v1", _, .list (.atom "signature" :: rows), _, _] => rows
  | _ => []
private def rewriteRows : SExpr → List SExpr
  | .list [.atom "gslt-presentation-v1", _, _, _, .list (.atom "rewrites" :: rows)] => rows
  | _ => []

private theorem decodeList_append (f : SExpr → Option α) (left right : List SExpr) :
    decodeList f (left ++ right) = (do
      let first ← decodeList f left
      let second ← decodeList f right
      pure (first ++ second)) := by
  induction left with
  | nil => simp [decodeList]
  | cons head tail ih =>
      simp only [List.cons_append, decodeList, ih]
      cases f head <;> simp
      cases decodeList f tail <;> simp
      cases decodeList f right <;> simp

@[local simp] private theorem natToken0 : "0".toNat? = some 0 := Nat.toNat?_repr 0
@[local simp] private theorem natToken1 : "1".toNat? = some 1 := Nat.toNat?_repr 1
@[local simp] private theorem natToken2 : "2".toNat? = some 2 := Nat.toNat?_repr 2
@[local simp] private theorem natToken3 : "3".toNat? = some 3 := Nat.toNat?_repr 3
@[local simp] private theorem natToken4 : "4".toNat? = some 4 := Nat.toNat?_repr 4
@[local simp] private theorem natToken5 : "5".toNat? = some 5 := Nat.toNat?_repr 5
@[local simp] private theorem natToken6 : "6".toNat? = some 6 := Nat.toNat?_repr 6
@[local simp] private theorem natToken7 : "7".toNat? = some 7 := Nat.toNat?_repr 7
@[local simp] private theorem natToken8 : "8".toNat? = some 8 := Nat.toNat?_repr 8

private def graphOperators0 : List Operator :=
  (((operatorRows graphSyntax).drop 0).take 10).filterMap decodeOperator
private theorem graphOperators0_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 0).take 10) = some graphOperators0 := by
  dsimp only [graphOperators0, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators0_encoded :
    graphOperators0.map encodeOperator = ((operatorRows graphSyntax).drop 0).take 10 := by
  dsimp only [graphOperators0, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators1 : List Operator :=
  (((operatorRows graphSyntax).drop 10).take 10).filterMap decodeOperator
private theorem graphOperators1_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 10).take 10) = some graphOperators1 := by
  dsimp only [graphOperators1, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators1_encoded :
    graphOperators1.map encodeOperator = ((operatorRows graphSyntax).drop 10).take 10 := by
  dsimp only [graphOperators1, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators2 : List Operator :=
  (((operatorRows graphSyntax).drop 20).take 10).filterMap decodeOperator
private theorem graphOperators2_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 20).take 10) = some graphOperators2 := by
  dsimp only [graphOperators2, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators2_encoded :
    graphOperators2.map encodeOperator = ((operatorRows graphSyntax).drop 20).take 10 := by
  dsimp only [graphOperators2, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators3 : List Operator :=
  (((operatorRows graphSyntax).drop 30).take 10).filterMap decodeOperator
private theorem graphOperators3_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 30).take 10) = some graphOperators3 := by
  dsimp only [graphOperators3, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators3_encoded :
    graphOperators3.map encodeOperator = ((operatorRows graphSyntax).drop 30).take 10 := by
  dsimp only [graphOperators3, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators4 : List Operator :=
  (((operatorRows graphSyntax).drop 40).take 10).filterMap decodeOperator
private theorem graphOperators4_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 40).take 10) = some graphOperators4 := by
  dsimp only [graphOperators4, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators4_encoded :
    graphOperators4.map encodeOperator = ((operatorRows graphSyntax).drop 40).take 10 := by
  dsimp only [graphOperators4, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators5 : List Operator :=
  (((operatorRows graphSyntax).drop 50).take 10).filterMap decodeOperator
private theorem graphOperators5_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 50).take 10) = some graphOperators5 := by
  dsimp only [graphOperators5, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators5_encoded :
    graphOperators5.map encodeOperator = ((operatorRows graphSyntax).drop 50).take 10 := by
  dsimp only [graphOperators5, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators6 : List Operator :=
  (((operatorRows graphSyntax).drop 60).take 10).filterMap decodeOperator
private theorem graphOperators6_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 60).take 10) = some graphOperators6 := by
  dsimp only [graphOperators6, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators6_encoded :
    graphOperators6.map encodeOperator = ((operatorRows graphSyntax).drop 60).take 10 := by
  dsimp only [graphOperators6, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def graphOperators7 : List Operator :=
  (((operatorRows graphSyntax).drop 70).take 10).filterMap decodeOperator
private theorem graphOperators7_decoded :
    decodeList decodeOperator (((operatorRows graphSyntax).drop 70).take 10) = some graphOperators7 := by
  dsimp only [graphOperators7, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem graphOperators7_encoded :
    graphOperators7.map encodeOperator = ((operatorRows graphSyntax).drop 70).take 10 := by
  dsimp only [graphOperators7, operatorRows, graphSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

def graphOperators : List Operator :=
  graphOperators0 ++ graphOperators1 ++ graphOperators2 ++ graphOperators3 ++ graphOperators4 ++ graphOperators5 ++ graphOperators6 ++ graphOperators7
private theorem graphOperators_partition : operatorRows graphSyntax =
    ((operatorRows graphSyntax).drop 0).take 10 ++ ((operatorRows graphSyntax).drop 10).take 10 ++ ((operatorRows graphSyntax).drop 20).take 10 ++ ((operatorRows graphSyntax).drop 30).take 10 ++ ((operatorRows graphSyntax).drop 40).take 10 ++ ((operatorRows graphSyntax).drop 50).take 10 ++ ((operatorRows graphSyntax).drop 60).take 10 ++ ((operatorRows graphSyntax).drop 70).take 10 := rfl
theorem graphOperators_decoded : decodeList decodeOperator (operatorRows graphSyntax) =
    some graphOperators := by
  conv_lhs => rw [graphOperators_partition]
  simp only [decodeList_append, graphOperators0_decoded, graphOperators1_decoded, graphOperators2_decoded, graphOperators3_decoded, graphOperators4_decoded, graphOperators5_decoded, graphOperators6_decoded, graphOperators7_decoded]
  rfl
theorem graphOperators_encoded : graphOperators.map encodeOperator = operatorRows graphSyntax := by
  rw [graphOperators_partition]
  simp only [graphOperators, List.map_append, graphOperators0_encoded, graphOperators1_encoded, graphOperators2_encoded, graphOperators3_encoded, graphOperators4_encoded, graphOperators5_encoded, graphOperators6_encoded, graphOperators7_encoded]

private def graphRewrites0 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 0).take 10).filterMap decodeRewrite
private theorem graphRewrites0_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 0).take 10) = some graphRewrites0 := by
  rfl
private theorem graphRewrites0_encoded :
    graphRewrites0.map encodeRewrite = ((rewriteRows graphSyntax).drop 0).take 10 := by
  rfl

private def graphRewrites1 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 10).take 10).filterMap decodeRewrite
private theorem graphRewrites1_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 10).take 10) = some graphRewrites1 := by
  rfl
private theorem graphRewrites1_encoded :
    graphRewrites1.map encodeRewrite = ((rewriteRows graphSyntax).drop 10).take 10 := by
  rfl

private def graphRewrites2 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 20).take 10).filterMap decodeRewrite
private theorem graphRewrites2_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 20).take 10) = some graphRewrites2 := by
  rfl
private theorem graphRewrites2_encoded :
    graphRewrites2.map encodeRewrite = ((rewriteRows graphSyntax).drop 20).take 10 := by
  rfl

private def graphRewrites3 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 30).take 10).filterMap decodeRewrite
private theorem graphRewrites3_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 30).take 10) = some graphRewrites3 := by
  rfl
private theorem graphRewrites3_encoded :
    graphRewrites3.map encodeRewrite = ((rewriteRows graphSyntax).drop 30).take 10 := by
  rfl

private def graphRewrites4 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 40).take 10).filterMap decodeRewrite
private theorem graphRewrites4_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 40).take 10) = some graphRewrites4 := by
  rfl
private theorem graphRewrites4_encoded :
    graphRewrites4.map encodeRewrite = ((rewriteRows graphSyntax).drop 40).take 10 := by
  rfl

private def graphRewrites5 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 50).take 10).filterMap decodeRewrite
private theorem graphRewrites5_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 50).take 10) = some graphRewrites5 := by
  rfl
private theorem graphRewrites5_encoded :
    graphRewrites5.map encodeRewrite = ((rewriteRows graphSyntax).drop 50).take 10 := by
  rfl

private def graphRewrites6 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 60).take 10).filterMap decodeRewrite
private theorem graphRewrites6_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 60).take 10) = some graphRewrites6 := by
  rfl
private theorem graphRewrites6_encoded :
    graphRewrites6.map encodeRewrite = ((rewriteRows graphSyntax).drop 60).take 10 := by
  rfl

private def graphRewrites7 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 70).take 10).filterMap decodeRewrite
private theorem graphRewrites7_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 70).take 10) = some graphRewrites7 := by
  rfl
private theorem graphRewrites7_encoded :
    graphRewrites7.map encodeRewrite = ((rewriteRows graphSyntax).drop 70).take 10 := by
  rfl

private def graphRewrites8 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 80).take 10).filterMap decodeRewrite
private theorem graphRewrites8_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 80).take 10) = some graphRewrites8 := by
  rfl
private theorem graphRewrites8_encoded :
    graphRewrites8.map encodeRewrite = ((rewriteRows graphSyntax).drop 80).take 10 := by
  rfl

private def graphRewrites9 : List Rewrite :=
  (((rewriteRows graphSyntax).drop 90).take 10).filterMap decodeRewrite
private theorem graphRewrites9_decoded :
    decodeList decodeRewrite (((rewriteRows graphSyntax).drop 90).take 10) = some graphRewrites9 := by
  rfl
private theorem graphRewrites9_encoded :
    graphRewrites9.map encodeRewrite = ((rewriteRows graphSyntax).drop 90).take 10 := by
  rfl

def graphRewrites : List Rewrite :=
  graphRewrites0 ++ graphRewrites1 ++ graphRewrites2 ++ graphRewrites3 ++ graphRewrites4 ++ graphRewrites5 ++ graphRewrites6 ++ graphRewrites7 ++ graphRewrites8 ++ graphRewrites9
private theorem graphRewrites_partition : rewriteRows graphSyntax =
    ((rewriteRows graphSyntax).drop 0).take 10 ++ ((rewriteRows graphSyntax).drop 10).take 10 ++ ((rewriteRows graphSyntax).drop 20).take 10 ++ ((rewriteRows graphSyntax).drop 30).take 10 ++ ((rewriteRows graphSyntax).drop 40).take 10 ++ ((rewriteRows graphSyntax).drop 50).take 10 ++ ((rewriteRows graphSyntax).drop 60).take 10 ++ ((rewriteRows graphSyntax).drop 70).take 10 ++ ((rewriteRows graphSyntax).drop 80).take 10 ++ ((rewriteRows graphSyntax).drop 90).take 10 := rfl
theorem graphRewrites_decoded : decodeList decodeRewrite (rewriteRows graphSyntax) =
    some graphRewrites := by
  conv_lhs => rw [graphRewrites_partition]
  simp only [decodeList_append, graphRewrites0_decoded, graphRewrites1_decoded, graphRewrites2_decoded, graphRewrites3_decoded, graphRewrites4_decoded, graphRewrites5_decoded, graphRewrites6_decoded, graphRewrites7_decoded, graphRewrites8_decoded, graphRewrites9_decoded]
  rfl
theorem graphRewrites_encoded : graphRewrites.map encodeRewrite = rewriteRows graphSyntax := by
  rw [graphRewrites_partition]
  simp only [graphRewrites, List.map_append, graphRewrites0_encoded, graphRewrites1_encoded, graphRewrites2_encoded, graphRewrites3_encoded, graphRewrites4_encoded, graphRewrites5_encoded, graphRewrites6_encoded, graphRewrites7_encoded, graphRewrites8_encoded, graphRewrites9_encoded]

def graphSource : Source := ⟨"PlainBnfGraphAnalysisV1", graphOperators, [], graphRewrites⟩

/-- Includes the FIFO entry, rotation and reverse accumulator; no appended
source row is omitted by the chunked decoder. -/
theorem graph_source_size :
    graphSource.operators.length = 80 ∧ graphSource.rewrites.length = 97 := by
  constructor
  · have lengths := congrArg List.length graphOperators_encoded
    have raw : (operatorRows graphSyntax).length = 80 := rfl
    simpa only [List.length_map, raw, graphSource] using lengths
  · rfl
private theorem graph_envelope : graphSyntax =
    .list [.atom "gslt-presentation-v1", .atom "PlainBnfGraphAnalysisV1",
      .list (.atom "signature" :: operatorRows graphSyntax), .list [.atom "equations"],
      .list (.atom "rewrites" :: rewriteRows graphSyntax)] := rfl
theorem graph_decoded : decode graphSyntax = some graphSource := by
  conv_lhs => rw [graph_envelope]
  simp only [decode, atomToken?, graphOperators_decoded, graphRewrites_decoded, graphSource]
  rfl
theorem graph_encoded : encode graphSource = graphSyntax := by
  simp only [encode, graphSource, graphOperators_encoded, graphRewrites_encoded, encodeAtomToken]
  exact graph_envelope.symm
theorem graph_canonical : Canonical graphSyntax := ⟨graphSource, graph_encoded.symm⟩

private def admissionOperators0 : List Operator :=
  (((operatorRows admissionSyntax).drop 0).take 10).filterMap decodeOperator
private theorem admissionOperators0_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 0).take 10) = some admissionOperators0 := by
  dsimp only [admissionOperators0, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators0_encoded :
    admissionOperators0.map encodeOperator = ((operatorRows admissionSyntax).drop 0).take 10 := by
  dsimp only [admissionOperators0, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators1 : List Operator :=
  (((operatorRows admissionSyntax).drop 10).take 10).filterMap decodeOperator
private theorem admissionOperators1_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 10).take 10) = some admissionOperators1 := by
  dsimp only [admissionOperators1, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators1_encoded :
    admissionOperators1.map encodeOperator = ((operatorRows admissionSyntax).drop 10).take 10 := by
  dsimp only [admissionOperators1, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators2 : List Operator :=
  (((operatorRows admissionSyntax).drop 20).take 10).filterMap decodeOperator
private theorem admissionOperators2_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 20).take 10) = some admissionOperators2 := by
  dsimp only [admissionOperators2, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators2_encoded :
    admissionOperators2.map encodeOperator = ((operatorRows admissionSyntax).drop 20).take 10 := by
  dsimp only [admissionOperators2, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators3 : List Operator :=
  (((operatorRows admissionSyntax).drop 30).take 10).filterMap decodeOperator
private theorem admissionOperators3_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 30).take 10) = some admissionOperators3 := by
  dsimp only [admissionOperators3, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators3_encoded :
    admissionOperators3.map encodeOperator = ((operatorRows admissionSyntax).drop 30).take 10 := by
  dsimp only [admissionOperators3, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators4 : List Operator :=
  (((operatorRows admissionSyntax).drop 40).take 10).filterMap decodeOperator
private theorem admissionOperators4_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 40).take 10) = some admissionOperators4 := by
  dsimp only [admissionOperators4, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators4_encoded :
    admissionOperators4.map encodeOperator = ((operatorRows admissionSyntax).drop 40).take 10 := by
  dsimp only [admissionOperators4, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators5 : List Operator :=
  (((operatorRows admissionSyntax).drop 50).take 10).filterMap decodeOperator
private theorem admissionOperators5_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 50).take 10) = some admissionOperators5 := by
  dsimp only [admissionOperators5, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators5_encoded :
    admissionOperators5.map encodeOperator = ((operatorRows admissionSyntax).drop 50).take 10 := by
  dsimp only [admissionOperators5, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators6 : List Operator :=
  (((operatorRows admissionSyntax).drop 60).take 10).filterMap decodeOperator
private theorem admissionOperators6_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 60).take 10) = some admissionOperators6 := by
  dsimp only [admissionOperators6, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators6_encoded :
    admissionOperators6.map encodeOperator = ((operatorRows admissionSyntax).drop 60).take 10 := by
  dsimp only [admissionOperators6, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def admissionOperators7 : List Operator :=
  (((operatorRows admissionSyntax).drop 70).take 10).filterMap decodeOperator
private theorem admissionOperators7_decoded :
    decodeList decodeOperator (((operatorRows admissionSyntax).drop 70).take 10) = some admissionOperators7 := by
  dsimp only [admissionOperators7, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]
private theorem admissionOperators7_encoded :
    admissionOperators7.map encodeOperator = ((operatorRows admissionSyntax).drop 70).take 10 := by
  dsimp only [admissionOperators7, operatorRows, admissionSyntax, PlainBnfScalarOrderSource.sourceSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

def admissionOperators : List Operator :=
  admissionOperators0 ++ admissionOperators1 ++ admissionOperators2 ++ admissionOperators3 ++ admissionOperators4 ++ admissionOperators5 ++ admissionOperators6 ++ admissionOperators7
private theorem admissionOperators_partition : operatorRows admissionSyntax =
    ((operatorRows admissionSyntax).drop 0).take 10 ++ ((operatorRows admissionSyntax).drop 10).take 10 ++ ((operatorRows admissionSyntax).drop 20).take 10 ++ ((operatorRows admissionSyntax).drop 30).take 10 ++ ((operatorRows admissionSyntax).drop 40).take 10 ++ ((operatorRows admissionSyntax).drop 50).take 10 ++ ((operatorRows admissionSyntax).drop 60).take 10 ++ ((operatorRows admissionSyntax).drop 70).take 10 := rfl
theorem admissionOperators_decoded : decodeList decodeOperator (operatorRows admissionSyntax) =
    some admissionOperators := by
  conv_lhs => rw [admissionOperators_partition]
  simp only [decodeList_append, admissionOperators0_decoded, admissionOperators1_decoded, admissionOperators2_decoded, admissionOperators3_decoded, admissionOperators4_decoded, admissionOperators5_decoded, admissionOperators6_decoded, admissionOperators7_decoded]
  rfl
theorem admissionOperators_encoded : admissionOperators.map encodeOperator = operatorRows admissionSyntax := by
  rw [admissionOperators_partition]
  simp only [admissionOperators, List.map_append, admissionOperators0_encoded, admissionOperators1_encoded, admissionOperators2_encoded, admissionOperators3_encoded, admissionOperators4_encoded, admissionOperators5_encoded, admissionOperators6_encoded, admissionOperators7_encoded]

private def admissionRewrites0 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 0).take 10).filterMap decodeRewrite
private theorem admissionRewrites0_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 0).take 10) = some admissionRewrites0 := by
  rfl
private theorem admissionRewrites0_encoded :
    admissionRewrites0.map encodeRewrite = ((rewriteRows admissionSyntax).drop 0).take 10 := by
  rfl

private def admissionRewrites1 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 10).take 10).filterMap decodeRewrite
private theorem admissionRewrites1_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 10).take 10) = some admissionRewrites1 := by
  rfl
private theorem admissionRewrites1_encoded :
    admissionRewrites1.map encodeRewrite = ((rewriteRows admissionSyntax).drop 10).take 10 := by
  rfl

private def admissionRewrites2 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 20).take 10).filterMap decodeRewrite
private theorem admissionRewrites2_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 20).take 10) = some admissionRewrites2 := by
  rfl
private theorem admissionRewrites2_encoded :
    admissionRewrites2.map encodeRewrite = ((rewriteRows admissionSyntax).drop 20).take 10 := by
  rfl

private def admissionRewrites3 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 30).take 10).filterMap decodeRewrite
private theorem admissionRewrites3_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 30).take 10) = some admissionRewrites3 := by
  rfl
private theorem admissionRewrites3_encoded :
    admissionRewrites3.map encodeRewrite = ((rewriteRows admissionSyntax).drop 30).take 10 := by
  rfl

private def admissionRewrites4 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 40).take 10).filterMap decodeRewrite
private theorem admissionRewrites4_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 40).take 10) = some admissionRewrites4 := by
  rfl
private theorem admissionRewrites4_encoded :
    admissionRewrites4.map encodeRewrite = ((rewriteRows admissionSyntax).drop 40).take 10 := by
  rfl

private def admissionRewrites5 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 50).take 10).filterMap decodeRewrite
private theorem admissionRewrites5_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 50).take 10) = some admissionRewrites5 := by
  rfl
private theorem admissionRewrites5_encoded :
    admissionRewrites5.map encodeRewrite = ((rewriteRows admissionSyntax).drop 50).take 10 := by
  rfl

private def admissionRewrites6 : List Rewrite :=
  (((rewriteRows admissionSyntax).drop 60).take 10).filterMap decodeRewrite
private theorem admissionRewrites6_decoded :
    decodeList decodeRewrite (((rewriteRows admissionSyntax).drop 60).take 10) = some admissionRewrites6 := by
  rfl
private theorem admissionRewrites6_encoded :
    admissionRewrites6.map encodeRewrite = ((rewriteRows admissionSyntax).drop 60).take 10 := by
  rfl

def admissionRewrites : List Rewrite :=
  admissionRewrites0 ++ admissionRewrites1 ++ admissionRewrites2 ++ admissionRewrites3 ++ admissionRewrites4 ++ admissionRewrites5 ++ admissionRewrites6
private theorem admissionRewrites_partition : rewriteRows admissionSyntax =
    ((rewriteRows admissionSyntax).drop 0).take 10 ++ ((rewriteRows admissionSyntax).drop 10).take 10 ++ ((rewriteRows admissionSyntax).drop 20).take 10 ++ ((rewriteRows admissionSyntax).drop 30).take 10 ++ ((rewriteRows admissionSyntax).drop 40).take 10 ++ ((rewriteRows admissionSyntax).drop 50).take 10 ++ ((rewriteRows admissionSyntax).drop 60).take 10 := rfl
theorem admissionRewrites_decoded : decodeList decodeRewrite (rewriteRows admissionSyntax) =
    some admissionRewrites := by
  conv_lhs => rw [admissionRewrites_partition]
  simp only [decodeList_append, admissionRewrites0_decoded, admissionRewrites1_decoded, admissionRewrites2_decoded, admissionRewrites3_decoded, admissionRewrites4_decoded, admissionRewrites5_decoded, admissionRewrites6_decoded]
  rfl
theorem admissionRewrites_encoded : admissionRewrites.map encodeRewrite = rewriteRows admissionSyntax := by
  rw [admissionRewrites_partition]
  simp only [admissionRewrites, List.map_append, admissionRewrites0_encoded, admissionRewrites1_encoded, admissionRewrites2_encoded, admissionRewrites3_encoded, admissionRewrites4_encoded, admissionRewrites5_encoded, admissionRewrites6_encoded]

def admissionSource : Source := ⟨"PlainBnfSemanticAdmissionV1", admissionOperators, [], admissionRewrites⟩
private theorem admission_envelope : admissionSyntax =
    .list [.atom "gslt-presentation-v1", .atom "PlainBnfSemanticAdmissionV1",
      .list (.atom "signature" :: operatorRows admissionSyntax), .list [.atom "equations"],
      .list (.atom "rewrites" :: rewriteRows admissionSyntax)] := rfl
theorem admission_decoded : decode admissionSyntax = some admissionSource := by
  conv_lhs => rw [admission_envelope]
  simp only [decode, atomToken?, admissionOperators_decoded, admissionRewrites_decoded, admissionSource]
  rfl
theorem admission_encoded : encode admissionSource = admissionSyntax := by
  simp only [encode, admissionSource, admissionOperators_encoded, admissionRewrites_encoded, encodeAtomToken]
  exact admission_envelope.symm
theorem admission_canonical : Canonical admissionSyntax := ⟨admissionSource, admission_encoded.symm⟩

#print axioms graph_decoded
#print axioms admission_decoded
#print axioms graph_encoded
#print axioms admission_encoded

end Mettapedia.GSLT.Parsing.PlainBnfReferenceSourceAdmission
