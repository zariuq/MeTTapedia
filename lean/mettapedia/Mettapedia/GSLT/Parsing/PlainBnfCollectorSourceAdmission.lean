import Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceExecution

/-!
# Complete canonical admission of the authored collector and trie sources

The existing source decoder is evaluated in bounded structural pieces, then
reassembled by its list-composition law. Full source rows, including ordered
bodies and occurrence positions, remain the returned values. Source quotation
is still an executable byte-reader boundary, not proved byte parsing.

Admission here means canonical decoding and the existing open-component
schema. It does not assert closed-composition reference validity, complete
collector execution, or native compiler adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceAdmission

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def discoverySyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/plain_bnf_graph_discovery_v1.metta"

def indexSyntax : SExpr :=
  metta_sexpr_file% petta "../../../../../../hyperon/cetta-prime-nik-20260811/langdef/bnf/plain_bnf_graph_index_v1.metta"

private def operatorRows : SExpr → List SExpr
  | .list [.atom "gslt-presentation-v1", _, .list (.atom "signature" :: rows), _, _] => rows
  | _ => []

private def rewriteRows : SExpr → List SExpr
  | .list [.atom "gslt-presentation-v1", _, _, _, .list (.atom "rewrites" :: rows)] => rows
  | _ => []

private theorem decodeList_append {α : Type} (decoder : SExpr → Option α)
    (left right : List SExpr) :
    decodeList decoder (left ++ right) =
      (do let first ← decodeList decoder left
          let rest ← decodeList decoder right
          some (first ++ rest)) := by
  induction left with
  | nil => simp [decodeList]
  | cons head tail ih =>
      cases first : decoder head <;> simp [decodeList, first, ih]
      cases rest : decodeList decoder tail <;>
        cases last : decodeList decoder right <;> simp

@[local simp] private theorem natToken0 : "0".toNat? = some 0 :=
  Nat.toNat?_repr 0

@[local simp] private theorem natToken1 : "1".toNat? = some 1 :=
  Nat.toNat?_repr 1

@[local simp] private theorem natToken2 : "2".toNat? = some 2 :=
  Nat.toNat?_repr 2

@[local simp] private theorem natToken3 : "3".toNat? = some 3 :=
  Nat.toNat?_repr 3

@[local simp] private theorem natToken4 : "4".toNat? = some 4 :=
  Nat.toNat?_repr 4

@[local simp] private theorem natToken5 : "5".toNat? = some 5 :=
  Nat.toNat?_repr 5

@[local simp] private theorem natToken6 : "6".toNat? = some 6 :=
  Nat.toNat?_repr 6

@[local simp] private theorem natToken7 : "7".toNat? = some 7 :=
  Nat.toNat?_repr 7

@[local simp] private theorem natToken8 : "8".toNat? = some 8 :=
  Nat.toNat?_repr 8

@[local simp] private theorem natToken9 : "9".toNat? = some 9 :=
  Nat.toNat?_repr 9

private def discoveryOperators0 : List Operator :=
  (((operatorRows discoverySyntax).drop 0).take 10).filterMap decodeOperator

private theorem discoveryOperators0_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 0).take 10) = some discoveryOperators0 := by
  dsimp only [discoveryOperators0, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators0_encoded :
    discoveryOperators0.map encodeOperator = ((operatorRows discoverySyntax).drop 0).take 10 := by
  dsimp only [discoveryOperators0, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators1 : List Operator :=
  (((operatorRows discoverySyntax).drop 10).take 10).filterMap decodeOperator

private theorem discoveryOperators1_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 10).take 10) = some discoveryOperators1 := by
  dsimp only [discoveryOperators1, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators1_encoded :
    discoveryOperators1.map encodeOperator = ((operatorRows discoverySyntax).drop 10).take 10 := by
  dsimp only [discoveryOperators1, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators2 : List Operator :=
  (((operatorRows discoverySyntax).drop 20).take 10).filterMap decodeOperator

private theorem discoveryOperators2_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 20).take 10) = some discoveryOperators2 := by
  dsimp only [discoveryOperators2, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators2_encoded :
    discoveryOperators2.map encodeOperator = ((operatorRows discoverySyntax).drop 20).take 10 := by
  dsimp only [discoveryOperators2, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators3 : List Operator :=
  (((operatorRows discoverySyntax).drop 30).take 10).filterMap decodeOperator

private theorem discoveryOperators3_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 30).take 10) = some discoveryOperators3 := by
  dsimp only [discoveryOperators3, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators3_encoded :
    discoveryOperators3.map encodeOperator = ((operatorRows discoverySyntax).drop 30).take 10 := by
  dsimp only [discoveryOperators3, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators4 : List Operator :=
  (((operatorRows discoverySyntax).drop 40).take 10).filterMap decodeOperator

private theorem discoveryOperators4_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 40).take 10) = some discoveryOperators4 := by
  dsimp only [discoveryOperators4, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators4_encoded :
    discoveryOperators4.map encodeOperator = ((operatorRows discoverySyntax).drop 40).take 10 := by
  dsimp only [discoveryOperators4, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators5 : List Operator :=
  (((operatorRows discoverySyntax).drop 50).take 10).filterMap decodeOperator

private theorem discoveryOperators5_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 50).take 10) = some discoveryOperators5 := by
  dsimp only [discoveryOperators5, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators5_encoded :
    discoveryOperators5.map encodeOperator = ((operatorRows discoverySyntax).drop 50).take 10 := by
  dsimp only [discoveryOperators5, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators6 : List Operator :=
  (((operatorRows discoverySyntax).drop 60).take 10).filterMap decodeOperator

private theorem discoveryOperators6_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 60).take 10) = some discoveryOperators6 := by
  dsimp only [discoveryOperators6, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators6_encoded :
    discoveryOperators6.map encodeOperator = ((operatorRows discoverySyntax).drop 60).take 10 := by
  dsimp only [discoveryOperators6, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def discoveryOperators7 : List Operator :=
  (((operatorRows discoverySyntax).drop 70).take 10).filterMap decodeOperator

private theorem discoveryOperators7_decoded :
    decodeList decodeOperator (((operatorRows discoverySyntax).drop 70).take 10) = some discoveryOperators7 := by
  dsimp only [discoveryOperators7, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem discoveryOperators7_encoded :
    discoveryOperators7.map encodeOperator = ((operatorRows discoverySyntax).drop 70).take 10 := by
  dsimp only [discoveryOperators7, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

def discoveryOperators : List Operator :=
  discoveryOperators0 ++ discoveryOperators1 ++ discoveryOperators2 ++ discoveryOperators3 ++ discoveryOperators4 ++ discoveryOperators5 ++ discoveryOperators6 ++ discoveryOperators7

private theorem discoveryOperators_partition :
    operatorRows discoverySyntax = ((operatorRows discoverySyntax).drop 0).take 10 ++ ((operatorRows discoverySyntax).drop 10).take 10 ++ ((operatorRows discoverySyntax).drop 20).take 10 ++ ((operatorRows discoverySyntax).drop 30).take 10 ++ ((operatorRows discoverySyntax).drop 40).take 10 ++ ((operatorRows discoverySyntax).drop 50).take 10 ++ ((operatorRows discoverySyntax).drop 60).take 10 ++ ((operatorRows discoverySyntax).drop 70).take 10 := by rfl

theorem discoveryOperators_decoded :
    decodeList decodeOperator (operatorRows discoverySyntax) = some discoveryOperators := by
  conv_lhs => rw [discoveryOperators_partition]
  simp only [decodeList_append, discoveryOperators0_decoded, discoveryOperators1_decoded, discoveryOperators2_decoded, discoveryOperators3_decoded, discoveryOperators4_decoded, discoveryOperators5_decoded, discoveryOperators6_decoded, discoveryOperators7_decoded,
    ]
  rfl

theorem discoveryOperators_encoded :
    discoveryOperators.map encodeOperator = operatorRows discoverySyntax := by
  rw [discoveryOperators_partition]
  simp only [discoveryOperators, List.map_append,
    discoveryOperators0_encoded, discoveryOperators1_encoded, discoveryOperators2_encoded, discoveryOperators3_encoded, discoveryOperators4_encoded, discoveryOperators5_encoded, discoveryOperators6_encoded, discoveryOperators7_encoded]

private def discoveryRewrites0 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 0).take 10).filterMap decodeRewrite

private theorem discoveryRewrites0_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 0).take 10) = some discoveryRewrites0 := by rfl

private theorem discoveryRewrites0_encoded :
    discoveryRewrites0.map encodeRewrite = ((rewriteRows discoverySyntax).drop 0).take 10 := by rfl

private def discoveryRewrites1 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 10).take 10).filterMap decodeRewrite

private theorem discoveryRewrites1_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 10).take 10) = some discoveryRewrites1 := by rfl

private theorem discoveryRewrites1_encoded :
    discoveryRewrites1.map encodeRewrite = ((rewriteRows discoverySyntax).drop 10).take 10 := by rfl

private def discoveryRewrites2 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 20).take 10).filterMap decodeRewrite

private theorem discoveryRewrites2_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 20).take 10) = some discoveryRewrites2 := by rfl

private theorem discoveryRewrites2_encoded :
    discoveryRewrites2.map encodeRewrite = ((rewriteRows discoverySyntax).drop 20).take 10 := by rfl

private def discoveryRewrites3 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 30).take 10).filterMap decodeRewrite

private theorem discoveryRewrites3_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 30).take 10) = some discoveryRewrites3 := by rfl

private theorem discoveryRewrites3_encoded :
    discoveryRewrites3.map encodeRewrite = ((rewriteRows discoverySyntax).drop 30).take 10 := by rfl

private def discoveryRewrites4 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 40).take 10).filterMap decodeRewrite

private theorem discoveryRewrites4_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 40).take 10) = some discoveryRewrites4 := by rfl

private theorem discoveryRewrites4_encoded :
    discoveryRewrites4.map encodeRewrite = ((rewriteRows discoverySyntax).drop 40).take 10 := by rfl

private def discoveryRewrites5 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 50).take 10).filterMap decodeRewrite

private theorem discoveryRewrites5_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 50).take 10) = some discoveryRewrites5 := by rfl

private theorem discoveryRewrites5_encoded :
    discoveryRewrites5.map encodeRewrite = ((rewriteRows discoverySyntax).drop 50).take 10 := by rfl

private def discoveryRewrites6 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 60).take 10).filterMap decodeRewrite

private theorem discoveryRewrites6_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 60).take 10) = some discoveryRewrites6 := by rfl

private theorem discoveryRewrites6_encoded :
    discoveryRewrites6.map encodeRewrite = ((rewriteRows discoverySyntax).drop 60).take 10 := by rfl

private def discoveryRewrites7 : List Rewrite :=
  (((rewriteRows discoverySyntax).drop 70).take 10).filterMap decodeRewrite

private theorem discoveryRewrites7_decoded :
    decodeList decodeRewrite (((rewriteRows discoverySyntax).drop 70).take 10) = some discoveryRewrites7 := by rfl

private theorem discoveryRewrites7_encoded :
    discoveryRewrites7.map encodeRewrite = ((rewriteRows discoverySyntax).drop 70).take 10 := by rfl

def discoveryRewrites : List Rewrite :=
  discoveryRewrites0 ++ discoveryRewrites1 ++ discoveryRewrites2 ++ discoveryRewrites3 ++ discoveryRewrites4 ++ discoveryRewrites5 ++ discoveryRewrites6 ++ discoveryRewrites7

private theorem discoveryRewrites_partition :
    rewriteRows discoverySyntax = ((rewriteRows discoverySyntax).drop 0).take 10 ++ ((rewriteRows discoverySyntax).drop 10).take 10 ++ ((rewriteRows discoverySyntax).drop 20).take 10 ++ ((rewriteRows discoverySyntax).drop 30).take 10 ++ ((rewriteRows discoverySyntax).drop 40).take 10 ++ ((rewriteRows discoverySyntax).drop 50).take 10 ++ ((rewriteRows discoverySyntax).drop 60).take 10 ++ ((rewriteRows discoverySyntax).drop 70).take 10 := by rfl

theorem discoveryRewrites_decoded :
    decodeList decodeRewrite (rewriteRows discoverySyntax) = some discoveryRewrites := by
  conv_lhs => rw [discoveryRewrites_partition]
  simp only [decodeList_append, discoveryRewrites0_decoded, discoveryRewrites1_decoded, discoveryRewrites2_decoded, discoveryRewrites3_decoded, discoveryRewrites4_decoded, discoveryRewrites5_decoded, discoveryRewrites6_decoded, discoveryRewrites7_decoded,
    ]
  rfl

theorem discoveryRewrites_encoded :
    discoveryRewrites.map encodeRewrite = rewriteRows discoverySyntax := by
  rw [discoveryRewrites_partition]
  simp only [discoveryRewrites, List.map_append,
    discoveryRewrites0_encoded, discoveryRewrites1_encoded, discoveryRewrites2_encoded, discoveryRewrites3_encoded, discoveryRewrites4_encoded, discoveryRewrites5_encoded, discoveryRewrites6_encoded, discoveryRewrites7_encoded]

private def indexOperators0 : List Operator :=
  (((operatorRows indexSyntax).drop 0).take 10).filterMap decodeOperator

private theorem indexOperators0_decoded :
    decodeList decodeOperator (((operatorRows indexSyntax).drop 0).take 10) = some indexOperators0 := by
  dsimp only [indexOperators0, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem indexOperators0_encoded :
    indexOperators0.map encodeOperator = ((operatorRows indexSyntax).drop 0).take 10 := by
  dsimp only [indexOperators0, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def indexOperators1 : List Operator :=
  (((operatorRows indexSyntax).drop 10).take 10).filterMap decodeOperator

private theorem indexOperators1_decoded :
    decodeList decodeOperator (((operatorRows indexSyntax).drop 10).take 10) = some indexOperators1 := by
  dsimp only [indexOperators1, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem indexOperators1_encoded :
    indexOperators1.map encodeOperator = ((operatorRows indexSyntax).drop 10).take 10 := by
  dsimp only [indexOperators1, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

private def indexOperators2 : List Operator :=
  (((operatorRows indexSyntax).drop 20).take 10).filterMap decodeOperator

private theorem indexOperators2_decoded :
    decodeList decodeOperator (((operatorRows indexSyntax).drop 20).take 10) = some indexOperators2 := by
  dsimp only [indexOperators2, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeList, decodeOperator, atomToken?]

private theorem indexOperators2_encoded :
    indexOperators2.map encodeOperator = ((operatorRows indexSyntax).drop 20).take 10 := by
  dsimp only [indexOperators2, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?, encodeOperator, encodeAtomToken]
  decide

def indexOperators : List Operator :=
  indexOperators0 ++ indexOperators1 ++ indexOperators2

private theorem indexOperators_partition :
    operatorRows indexSyntax = ((operatorRows indexSyntax).drop 0).take 10 ++ ((operatorRows indexSyntax).drop 10).take 10 ++ ((operatorRows indexSyntax).drop 20).take 10 := by rfl

theorem indexOperators_decoded :
    decodeList decodeOperator (operatorRows indexSyntax) = some indexOperators := by
  conv_lhs => rw [indexOperators_partition]
  simp only [decodeList_append, indexOperators0_decoded, indexOperators1_decoded, indexOperators2_decoded,
    ]
  rfl

theorem indexOperators_encoded :
    indexOperators.map encodeOperator = operatorRows indexSyntax := by
  rw [indexOperators_partition]
  simp only [indexOperators, List.map_append,
    indexOperators0_encoded, indexOperators1_encoded, indexOperators2_encoded]

private def indexRewrites0 : List Rewrite :=
  (((rewriteRows indexSyntax).drop 0).take 10).filterMap decodeRewrite

private theorem indexRewrites0_decoded :
    decodeList decodeRewrite (((rewriteRows indexSyntax).drop 0).take 10) = some indexRewrites0 := by rfl

private theorem indexRewrites0_encoded :
    indexRewrites0.map encodeRewrite = ((rewriteRows indexSyntax).drop 0).take 10 := by rfl

private def indexRewrites1 : List Rewrite :=
  (((rewriteRows indexSyntax).drop 10).take 10).filterMap decodeRewrite

private theorem indexRewrites1_decoded :
    decodeList decodeRewrite (((rewriteRows indexSyntax).drop 10).take 10) = some indexRewrites1 := by rfl

private theorem indexRewrites1_encoded :
    indexRewrites1.map encodeRewrite = ((rewriteRows indexSyntax).drop 10).take 10 := by rfl

def indexRewrites : List Rewrite :=
  indexRewrites0 ++ indexRewrites1

private theorem indexRewrites_partition :
    rewriteRows indexSyntax = ((rewriteRows indexSyntax).drop 0).take 10 ++ ((rewriteRows indexSyntax).drop 10).take 10 := by rfl

theorem indexRewrites_decoded :
    decodeList decodeRewrite (rewriteRows indexSyntax) = some indexRewrites := by
  conv_lhs => rw [indexRewrites_partition]
  simp only [decodeList_append, indexRewrites0_decoded, indexRewrites1_decoded,
    ]
  rfl

theorem indexRewrites_encoded :
    indexRewrites.map encodeRewrite = rewriteRows indexSyntax := by
  rw [indexRewrites_partition]
  simp only [indexRewrites, List.map_append,
    indexRewrites0_encoded, indexRewrites1_encoded]

def discoverySource : Source :=
  ⟨"PlainBnfGraphDiscoveryV1", discoveryOperators, [], discoveryRewrites⟩

def indexSource : Source :=
  ⟨"PlainBnfGraphIndexV1", indexOperators, [], indexRewrites⟩

private theorem discovery_envelope :
    discoverySyntax = .list [.atom "gslt-presentation-v1", .atom "PlainBnfGraphDiscoveryV1",
      .list (.atom "signature" :: operatorRows discoverySyntax), .list [.atom "equations"],
      .list (.atom "rewrites" :: rewriteRows discoverySyntax)] := by rfl

theorem discovery_decoded : decode discoverySyntax = some discoverySource := by
  conv_lhs => rw [discovery_envelope]
  simp only [decode, atomToken?, discoveryOperators_decoded,
    discoveryRewrites_decoded, discoverySource]
  rfl

theorem discovery_encoded : encode discoverySource = discoverySyntax := by
  unfold encode discoverySource
  rw [discoveryOperators_encoded, discoveryRewrites_encoded]
  exact discovery_envelope.symm

theorem discovery_canonical : Canonical discoverySyntax := ⟨discoverySource, discovery_encoded.symm⟩

private theorem index_envelope :
    indexSyntax = .list [.atom "gslt-presentation-v1", .atom "PlainBnfGraphIndexV1",
      .list (.atom "signature" :: operatorRows indexSyntax), .list [.atom "equations"],
      .list (.atom "rewrites" :: rewriteRows indexSyntax)] := by rfl

theorem index_decoded : decode indexSyntax = some indexSource := by
  conv_lhs => rw [index_envelope]
  simp only [decode, atomToken?, indexOperators_decoded,
    indexRewrites_decoded, indexSource]
  rfl

theorem index_encoded : encode indexSource = indexSyntax := by
  unfold encode indexSource
  rw [indexOperators_encoded, indexRewrites_encoded]
  exact index_envelope.symm

theorem index_canonical : Canonical indexSyntax := ⟨indexSource, index_encoded.symm⟩


/-- A source call belongs to this finite family only by its actual head symbol. -/
def inFamily (row : Rewrite) : Bool :=
  match row.head with
  | .list (.atom relation :: _) =>
      (PlainBnfCollectorSourceExecution.mode? relation).isSome
  | _ => false

/-- Keep the full source row and its original zero-based occurrence. -/
def family (source : Source) : List (Rewrite × Nat) :=
  source.rewrites.zipIdx.filter (fun indexed => inFamily indexed.1)

theorem mem_family_iff (source : Source) (row : Rewrite) (occurrence : Nat) :
    (row, occurrence) ∈ family source ↔
      source.rewrites[occurrence]? = some row ∧ inFamily row = true := by
  simp [family, List.mk_mem_zipIdx_iff_getElem?]

theorem discovery_occurrence (occurrence : Nat) :
    discoverySource.rewrites[occurrence]? = rawRewriteAt? discoverySyntax occurrence :=
  rawRewriteAt?_of_decode discovery_decoded occurrence

theorem index_occurrence (occurrence : Nat) :
    indexSource.rewrites[occurrence]? = rawRewriteAt? indexSyntax occurrence :=
  rawRewriteAt?_of_decode index_decoded occurrence

theorem discovery_rewrite_count : discoverySource.rewrites.length = 79 := by rfl

theorem index_rewrite_count : indexSource.rewrites.length = 20 := by rfl

theorem discovery_operator_count : discoverySource.operators.length = 80 := by
  have h := congrArg List.length discoveryOperators_encoded
  have count : (operatorRows discoverySyntax).length = 80 := by rfl
  simpa only [discoverySource, List.length_map, count] using h

theorem index_operator_count : indexSource.operators.length = 26 := by
  have h := congrArg List.length indexOperators_encoded
  have count : (operatorRows indexSyntax).length = 26 := by rfl
  simpa only [indexSource, List.length_map, count] using h

theorem discovery_family_occurrences :
    (family discoverySource).map Prod.snd = [40, 41, 42, 43, 44, 45, 46, 47, 48] := by rfl

theorem index_family_occurrences :
    (family indexSource).map Prod.snd = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := by rfl

private theorem discoveryOperators0_valid :
    discoveryOperators0.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators0, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators1_valid :
    discoveryOperators1.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators1, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators2_valid :
    discoveryOperators2.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators2, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators3_valid :
    discoveryOperators3.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators3, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators4_valid :
    discoveryOperators4.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators4, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators5_valid :
    discoveryOperators5.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators5, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators6_valid :
    discoveryOperators6.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators6, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryOperators7_valid :
    discoveryOperators7.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [discoveryOperators7, operatorRows, discoverySyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem discoveryRewrites0_valid :
    discoveryRewrites0.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites1_valid :
    discoveryRewrites1.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites2_valid :
    discoveryRewrites2.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites3_valid :
    discoveryRewrites3.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites4_valid :
    discoveryRewrites4.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites5_valid :
    discoveryRewrites5.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites6_valid :
    discoveryRewrites6.all Rewrite.hasValidShape = true := by rfl

private theorem discoveryRewrites7_valid :
    discoveryRewrites7.all Rewrite.hasValidShape = true := by rfl

private theorem indexOperators0_valid :
    indexOperators0.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [indexOperators0, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem indexOperators1_valid :
    indexOperators1.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [indexOperators1, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem indexOperators2_valid :
    indexOperators2.all (fun operator => !operator.name.isEmpty) = true := by
  dsimp only [indexOperators2, operatorRows, indexSyntax, List.drop, List.take]
  simp [decodeOperator, atomToken?]

private theorem indexRewrites0_valid :
    indexRewrites0.all Rewrite.hasValidShape = true := by rfl

private theorem indexRewrites1_valid :
    indexRewrites1.all Rewrite.hasValidShape = true := by rfl

theorem discovery_schema : discoverySource.hasValidSchema = true := by
  simp only [discoverySource, Source.hasValidSchema, discoveryOperators, discoveryRewrites,
    List.all_append, discoveryOperators0_valid, discoveryOperators1_valid, discoveryOperators2_valid, discoveryOperators3_valid, discoveryOperators4_valid, discoveryOperators5_valid, discoveryOperators6_valid, discoveryOperators7_valid, discoveryRewrites0_valid, discoveryRewrites1_valid, discoveryRewrites2_valid, discoveryRewrites3_valid, discoveryRewrites4_valid, discoveryRewrites5_valid, discoveryRewrites6_valid, discoveryRewrites7_valid]
  rfl

theorem index_schema : indexSource.hasValidSchema = true := by
  simp only [indexSource, Source.hasValidSchema, indexOperators, indexRewrites,
    List.all_append, indexOperators0_valid, indexOperators1_valid, indexOperators2_valid, indexRewrites0_valid, indexRewrites1_valid]
  rfl


/-- Full row values, not merely the projected occurrence numbers. -/
theorem discovery_family_exact :
    family discoverySource =
      ((discoverySource.rewrites.drop 40).take 9).zipIdx 40 := by rfl

theorem index_family_exact :
    family indexSource = (indexSource.rewrites.take 14).zipIdx := by rfl

private theorem family_mem_of_occurrence {source : Source} {row : Rewrite} {occurrence : Nat}
    (found : source.rewrites[occurrence]? = some row)
    (listed : occurrence ∈ (family source).map Prod.snd) :
    (row, occurrence) ∈ family source := by
  obtain ⟨⟨selected, index⟩, member, same⟩ := List.mem_map.mp listed
  change index = occurrence at same
  subst index
  have selectedAt := ((mem_family_iff source selected occurrence).mp member).1
  have rowsEqual : selected = row := Option.some.inj (selectedAt.symm.trans found)
  subst selected
  exact member

theorem discovery_family_iff (row : Rewrite) (occurrence : Nat) :
    (row, occurrence) ∈ family discoverySource ↔
      rawRewriteAt? discoverySyntax occurrence = some row ∧
        40 ≤ occurrence ∧ occurrence < 49 := by
  constructor
  · intro member
    have found := ((mem_family_iff discoverySource row occurrence).mp member).1
    have listed : occurrence ∈ (family discoverySource).map Prod.snd :=
      List.mem_map.mpr ⟨(row, occurrence), member, rfl⟩
    rw [discovery_family_occurrences] at listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    exact ⟨(discovery_occurrence occurrence).symm.trans found, by omega⟩
  · rintro ⟨found, lower, upper⟩
    apply family_mem_of_occurrence ((discovery_occurrence occurrence).trans found)
    rw [discovery_family_occurrences]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem index_family_iff (row : Rewrite) (occurrence : Nat) :
    (row, occurrence) ∈ family indexSource ↔
      rawRewriteAt? indexSyntax occurrence = some row ∧ occurrence < 14 := by
  constructor
  · intro member
    have found := ((mem_family_iff indexSource row occurrence).mp member).1
    have listed : occurrence ∈ (family indexSource).map Prod.snd :=
      List.mem_map.mpr ⟨(row, occurrence), member, rfl⟩
    rw [index_family_occurrences] at listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    exact ⟨(index_occurrence occurrence).symm.trans found, by omega⟩
  · rintro ⟨found, upper⟩
    apply family_mem_of_occurrence ((index_occurrence occurrence).trans found)
    rw [index_family_occurrences]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

/-- Existing operational reversal rules are exactly those obtained from the
now-admitted full source, not a second authored rule definition. -/
theorem reversalRules_from_admitted_source :
    PlainBnfCollectorSourceExecution.reversalRules? =
      (do
        let nilRule ← discoverySource.rewrites[47]? >>= PlainBnfCollectorSourceExecution.lowerRule?
        let consRule ← discoverySource.rewrites[48]? >>= PlainBnfCollectorSourceExecution.lowerRule?
        some [nilRule, consRule]) := by
  rw [discovery_occurrence, discovery_occurrence]
  rfl

/-- A second matching occurrence is retained even when its row is equal. -/
theorem appended_selected_occurrence (source : Source) (row : Rewrite)
    (selected : inFamily row = true) :
    family {source with rewrites := source.rewrites ++ [row]} =
      family source ++ [(row, source.rewrites.length)] := by
  simp [family, List.zipIdx_append, selected]

theorem unknown_head_excluded :
    inFamily {name := "outsider", head := .list [.atom "OutsideCollectorFamily"], body := []} =
      false := by rfl

theorem discovery_outsider_excluded (row : Rewrite) (occurrence : Nat)
    (outside : occurrence < 40 ∨ 49 ≤ occurrence) :
    (row, occurrence) ∉ family discoverySource := by
  rw [discovery_family_iff]
  omega

theorem index_outsider_excluded (row : Rewrite) (occurrence : Nat)
    (outside : 14 ≤ occurrence) :
    (row, occurrence) ∉ family indexSource := by
  rw [index_family_iff]
  omega

#print axioms discovery_decoded
#print axioms discovery_encoded
#print axioms discovery_schema
#print axioms discovery_family_iff
#print axioms index_family_iff
#print axioms reversalRules_from_admitted_source

end Mettapedia.GSLT.Parsing.PlainBnfCollectorSourceAdmission
