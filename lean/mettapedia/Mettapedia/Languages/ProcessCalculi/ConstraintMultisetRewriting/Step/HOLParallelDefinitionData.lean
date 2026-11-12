import Lean.Data.Json

/-! # Received HOL parallel-definition data

Generated from the independent HOL proof closure. The registered
receiver checks these records; this data carries no correctness claim.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelDefinitionData

private def node0 : Lean.Json := Lean.toJson (132166 : Nat)
private def node1 : Lean.Json := Lean.Json.str "DEFINITION"
private def node2 : Lean.Json := Lean.Json.str "app"
private def node3 : Lean.Json := Lean.Json.str "const"
private def node4 : Lean.Json := Lean.Json.str "="
private def node5 : Lean.Json := Lean.Json.str "op"
private def node6 : Lean.Json := Lean.Json.str "fun"
private def node7 : Lean.Json := Lean.Json.str "var"
private def node8 : Lean.Json := Lean.Json.str "T"
private def node9 : Lean.Json := Lean.Json.arr #[node7, node8]
private def node10 : Lean.Json := Lean.Json.str "bool"
private def node11 : Lean.Json := Lean.Json.arr #[]
private def node12 : Lean.Json := Lean.Json.arr #[node5, node10, node11]
private def node13 : Lean.Json := Lean.Json.arr #[node9, node12]
private def node14 : Lean.Json := Lean.Json.arr #[node5, node6, node13]
private def node15 : Lean.Json := Lean.Json.arr #[node9, node14]
private def node16 : Lean.Json := Lean.Json.arr #[node5, node6, node15]
private def node17 : Lean.Json := Lean.Json.arr #[node16, node16]
private def node18 : Lean.Json := Lean.Json.arr #[node5, node6, node17]
private def node19 : Lean.Json := Lean.Json.arr #[node16, node18]
private def node20 : Lean.Json := Lean.Json.arr #[node5, node6, node19]
private def node21 : Lean.Json := Lean.Json.arr #[node20, node12]
private def node22 : Lean.Json := Lean.Json.arr #[node5, node6, node21]
private def node23 : Lean.Json := Lean.Json.arr #[node20, node22]
private def node24 : Lean.Json := Lean.Json.arr #[node5, node6, node23]
private def node25 : Lean.Json := Lean.Json.arr #[node3, node4, node24]
private def node26 : Lean.Json := Lean.Json.str "tc_parallel_store"
private def node27 : Lean.Json := Lean.Json.arr #[node3, node26, node20]
private def node28 : Lean.Json := Lean.Json.arr #[node2, node25, node27]
private def node29 : Lean.Json := Lean.Json.str "abs"
private def node30 : Lean.Json := Lean.Json.str "left"
private def node31 : Lean.Json := Lean.Json.arr #[node7, node30, node16]
private def node32 : Lean.Json := Lean.Json.str "right"
private def node33 : Lean.Json := Lean.Json.arr #[node7, node32, node16]
private def node34 : Lean.Json := Lean.Json.str "x"
private def node35 : Lean.Json := Lean.Json.arr #[node7, node34, node9]
private def node36 : Lean.Json := Lean.Json.str "y"
private def node37 : Lean.Json := Lean.Json.arr #[node7, node36, node9]
private def node38 : Lean.Json := Lean.Json.str "\\/"
private def node39 : Lean.Json := Lean.Json.arr #[node12, node12]
private def node40 : Lean.Json := Lean.Json.arr #[node5, node6, node39]
private def node41 : Lean.Json := Lean.Json.arr #[node12, node40]
private def node42 : Lean.Json := Lean.Json.arr #[node5, node6, node41]
private def node43 : Lean.Json := Lean.Json.arr #[node3, node38, node42]
private def node44 : Lean.Json := Lean.Json.arr #[node2, node31, node35]
private def node45 : Lean.Json := Lean.Json.arr #[node2, node44, node37]
private def node46 : Lean.Json := Lean.Json.arr #[node2, node43, node45]
private def node47 : Lean.Json := Lean.Json.arr #[node2, node33, node35]
private def node48 : Lean.Json := Lean.Json.arr #[node2, node47, node37]
private def node49 : Lean.Json := Lean.Json.arr #[node2, node46, node48]
private def node50 : Lean.Json := Lean.Json.arr #[node29, node37, node49]
private def node51 : Lean.Json := Lean.Json.arr #[node29, node35, node50]
private def node52 : Lean.Json := Lean.Json.arr #[node29, node33, node51]
private def node53 : Lean.Json := Lean.Json.arr #[node29, node31, node52]
private def node54 : Lean.Json := Lean.Json.arr #[node2, node28, node53]
private def node55 : Lean.Json := Lean.Json.arr #[node54, node26, node20]
private def node56 : Lean.Json := Lean.Json.mkObj [("hypotheses", node11), ("conclusion", node54)]
private def node57 : Lean.Json := Lean.Json.mkObj [("id", node0), ("rule", node1), ("arguments", node55), ("theorem", node56)]
private def node58 : Lean.Json := Lean.toJson (132207 : Nat)
private def node59 : Lean.Json := Lean.Json.str "O"
private def node60 : Lean.Json := Lean.Json.arr #[node7, node59]
private def node61 : Lean.Json := Lean.Json.arr #[node60, node12]
private def node62 : Lean.Json := Lean.Json.arr #[node5, node6, node61]
private def node63 : Lean.Json := Lean.Json.arr #[node62, node62]
private def node64 : Lean.Json := Lean.Json.arr #[node5, node6, node63]
private def node65 : Lean.Json := Lean.Json.arr #[node62, node64]
private def node66 : Lean.Json := Lean.Json.arr #[node5, node6, node65]
private def node67 : Lean.Json := Lean.Json.arr #[node66, node12]
private def node68 : Lean.Json := Lean.Json.arr #[node5, node6, node67]
private def node69 : Lean.Json := Lean.Json.arr #[node66, node68]
private def node70 : Lean.Json := Lean.Json.arr #[node5, node6, node69]
private def node71 : Lean.Json := Lean.Json.arr #[node3, node4, node70]
private def node72 : Lean.Json := Lean.Json.str "tc_parallel_present"
private def node73 : Lean.Json := Lean.Json.arr #[node3, node72, node66]
private def node74 : Lean.Json := Lean.Json.arr #[node2, node71, node73]
private def node75 : Lean.Json := Lean.Json.arr #[node7, node30, node62]
private def node76 : Lean.Json := Lean.Json.arr #[node7, node32, node62]
private def node77 : Lean.Json := Lean.Json.str "occ"
private def node78 : Lean.Json := Lean.Json.arr #[node7, node77, node60]
private def node79 : Lean.Json := Lean.Json.arr #[node2, node75, node78]
private def node80 : Lean.Json := Lean.Json.arr #[node2, node43, node79]
private def node81 : Lean.Json := Lean.Json.arr #[node2, node76, node78]
private def node82 : Lean.Json := Lean.Json.arr #[node2, node80, node81]
private def node83 : Lean.Json := Lean.Json.arr #[node29, node78, node82]
private def node84 : Lean.Json := Lean.Json.arr #[node29, node76, node83]
private def node85 : Lean.Json := Lean.Json.arr #[node29, node75, node84]
private def node86 : Lean.Json := Lean.Json.arr #[node2, node74, node85]
private def node87 : Lean.Json := Lean.Json.arr #[node86, node72, node66]
private def node88 : Lean.Json := Lean.Json.mkObj [("hypotheses", node11), ("conclusion", node86)]
private def node89 : Lean.Json := Lean.Json.mkObj [("id", node58), ("rule", node1), ("arguments", node87), ("theorem", node88)]

def records : List Lean.Json := [node57, node89]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLParallelDefinitionData
