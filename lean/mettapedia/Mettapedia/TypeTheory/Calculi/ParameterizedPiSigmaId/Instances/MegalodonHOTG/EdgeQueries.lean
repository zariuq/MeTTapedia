import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Queries
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetConstantFamilies
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.ContextualPreservation
import Mettapedia.Logic.HOL.Embedding.ZFSetWellFoundedRecursion

/-!
# One query with several answers, on three faces

The program of the curriculum: a space holds four edges, one of them twice,

    (edge a b)  (edge a c)  (edge b a)  (edge a b)

and `hop x` asks for the targets of the edges that leave `x`. Run on `a` it gives `b`, `c`
and `b` again.

**The package** (`edges`), over the tower inside the sets: a type `node` with three terms
`a`, `b`, `c`; a type `edge@occurrence` with one term for each stored edge, `edge@a@b`,
`edge@a@c`, `edge@b@a` and `edge@a@b#2`; and the source and the target of an occurrence,
`edge@arg1` and `edge@arg2`, with one equation for each stored edge and each of the two
(`edge@arg1 (edge@a@b) ⟶ a`, `edge@arg2 (edge@a@b) ⟶ b`, and so on). The query is the type of
`MegalodonHOTG.Queries`: `hop x` is `Σ (o : edge@occurrence). Id node (edge@arg1 o) x`.

* **Typed.** `hop a` is a set (`hop_isSet`). The first, the second and the fourth occurrence
  give answers (`answer1_typed`, `answer2_typed`, `answer4_typed`): the key of each is equal
  to `a` by one equation of the package.
* **Run.** The value an answer returns reaches its node by two steps of the package, a
  projection and one equation (`return1_reduces`, `return2_reduces`, `return4_reduces`): `b`,
  `c`, `b`. The same holds as an equality of the judgment (`return1_equal`).
* **Sets.** In the model the occurrences that match `a` are exactly the first, the second and
  the fourth (`matching_a`); the first and the fourth are different answers that return one
  value (`answers_distinct`, `first_fourth_same_value`), so `b` is returned twice and `c`
  once; no occurrence leaves `c`, so `hop c` has no closed term (`hop_c_no_answer`).

So the three faces agree on this query: what the judgment types, what the run returns and
what the sets contain are the same three answers with the same counts. Nothing here types a
pattern with variables against stored atoms; the occurrences are named one by one.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace Queries
namespace Edges

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory.ZFSetOrderedPair (first first_pair)
open ZFSetUniverseClosure (Closed CofinalInaccessibles)
open ZFSetInterpretation (universeSet seed_mem_universeSet)
open ZFSetDependentProducts (graph)
open ZFSetTraceProducts (traceLam traceApp tracePiSet traceApp_graph_beta)
open ZFSetWellFoundedRecursion (numeral_mem_iff)
open ZFSetInductive (numeral_mem_of_omega)

universe u

variable {L : Type}

/-! ## The constants -/

/-- The type of nodes. -/
def nodeN : DeclName := .str .anonymous "node"
/-- A node. -/
def aN : DeclName := .str .anonymous "a"
/-- A node. -/
def bN : DeclName := .str .anonymous "b"
/-- A node. -/
def cN : DeclName := .str .anonymous "c"
/-- The type of stored occurrences. -/
def occN : DeclName := .str .anonymous "edge@occurrence"
/-- The first stored edge, from `a` to `b`. -/
def o1N : DeclName := .str .anonymous "edge@a@b"
/-- The second stored edge, from `a` to `c`. -/
def o2N : DeclName := .str .anonymous "edge@a@c"
/-- The third stored edge, from `b` to `a`. -/
def o3N : DeclName := .str .anonymous "edge@b@a"
/-- The fourth stored edge, from `a` to `b` again. -/
def o4N : DeclName := .str .anonymous "edge@a@b#2"
/-- The source of a stored edge. -/
def srcN : DeclName := .str .anonymous "edge@arg1"
/-- The target of a stored edge. -/
def dstN : DeclName := .str .anonymous "edge@arg2"

section Terms

variable [LevelOrder L] {n : Nat}

/-- `node`. -/
abbrev cNode : CTm (Head L) n := .const nodeN
/-- `a`. -/
abbrev cA : CTm (Head L) n := .const aN
/-- `b`. -/
abbrev cB : CTm (Head L) n := .const bN
/-- `c`. -/
abbrev cC : CTm (Head L) n := .const cN
/-- `edge@occurrence`. -/
abbrev cOcc : CTm (Head L) n := .const occN
/-- `edge@a@b`. -/
abbrev cO1 : CTm (Head L) n := .const o1N
/-- `edge@a@c`. -/
abbrev cO2 : CTm (Head L) n := .const o2N
/-- `edge@b@a`. -/
abbrev cO3 : CTm (Head L) n := .const o3N
/-- `edge@a@b#2`. -/
abbrev cO4 : CTm (Head L) n := .const o4N
/-- `edge@arg1`. -/
abbrev cSrc : CTm (Head L) n := .const srcN
/-- `edge@arg2`. -/
abbrev cDst : CTm (Head L) n := .const dstN
/-- The type of `edge@arg1` and of `edge@arg2`: an occurrence gives a node. -/
abbrev edgeMap : CTm (Head L) n := .pi cOcc cNode
/-- **The query**: the stored edges that leave `x`. -/
abbrev hop (x : CTm (Head L) n) : CTm (Head L) n := cQuery cOcc cNode cSrc x

end Terms

variable [LevelOrder L]

variable (L) in
/-- The table of the constants: each with its type. -/
def table : List (DeclName × CTm (Head L) 0) :=
  [(nodeN, U0), (aN, cNode), (bN, cNode), (cN, cNode), (occN, U0),
    (o1N, cOcc), (o2N, cOcc), (o3N, cOcc), (o4N, cOcc), (srcN, edgeMap), (dstN, edgeMap)]

variable (L) in
/-- The declarations of the constants. -/
def decls : DeclName → Option (CTm (Head L) 0) := tableLookup (table L)

variable (L) in
/-- One stored fact: `f o ⟶ v`. -/
def fact (f o v : DeclName) : DefiningEquation (Head L) where
  arity := 0
  telescope := .nil
  left := .app (.const f) (.const o)
  right := .const v

variable (L) in
/-- The equations: the source and the target of each stored edge. -/
def equations : List (DefiningEquation (Head L)) :=
  [fact L srcN o1N aN, fact L dstN o1N bN, fact L srcN o2N aN, fact L dstN o2N cN,
    fact L srcN o3N bN, fact L dstN o3N aN, fact L srcN o4N aN, fact L dstN o4N bN]

variable (L) in
/-- The tower inside the sets with the nodes, the stored edges and their sources and
targets. -/
abbrev edges := withFamily (bare L) (decls L) (equations L)

theorem decls_node : decls L nodeN = some U0 := rfl
theorem decls_a : decls L aN = some cNode := rfl
theorem decls_b : decls L bN = some cNode := rfl
theorem decls_c : decls L cN = some cNode := rfl
theorem decls_occ : decls L occN = some U0 := rfl
theorem decls_o1 : decls L o1N = some cOcc := rfl
theorem decls_o2 : decls L o2N = some cOcc := rfl
theorem decls_o3 : decls L o3N = some cOcc := rfl
theorem decls_o4 : decls L o4N = some cOcc := rfl
theorem decls_src : decls L srcN = some edgeMap := rfl
theorem decls_dst : decls L dstN = some edgeMap := rfl

/-! ## In the judgment -/

section Judgment

variable {n : Nat} {Γ : CCtx (Head L) n}

/-- A constant is declared in the package as the table declares it. -/
theorem declared {c : DeclName} {T : CTm (Head L) 0} (known : decls L c = some T) :
    (edges L).constantType c = some T :=
  (withFamily_declared (bare L) rfl).trans known

/-- The package contains the steps of its equations. -/
theorem computes :
    StepsWithin (familyChurch (rules L) (decls L) (equations L)) (edges L) :=
  StepsWithin.sum_right (bare L) (familyChurch (rules L) (decls L) (equations L))

/-- The least universe is a type. -/
theorem least_typed : CTyped (edges L) Γ U0 (universeAt (LevelOrder.succ LevelOrder.bot)) :=
  universe_typed package_contains LevelOrder.bot

/-- `node` is a type of the least universe. -/
theorem node_typed : CTyped (edges L) Γ cNode U0 :=
  definition_typed (declared decls_node) (least_typed (Γ := .nil))
    (package_contains.isUniverse (.sort _))

/-- `edge@occurrence` is a type of the least universe. -/
theorem occ_typed : CTyped (edges L) Γ cOcc U0 :=
  definition_typed (declared decls_occ) (least_typed (Γ := .nil))
    (package_contains.isUniverse (.sort _))

/-- `node` is a set. -/
theorem node_isSet : CTyped (edges L) Γ cNode allSets := small_isSet package_contains node_typed

/-- `edge@occurrence` is a set. -/
theorem occ_isSet : CTyped (edges L) Γ cOcc allSets := small_isSet package_contains occ_typed

theorem a_typed : CTyped (edges L) Γ cA cNode :=
  definition_typed (declared decls_a) (node_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

theorem b_typed : CTyped (edges L) Γ cB cNode :=
  definition_typed (declared decls_b) (node_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

theorem c_typed : CTyped (edges L) Γ cC cNode :=
  definition_typed (declared decls_c) (node_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

theorem o1_typed : CTyped (edges L) Γ cO1 cOcc :=
  definition_typed (declared decls_o1) (occ_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

theorem o2_typed : CTyped (edges L) Γ cO2 cOcc :=
  definition_typed (declared decls_o2) (occ_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

theorem o3_typed : CTyped (edges L) Γ cO3 cOcc :=
  definition_typed (declared decls_o3) (occ_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

theorem o4_typed : CTyped (edges L) Γ cO4 cOcc :=
  definition_typed (declared decls_o4) (occ_typed (Γ := .nil)) (package_contains.isUniverse (.sort _))

/-- The type of `edge@arg1` and `edge@arg2` is a type of the least universe. -/
theorem edgeMap_typed : CTyped (edges L) Γ edgeMap U0 :=
  CDerivable.cumul
    (.piForm occ_typed (package_contains.isUniverse (.sort _)) node_typed
      (package_contains.isUniverse (.sort _)) (package_contains.join (.sorts _ _)))
    (package_contains.cumulative
      (u := .sort (.max (.const (.below LevelOrder.bot)) (.const (.below LevelOrder.bot))))
      (v := .sort (.const (.below LevelOrder.bot))) fun _ => max_le (le_refl _) (le_refl _))

/-- `edge@arg1` takes an occurrence to a node. -/
theorem src_typed : CTyped (edges L) Γ cSrc edgeMap :=
  definition_typed (declared decls_src) (edgeMap_typed (Γ := .nil))
    (package_contains.isUniverse (.sort _))

/-- `edge@arg2` takes an occurrence to a node. -/
theorem dst_typed : CTyped (edges L) Γ cDst edgeMap :=
  definition_typed (declared decls_dst) (edgeMap_typed (Γ := .nil))
    (package_contains.isUniverse (.sort _))

/-- **A stored fact holds in the judgment**: `f o` is equal to `v`, as nodes. -/
theorem fact_rule {f o v : DeclName} (member : fact L f o v ∈ equations L)
    (hf : CTyped (edges L) Γ (.const f) edgeMap) (ho : CTyped (edges L) Γ (.const o) cOcc)
    (hv : CTyped (edges L) Γ (.const v) cNode) :
    CEqual (edges L) Γ (.app (.const f) (.const o)) (.const v) cNode :=
  family_equation_holds (rules L) computes (e := fact L f o v) member (fun i => i.elim0)
    (fun i => i.elim0) (.appElim (B := cNode) hf ho) hv

/-- **A stored fact is a step of the package.** -/
theorem fact_step {f o v : DeclName} (member : fact L f o v ∈ equations L) :
    (edges L).computation.step (.app (.const f) (.const o) : CTm (Head L) n) (.const v) :=
  computes.step ⟨fact L f o v, member, fun i => i.elim0, rfl, rfl⟩

omit [LevelOrder L] in
theorem src1_member : fact L srcN o1N aN ∈ equations L := List.mem_cons_self
omit [LevelOrder L] in
theorem dst1_member : fact L dstN o1N bN ∈ equations L :=
  List.mem_cons_of_mem _ List.mem_cons_self
omit [LevelOrder L] in
theorem src2_member : fact L srcN o2N aN ∈ equations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
omit [LevelOrder L] in
theorem dst2_member : fact L dstN o2N cN ∈ equations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
omit [LevelOrder L] in
theorem src4_member : fact L srcN o4N aN ∈ equations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))))
omit [LevelOrder L] in
theorem dst4_member : fact L dstN o4N bN ∈ equations L :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))))

/-- **The type of the answers of `hop x` is a set.** -/
theorem hop_isSet {x : CTm (Head L) n} (hx : CTyped (edges L) Γ x cNode) :
    CTyped (edges L) Γ (hop x) allSets :=
  query_isSet package_contains occ_isSet node_isSet src_typed hx

/-- **The first stored edge answers `hop a`.** -/
theorem answer1_typed : CTyped (edges L) Γ (cAnswer cSrc cO1) (hop cA) :=
  answer_typed package_contains occ_isSet node_isSet src_typed a_typed o1_typed
    (fact_rule src1_member src_typed o1_typed a_typed)

/-- **The second stored edge answers `hop a`.** -/
theorem answer2_typed : CTyped (edges L) Γ (cAnswer cSrc cO2) (hop cA) :=
  answer_typed package_contains occ_isSet node_isSet src_typed a_typed o2_typed
    (fact_rule src2_member src_typed o2_typed a_typed)

/-- **The fourth stored edge answers `hop a`.** -/
theorem answer4_typed : CTyped (edges L) Γ (cAnswer cSrc cO4) (hop cA) :=
  answer_typed package_contains occ_isSet node_isSet src_typed a_typed o4_typed
    (fact_rule src4_member src_typed o4_typed a_typed)

/-- The value an answer returns is a node. -/
theorem return_node {q x : CTm (Head L) n} (hq : CTyped (edges L) Γ q (hop x)) :
    CTyped (edges L) Γ (cReturn cDst q) cNode :=
  return_typed (T := cNode) dst_typed hq

/-- **Run: the value an answer returns reaches its node by a projection and one stored
fact.** -/
theorem return_reduces {o v : DeclName} (member : fact L dstN o v ∈ equations L) :
    CReduces (edges L) (cReturn cDst (cAnswer cSrc (.const o)) : CTm (Head L) n) (.const v) :=
  .tail (.single (.congAppArg (.betaSigmaFst _ _))) (.root (fact_step member))

/-- The first answer returns `b`. -/
theorem return1_reduces :
    CReduces (edges L) (cReturn cDst (cAnswer cSrc cO1) : CTm (Head L) n) cB :=
  return_reduces dst1_member

/-- The second answer returns `c`. -/
theorem return2_reduces :
    CReduces (edges L) (cReturn cDst (cAnswer cSrc cO2) : CTm (Head L) n) cC :=
  return_reduces dst2_member

/-- The fourth answer returns `b` again. -/
theorem return4_reduces :
    CReduces (edges L) (cReturn cDst (cAnswer cSrc cO4) : CTm (Head L) n) cB :=
  return_reduces dst4_member

/-- The same as an equality of the judgment: the first answer returns `b`. -/
theorem return1_equal :
    CEqual (edges L) Γ (cReturn cDst (cAnswer cSrc cO1)) cB cNode := by
  have keyed : CTyped (edges L) Γ (.app cSrc cO1) cNode := key_typed src_typed o1_typed
  have evidence : CTyped (edges L) Γ (.refl (.app cSrc cO1))
      (CTm.inst0 cO1 (.id cNode (.app cSrc (.var 0)) cA)) :=
    .conv (.reflIntro keyed)
      (.idCong (.refl node_isSet) (package_contains.isUniverse (.sort _)) (.refl keyed)
        (fact_rule src1_member src_typed o1_typed a_typed))
      (package_contains.isUniverse (.sort _))
  have projected : CEqual (edges L) Γ (.fst (cAnswer cSrc cO1)) cO1 cOcc :=
    .betaFst (hop_isSet a_typed) (package_contains.isUniverse (.sort _)) o1_typed evidence
  exact .trans (.appCong (B := cNode) (.refl dst_typed) projected)
    (fact_rule dst1_member dst_typed o1_typed b_typed)

end Judgment

/-! ## In the sets -/

section Model

open Classical in
/-- The source of an occurrence, on sets: the third stored edge leaves `b`, the others leave
`a`. -/
noncomputable def srcFun (x : ZFSet.{u}) : ZFSet.{u} :=
  if x = numeral 2 then numeral 1 else numeral 0

open Classical in
/-- The target of an occurrence, on sets. -/
noncomputable def dstFun (x : ZFSet.{u}) : ZFSet.{u} :=
  if x = numeral 0 then numeral 1 else if x = numeral 1 then numeral 2
  else if x = numeral 2 then numeral 0 else numeral 1

theorem srcFun_two : srcFun.{u} (numeral 2) = numeral 1 := by
  unfold srcFun
  exact if_pos rfl

theorem srcFun_of_ne {i : Nat} (other : i ≠ 2) : srcFun.{u} (numeral i) = numeral 0 := by
  unfold srcFun
  exact if_neg fun same => other (numeral_injective same)

theorem srcFun_mem (x : ZFSet.{u}) : srcFun x ∈ (numeral 3 : ZFSet.{u}) := by
  unfold srcFun
  split
  · exact (numeral_mem_iff 1 3).mpr (by decide)
  · exact (numeral_mem_iff 0 3).mpr (by decide)

theorem dstFun_zero : dstFun.{u} (numeral 0) = numeral 1 := by
  unfold dstFun
  exact if_pos rfl

theorem dstFun_one : dstFun.{u} (numeral 1) = numeral 2 := by
  unfold dstFun
  rw [if_neg fun same => absurd (numeral_injective same) (by decide), if_pos rfl]

theorem dstFun_two : dstFun.{u} (numeral 2) = numeral 0 := by
  unfold dstFun
  rw [if_neg fun same => absurd (numeral_injective same) (by decide),
    if_neg fun same => absurd (numeral_injective same) (by decide), if_pos rfl]

theorem dstFun_three : dstFun.{u} (numeral 3) = numeral 1 := by
  unfold dstFun
  rw [if_neg fun same => absurd (numeral_injective same) (by decide),
    if_neg fun same => absurd (numeral_injective same) (by decide),
    if_neg fun same => absurd (numeral_injective same) (by decide)]

theorem dstFun_mem (x : ZFSet.{u}) : dstFun x ∈ (numeral 3 : ZFSet.{u}) := by
  unfold dstFun
  split
  · exact (numeral_mem_iff 1 3).mpr (by decide)
  · split
    · exact (numeral_mem_iff 2 3).mpr (by decide)
    · split
      · exact (numeral_mem_iff 0 3).mpr (by decide)
      · exact (numeral_mem_iff 1 3).mpr (by decide)

/-- `edge@arg1` as a set: the trace of the source on the four occurrences. -/
noncomputable def srcValue : ZFSet.{u} := traceLam (graph (numeral 4) srcFun)

/-- `edge@arg2` as a set: the trace of the target on the four occurrences. -/
noncomputable def dstValue : ZFSet.{u} := traceLam (graph (numeral 4) dstFun)

/-- The table of the values: three nodes, four occurrences, and the two traces. -/
noncomputable def valueTable : List (DeclName × ZFSet.{u}) :=
  [(nodeN, numeral 3), (aN, numeral 0), (bN, numeral 1), (cN, numeral 2), (occN, numeral 4),
    (o1N, numeral 0), (o2N, numeral 1), (o3N, numeral 2), (o4N, numeral 3),
    (srcN, srcValue), (dstN, dstValue)]

/-- The values of the constants. -/
noncomputable def values : DeclName → ZFSet.{u} := fun c =>
  (tableLookup valueTable c).getD ∅

theorem values_node : values.{u} nodeN = numeral 3 := rfl
theorem values_a : values.{u} aN = numeral 0 := rfl
theorem values_b : values.{u} bN = numeral 1 := rfl
theorem values_c : values.{u} cN = numeral 2 := rfl
theorem values_occ : values.{u} occN = numeral 4 := rfl
theorem values_o1 : values.{u} o1N = numeral 0 := rfl
theorem values_o2 : values.{u} o2N = numeral 1 := rfl
theorem values_o3 : values.{u} o3N = numeral 2 := rfl
theorem values_o4 : values.{u} o4N = numeral 3 := rfl
theorem values_src : values.{u} srcN = srcValue := rfl
theorem values_dst : values.{u} dstN = dstValue := rfl

/-- The source of the `i`-th occurrence, read off the trace. -/
theorem src_at (i : Nat) (small : i < 4) :
    traceApp srcValue.{u} (numeral i) = srcFun (numeral i) :=
  traceApp_graph_beta srcFun ((numeral_mem_iff i 4).mpr small)

/-- The target of the `i`-th occurrence, read off the trace. -/
theorem dst_at (i : Nat) (small : i < 4) :
    traceApp dstValue.{u} (numeral i) = dstFun (numeral i) :=
  traceApp_graph_beta dstFun ((numeral_mem_iff i 4).mpr small)

/-- A member of the fourth numeral is one of the first four numerals. -/
theorem mem_four {x : ZFSet.{u}} (member : x ∈ (numeral 4 : ZFSet.{u})) :
    x = numeral 0 ∨ x = numeral 1 ∨ x = numeral 2 ∨ x = numeral 3 := by
  rcases ZFSet.mem_insert_iff.mp (show x ∈ insert (numeral 3) (numeral 3) from member) with
    rfl | member
  · exact .inr (.inr (.inr rfl))
  rcases ZFSet.mem_insert_iff.mp (show x ∈ insert (numeral 2) (numeral 2) from member) with
    rfl | member
  · exact .inr (.inr (.inl rfl))
  rcases ZFSet.mem_insert_iff.mp (show x ∈ insert (numeral 1) (numeral 1) from member) with
    rfl | member
  · exact .inr (.inl rfl)
  rcases ZFSet.mem_insert_iff.mp (show x ∈ insert (numeral 0) (numeral 0) from member) with
    rfl | member
  · exact .inl rfl
  · exact (ZFSet.notMem_empty x member).elim

variable {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}} {ν : Nat → Above L}
  {consts : DeclName → ZFSet.{u}}

/-- An assignment that gives the constants their values. -/
abbrev Reads (consts : DeclName → ZFSet.{u}) : Prop :=
  ∀ c, decls L c ≠ none → consts c = values c

/-- The value an assignment gives a declared constant. -/
theorem Reads.at (reads : Reads (L := L) consts) {c : DeclName} {T : CTm (Head L) 0}
    (known : decls L c = some T) : consts c = values c :=
  reads c (by rw [known]; exact Option.some_ne_none T)

variable (chain : ClosedChain V) (omegaMem : ZFSet.omega ∈ V (.below LevelOrder.bot))

include chain omegaMem in
/-- Every value lies in the set of its constant's type. -/
theorem values_typed (reads : Reads (L := L) consts) {c : DeclName} {T : CTm (Head L) 0}
    (known : decls L c = some T) :
    values c ∈ ev (chainHead V ground ν) consts T Fin.elim0 := by
  have closed : Closed (V (.below LevelOrder.bot)) := chain.closed (.below LevelOrder.bot)
  have row := tableLookup_mem known
  simp only [table, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at row
  rcases row with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show (numeral 3 : ZFSet.{u}) ∈ V (.below LevelOrder.bot)
    exact numeral_mem_of_omega closed omegaMem 3
  · show (numeral 0 : ZFSet.{u}) ∈ consts nodeN
    rw [reads.at decls_node, values_node]
    exact (numeral_mem_iff 0 3).mpr (by decide)
  · show (numeral 1 : ZFSet.{u}) ∈ consts nodeN
    rw [reads.at decls_node, values_node]
    exact (numeral_mem_iff 1 3).mpr (by decide)
  · show (numeral 2 : ZFSet.{u}) ∈ consts nodeN
    rw [reads.at decls_node, values_node]
    exact (numeral_mem_iff 2 3).mpr (by decide)
  · show (numeral 4 : ZFSet.{u}) ∈ V (.below LevelOrder.bot)
    exact numeral_mem_of_omega closed omegaMem 4
  · show (numeral 0 : ZFSet.{u}) ∈ consts occN
    rw [reads.at decls_occ, values_occ]
    exact (numeral_mem_iff 0 4).mpr (by decide)
  · show (numeral 1 : ZFSet.{u}) ∈ consts occN
    rw [reads.at decls_occ, values_occ]
    exact (numeral_mem_iff 1 4).mpr (by decide)
  · show (numeral 2 : ZFSet.{u}) ∈ consts occN
    rw [reads.at decls_occ, values_occ]
    exact (numeral_mem_iff 2 4).mpr (by decide)
  · show (numeral 3 : ZFSet.{u}) ∈ consts occN
    rw [reads.at decls_occ, values_occ]
    exact (numeral_mem_iff 3 4).mpr (by decide)
  · show srcValue ∈ tracePiSet (consts occN) fun _ => consts nodeN
    rw [reads.at decls_occ, reads.at decls_node, values_occ, values_node]
    exact traceLam_graph_mem fun x _ => srcFun_mem x
  · show dstValue ∈ tracePiSet (consts occN) fun _ => consts nodeN
    rw [reads.at decls_occ, reads.at decls_node, values_occ, values_node]
    exact traceLam_graph_mem fun x _ => dstFun_mem x

/-- The value of a stored fact's left side, under an assignment that reads the constants. -/
theorem fact_value (reads : Reads (L := L) consts) {f o : DeclName} {F O : CTm (Head L) 0}
    (hf : decls L f = some F) (ho : decls L o = some O) (η : Env.{u} 0) :
    ev (chainHead V ground ν) consts (.app (.const f) (.const o) : CTm (Head L) 0) η =
      traceApp (values f) (values o) := by
  show traceApp (consts f) (consts o) = _
  rw [reads.at hf, reads.at ho]

/-- Every stored fact holds between sets. -/
theorem equations_valid (reads : Reads (L := L) consts) :
    ∀ e ∈ equations L, ∀ η : Env.{u} e.arity,
      Sat (chainHead V ground ν) consts e.telescope η →
        ev (chainHead V ground ν) consts e.left η =
          ev (chainHead V ground ν) consts e.right η := by
  intro e member η _
  simp only [equations, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (fact_value reads decls_src decls_o1 η).trans
      (((src_at 0 (by decide)).trans (srcFun_of_ne (by decide))).trans (reads.at decls_a).symm)
  · exact (fact_value reads decls_dst decls_o1 η).trans
      (((dst_at 0 (by decide)).trans dstFun_zero).trans (reads.at decls_b).symm)
  · exact (fact_value reads decls_src decls_o2 η).trans
      (((src_at 1 (by decide)).trans (srcFun_of_ne (by decide))).trans (reads.at decls_a).symm)
  · exact (fact_value reads decls_dst decls_o2 η).trans
      (((dst_at 1 (by decide)).trans dstFun_one).trans (reads.at decls_c).symm)
  · exact (fact_value reads decls_src decls_o3 η).trans
      (((src_at 2 (by decide)).trans srcFun_two).trans (reads.at decls_b).symm)
  · exact (fact_value reads decls_dst decls_o3 η).trans
      (((dst_at 2 (by decide)).trans dstFun_two).trans (reads.at decls_a).symm)
  · exact (fact_value reads decls_src decls_o4 η).trans
      (((src_at 3 (by decide)).trans (srcFun_of_ne (by decide))).trans (reads.at decls_a).symm)
  · exact (fact_value reads decls_dst decls_o4 η).trans
      (((dst_at 3 (by decide)).trans dstFun_three).trans (reads.at decls_b).symm)

include chain omegaMem in
/-- **The package has a set model**, over every chain of closed universes whose least one has
the natural numbers. -/
theorem edges_setModel (groundTyped : ground ∈ V LevelOrder.bot)
    (base : DeclName → ZFSet.{u}) :
    SetModel (chainHead V ground ν) (familyConsts base (decls L) values) (edges L) :=
  family_setModel_read (bare L)
    (fun consts _ => chain_setModel chain groundTyped ν consts) (fun _ _ => rfl) values
    (fun _ _ reads {_ _} known => values_typed chain omegaMem reads known)
    (fun _ _ reads => equations_valid reads)

/-- The assignment of the model reads the constants. -/
theorem model_reads (base : DeclName → ZFSet.{u}) :
    Reads (L := L) (familyConsts base (decls L) values) :=
  fun _ known => familyConsts_declared known

/-- **The occurrences that match `a`, in the sets: the first, the second and the fourth.** -/
theorem matching_a (base : DeclName → ZFSet.{u}) (x : ZFSet.{u}) :
    Matching (heads := chainHead V ground ν) (consts := familyConsts base (decls L) values)
        (cOcc : CTm (Head L) 0) cSrc cA Fin.elim0 x ↔
      x = numeral 0 ∨ x = numeral 1 ∨ x = numeral 3 := by
  have reads := model_reads (L := L) base
  show (x ∈ familyConsts base (decls L) values occN ∧
      traceApp (familyConsts base (decls L) values srcN) x =
        familyConsts base (decls L) values aN) ↔ _
  rw [reads.at decls_occ, reads.at decls_src, reads.at decls_a, values_occ, values_src,
    values_a]
  constructor
  · rintro ⟨member, same⟩
    rcases mem_four member with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · rw [src_at 2 (by decide), srcFun_two] at same
      exact absurd (numeral_injective same) (by decide)
    · exact .inr (.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨(numeral_mem_iff 0 4).mpr (by decide),
        (src_at 0 (by decide)).trans (srcFun_of_ne (by decide))⟩
    · exact ⟨(numeral_mem_iff 1 4).mpr (by decide),
        (src_at 1 (by decide)).trans (srcFun_of_ne (by decide))⟩
    · exact ⟨(numeral_mem_iff 3 4).mpr (by decide),
        (src_at 3 (by decide)).trans (srcFun_of_ne (by decide))⟩

/-- The value of the answer of the `i`-th occurrence, in the model. -/
theorem answer_value (base : DeclName → ZFSet.{u}) {o : DeclName} {O : CTm (Head L) 0}
    (known : decls L o = some O) :
    ev (chainHead V ground ν) (familyConsts base (decls L) values)
        (cAnswer cSrc (.const o) : CTm (Head L) 0) Fin.elim0 = ZFSet.pair (values o) ∅ := by
  rw [ev_answer]
  show ZFSet.pair (familyConsts base (decls L) values o) ∅ = _
  rw [(model_reads (L := L) base).at known]

/-- **The first and the fourth answer are different answers.** -/
theorem answers_distinct (base : DeclName → ZFSet.{u}) :
    ev (chainHead V ground ν) (familyConsts base (decls L) values)
        (cAnswer cSrc cO1 : CTm (Head L) 0) Fin.elim0 ≠
      ev (chainHead V ground ν) (familyConsts base (decls L) values)
        (cAnswer cSrc cO4 : CTm (Head L) 0) Fin.elim0 := by
  rw [answer_value base decls_o1, answer_value base decls_o4, values_o1, values_o4]
  intro same
  exact absurd (numeral_injective (ZFSet.pair_inj.mp same).1) (by decide)

/-- **They return one value**: both targets are `b`. -/
theorem first_fourth_same_value :
    traceApp dstValue.{u} (numeral 0) = traceApp dstValue.{u} (numeral 3) := by
  rw [dst_at 0 (by decide), dst_at 3 (by decide), dstFun_zero, dstFun_three]

include chain omegaMem in
/-- Negative example: **no stored edge leaves `c`, so `hop c` has no closed term.** -/
theorem hop_c_no_answer (groundTyped : ground ∈ V LevelOrder.bot) (q : CTm (Head L) 0) :
    ¬ CTyped (edges L) .nil q (hop cC) := by
  refine no_answer
    (edges_setModel (ν := fun _ => LevelOrder.bot) chain omegaMem groundTyped fun _ => ∅)
    (fun x matching => ?_) q
  have reads := model_reads (L := L) (fun _ => (∅ : ZFSet.{u}))
  have member : x ∈ familyConsts (fun _ => ∅) (decls L) values occN := matching.1
  have same : traceApp (familyConsts (fun _ => ∅) (decls L) values srcN) x =
      familyConsts (fun _ => ∅) (decls L) values cN := matching.2
  rw [reads.at decls_occ, values_occ] at member
  rw [reads.at decls_src, reads.at decls_c, values_src, values_c] at same
  rcases mem_four member with rfl | rfl | rfl | rfl
  · rw [src_at 0 (by decide), srcFun_of_ne (by decide)] at same
    exact absurd (numeral_injective same) (by decide)
  · rw [src_at 1 (by decide), srcFun_of_ne (by decide)] at same
    exact absurd (numeral_injective same) (by decide)
  · rw [src_at 2 (by decide), srcFun_two] at same
    exact absurd (numeral_injective same) (by decide)
  · rw [src_at 3 (by decide), srcFun_of_ne (by decide)] at same
    exact absurd (numeral_injective same) (by decide)

end Model

/-! ## On the stages -/

section LowerSets

variable (small : CofinalInaccessibles.{u}) (large : CofinalInaccessibles.{u + 1})

include small large in
/-- `hop c` has no closed term, relative to cofinally many inaccessible cardinals in two
universes. -/
theorem lowerSets_hop_c_no_answer (q : CTm (Head L) 0) :
    ¬ CTyped (edges L) .nil q (hop cC) :=
  hop_c_no_answer (stages_closedChain small large)
    (seed_mem_universeSet large ZFSet.omega (LevelOrder.bot : L))
    (empty_mem_universeSet large ZFSet.omega (LevelOrder.bot : L)) q

end LowerSets

end Edges
end Queries
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
