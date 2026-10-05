import Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity.Triangle
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.EdgeQueries

/-!
# One query with several answers: the three faces joined

The query of the curriculum asks a space of four stored edges, `(edge a b)`, `(edge a c)`,
`(edge b a)` and `(edge a b)` again, for the targets of the edges that leave a node:
`hop x = match &kb (edge x $y) $y`. `MegalodonHOTG.EdgeQueries` treats its faces one by one: the
answers of `hop x` are a type, the pairs of a stored occurrence with a proof that its source is
`x` (`cQuery`), and in the sets they are the matching occurrences (`mem_query`,
`answersEquiv`). This module runs the query and joins the three faces.

**Running.** A key is a node, or the source or the target of a stored edge (`KeyExpr`). It runs
to a node by the stored facts, which are steps of the package (`KeyExpr.runs`). The query then
walks the stored space and returns one answer for each occurrence whose source is that node
(`runQuery`): `hop a` returns the first, the second and the fourth occurrence, with the values
`b`, `c` and `b`. Every answer the run returns is a typed answer (`answer_typed_of_run`), and
the value it returns runs to the target of its occurrence (`answer_returns`).

**Three maps, built separately.** `typing` sends a key to the type of the answers of its
query; `meaning` sends a typed term to its value in the set model of the package
(`edges_setModel`); `direct` sends a key to the bag of answers the run returns, read as the set
of its answers, each occurrence paired with the empty set (`answersSet`). The direct map uses
neither the typed term nor the model.

**The triangle commutes by proof** (`meaning_typing`): the answers of the typed query, in the
sets, are exactly the answers the run returns (`mem_meaning`). Counts are kept: the answers
that return a value are the occurrences of the bag that return it, one answer each
(`mem_meaning_returning`), so `hop a` returns `b` twice, through two different answers
(`hop_a_returns_b_twice`).

**The triangle is not exact** (`queryTriangle_loses`): `hop a` and `hop (dst o3)` are
different programs, and the target of the third stored edge is `a`, so they have one set of
answers. The set does not keep how the key was written.

Negative example: the bag read as the set of the values it returns keeps one answer for each
value (`onePerValue`). At `hop a` it drops one of the two answers that return `b`, and the
typed query has both, so these three maps form no triangle (`onePerValue_disagrees`).

Not here: other stored spaces, and the stored edges as atoms matched against a pattern with
variables; the space is fixed and its occurrences are named one by one. A call to stored
rules, where two rules with one left side contribute each answer of the right side twice, is
outside these six pieces. The typed statement of that doubling is `answersCallEquiv`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonHOTG.Query

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG.Queries
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.MegalodonHOTG.Queries.Edges
open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open Mettapedia.SetTheory.ZFSetOrderedPair (first first_pair)
open ZFSetTraceProducts (traceApp)
open ZFSetWellFoundedRecursion (numeral_mem_iff)
open Mettapedia.Languages.MeTTa.PrimeCandidates.Trinity
open Mettapedia.Computability.ComputationalTrinity

universe u

/-! ## The stored space and the run -/

/-- **The stored space**: the source and the target of each of the four stored edges, with the
nodes `a`, `b`, `c` numbered `0`, `1`, `2`. -/
def stored : Fin 4 → Fin 3 × Fin 3 := ![(0, 1), (0, 2), (1, 0), (0, 1)]

/-- The names of the three nodes. -/
def nodeName : Fin 3 → DeclName := ![aN, bN, cN]

/-- The names of the four stored occurrences. -/
def occName : Fin 4 → DeclName := ![o1N, o2N, o3N, o4N]

/-- **A closed key**: a node, or the source or the target of a stored edge. -/
inductive KeyExpr where
  | node (x : Fin 3)
  | src (o : Fin 4)
  | dst (o : Fin 4)
  deriving DecidableEq, Repr

/-- **The node a key runs to**, by the stored facts. -/
def KeyExpr.run : KeyExpr → Fin 3
  | .node x => x
  | .src o => (stored o).1
  | .dst o => (stored o).2

/-- **Running `hop k`**: the stored occurrences, in order, whose source is the node the key runs
to. Each is an answer; an edge stored twice gives two answers. -/
def runQuery (k : KeyExpr) : List (Fin 4) :=
  (List.finRange 4).filter fun i => (stored i).1 = k.run

/-- The value an answer returns: the target of its occurrence. -/
def returned (i : Fin 4) : Fin 3 := (stored i).2

/-- Positive example: `hop a` returns the first, the second and the fourth occurrence, with the
values `b`, `c`, `b`. -/
example : runQuery (.node 0) = [0, 1, 3] ∧ (runQuery (.node 0)).map returned = [1, 2, 1] := by
  decide

/-- Negative example: no stored edge leaves `c`. -/
example : runQuery (.node 2) = [] := by decide

theorem mem_runQuery {k : KeyExpr} {i : Fin 4} : i ∈ runQuery k ↔ (stored i).1 = k.run := by
  simp [runQuery]

section Terms

variable {L : Type} [LevelOrder L]

/-- The term of a key. -/
def KeyExpr.toTerm : KeyExpr → CTm (Head L) 0
  | .node x => .const (nodeName x)
  | .src o => .app cSrc (.const (occName o))
  | .dst o => .app cDst (.const (occName o))

theorem nodeName_declared (x : Fin 3) : decls L (nodeName x) = some cNode := by
  fin_cases x <;> rfl

theorem occName_declared (o : Fin 4) : decls L (occName o) = some cOcc := by
  fin_cases o <;> rfl

/-- A node is a node. -/
theorem nodeConst_typed (x : Fin 3) : CTyped (edges L) .nil (.const (nodeName x)) cNode := by
  fin_cases x
  · exact a_typed
  · exact b_typed
  · exact c_typed

/-- A stored occurrence is an occurrence. -/
theorem occConst_typed (o : Fin 4) : CTyped (edges L) .nil (.const (occName o)) cOcc := by
  fin_cases o
  · exact o1_typed
  · exact o2_typed
  · exact o3_typed
  · exact o4_typed

/-- The term of every key is a node. -/
theorem KeyExpr.toTerm_typed : ∀ k : KeyExpr, CTyped (edges L) .nil (k.toTerm (L := L)) cNode
  | .node x => nodeConst_typed x
  | .src o => key_typed src_typed (occConst_typed o)
  | .dst o => key_typed dst_typed (occConst_typed o)

omit [LevelOrder L] in
/-- The stored fact of the source of each occurrence is an equation of the package. -/
theorem src_member (o : Fin 4) :
    fact L srcN (occName o) (nodeName (stored o).1) ∈ equations L := by
  fin_cases o
  · exact src1_member
  · exact src2_member
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self)))
  · exact src4_member

omit [LevelOrder L] in
/-- The stored fact of the target of each occurrence is an equation of the package. -/
theorem dst_member (o : Fin 4) :
    fact L dstN (occName o) (nodeName (stored o).2) ∈ equations L := by
  fin_cases o
  · exact dst1_member
  · exact dst2_member
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  · exact dst4_member

/-- **A key runs, by the steps of the package, to the node `KeyExpr.run` gives.** -/
theorem KeyExpr.runs : ∀ k : KeyExpr,
    CReduces (edges L) (k.toTerm (L := L)) (.const (nodeName k.run))
  | .node _ => .refl
  | .src o => .single (.root (fact_step (src_member o)))
  | .dst o => .single (.root (fact_step (dst_member o)))

/-- In the judgment, a key is equal to the node it runs to. -/
theorem KeyExpr.equal : ∀ k : KeyExpr,
    CEqual (edges L) .nil (k.toTerm (L := L)) (.const (nodeName k.run)) cNode
  | .node x => .refl (nodeConst_typed x)
  | .src o => fact_rule (src_member o) src_typed (occConst_typed o) (nodeConst_typed _)
  | .dst o => fact_rule (dst_member o) dst_typed (occConst_typed o) (nodeConst_typed _)

/-- **Every answer the run gives is a typed answer of `hop k`.** -/
theorem answer_typed_of_run {k : KeyExpr} {i : Fin 4} (member : i ∈ runQuery k) :
    CTyped (edges L) .nil (cAnswer cSrc (.const (occName i))) (hop (k.toTerm (L := L))) := by
  have same : (stored i).1 = k.run := mem_runQuery.mp member
  have keyed : CEqual (edges L) .nil (.app cSrc (.const (occName i)))
      (.const (nodeName (stored i).1)) cNode :=
    fact_rule (src_member i) src_typed (occConst_typed i) (nodeConst_typed _)
  rw [same] at keyed
  exact answer_typed package_contains occ_isSet node_isSet src_typed k.toTerm_typed
    (occConst_typed i)
    (keyed.trans k.equal.symm)

/-- The value an answer returns runs to the target of its occurrence. -/
theorem answer_returns (i : Fin 4) :
    CReduces (edges L) (cReturn cDst (cAnswer cSrc (.const (occName i))) : CTm (Head L) 0)
      (.const (nodeName (returned i))) :=
  return_reduces (dst_member i)

end Terms

/-! ## The answers as sets -/

/-- **The set of a bag of answers**: each occurrence paired with the empty set, the proof that
its key matches carrying nothing. -/
noncomputable def answersSet : List (Fin 4) → ZFSet.{u}
  | [] => ∅
  | i :: rest => insert (ZFSet.pair (numeral i.val) ∅) (answersSet rest)

theorem mem_answersSet {l : List (Fin 4)} {z : ZFSet.{u}} :
    z ∈ answersSet l ↔ ∃ i ∈ l, z = ZFSet.pair (numeral i.val) ∅ := by
  induction l with
  | nil => simp [answersSet]
  | cons i rest ih =>
      rw [answersSet, ZFSet.mem_insert_iff, ih]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨i, List.mem_cons_self, rfl⟩
        · exact ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact .inl rfl
        · exact .inr ⟨j, hj, rfl⟩

/-- A member of the fourth numeral is the numeral of an occurrence. -/
theorem exists_occurrence {x : ZFSet.{u}} (member : x ∈ (numeral 4 : ZFSet.{u})) :
    ∃ i : Fin 4, x = numeral i.val := by
  rcases mem_four member with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

/-- The source of each occurrence, read off the trace of `edge@arg1` in the model. -/
theorem src_value (i : Fin 4) :
    traceApp srcValue.{u} (numeral i.val) = numeral (stored i).1.val := by
  rw [src_at i.val i.isLt]
  fin_cases i
  · exact srcFun_of_ne (by decide)
  · exact srcFun_of_ne (by decide)
  · exact srcFun_two
  · exact srcFun_of_ne (by decide)

/-- The target of each occurrence, read off the trace of `edge@arg2` in the model. -/
theorem dst_value (i : Fin 4) :
    traceApp dstValue.{u} (numeral i.val) = numeral (returned i).val := by
  rw [dst_at i.val i.isLt]
  fin_cases i
  · exact dstFun_zero
  · exact dstFun_one
  · exact dstFun_two
  · exact dstFun_three

/-! ## The triangle -/

section Triangle

variable {L : Type} [LevelOrder L] {V : Above L → ZFSet.{u}} {ground : ZFSet.{u}}
  {ν : Nat → Above L} {base : DeclName → ZFSet.{u}}

variable (L) in
/-- A closed term of the package that is a set, with its typing. -/
abbrev TypedSet : Type := { T : CTm (Head L) 0 // CTyped (edges L) .nil T allSets }

/-- **What runs is typed**: the query `hop k` of a key, with the proof that its answers form a
set. -/
def typing (k : KeyExpr) : TypedSet L := ⟨hop k.toTerm, hop_isSet k.toTerm_typed⟩

variable (V ground ν base) in
/-- **What is typed means a set**: the value of a typed term in the set model of the package. -/
noncomputable def meaning (T : TypedSet L) : ZFSet.{u} :=
  ev (chainHead V ground ν) (familyConsts base (decls L) values) T.1 Fin.elim0

/-- **What runs reaches a set**: the bag of answers the run returns, as the set of its
answers. -/
noncomputable def direct (k : KeyExpr) : ZFSet.{u} := answersSet (runQuery k)

/-- The value of a key in the model is the numeral of the node it runs to. -/
theorem key_value (k : KeyExpr) :
    ev (chainHead V ground ν) (familyConsts base (decls L) values) (k.toTerm (L := L))
      Fin.elim0 = numeral k.run.val := by
  have reads := model_reads (L := L) base
  cases k with
  | node x =>
      show familyConsts base (decls L) values (nodeName x) = _
      rw [reads.at (nodeName_declared x)]
      fin_cases x <;> rfl
  | src o =>
      show traceApp (familyConsts base (decls L) values srcN)
        (familyConsts base (decls L) values (occName o)) = _
      rw [reads.at decls_src, reads.at (occName_declared o), values_src]
      have occ : values.{u} (occName o) = numeral o.val := by fin_cases o <;> rfl
      rw [occ, src_value]
      rfl
  | dst o =>
      show traceApp (familyConsts base (decls L) values dstN)
        (familyConsts base (decls L) values (occName o)) = _
      rw [reads.at decls_dst, reads.at (occName_declared o), values_dst]
      have occ : values.{u} (occName o) = numeral o.val := by fin_cases o <;> rfl
      rw [occ, dst_value]
      rfl

/-- **The answers of the typed query, in the sets, are the answers the run returns.** -/
theorem mem_meaning (k : KeyExpr) (z : ZFSet.{u}) :
    z ∈ meaning V ground ν base (typing (L := L) k) ↔
      ∃ i ∈ runQuery k, z = ZFSet.pair (numeral i.val) ∅ := by
  have reads := model_reads (L := L) base
  unfold meaning typing
  rw [mem_query]
  constructor
  · rintro ⟨x, hx, same, rfl⟩
    change x ∈ familyConsts base (decls L) values occN at hx
    change traceApp (familyConsts base (decls L) values srcN) x =
      ev (chainHead V ground ν) (familyConsts base (decls L) values) (k.toTerm (L := L))
        Fin.elim0 at same
    rw [reads.at decls_occ, values_occ] at hx
    obtain ⟨i, rfl⟩ := exists_occurrence hx
    rw [reads.at decls_src, values_src, src_value, key_value] at same
    exact ⟨i, mem_runQuery.mpr (Fin.ext (numeral_injective same)), rfl⟩
  · rintro ⟨i, member, rfl⟩
    refine ⟨numeral i.val, ?_, ?_, rfl⟩
    · show numeral i.val ∈ familyConsts base (decls L) values occN
      rw [reads.at decls_occ, values_occ]
      exact (numeral_mem_iff _ _).mpr i.isLt
    · show traceApp (familyConsts base (decls L) values srcN) (numeral i.val) =
        ev (chainHead V ground ν) (familyConsts base (decls L) values) (k.toTerm (L := L))
          Fin.elim0
      rw [reads.at decls_src, values_src, src_value, key_value, mem_runQuery.mp member]

/-- **The three ways to a set agree**: the value of the typed query in the set model is the set
of the answers the run returns. -/
theorem meaning_typing (k : KeyExpr) :
    meaning V ground ν base (typing (L := L) k) = direct k :=
  ZFSet.ext fun z => (mem_meaning k z).trans mem_answersSet.symm

variable (L V ground ν base) in
/-- **The triangle of the three faces of the query.** -/
noncomputable def queryTriangle : Comparison.{0, 0, u + 1} Closed :=
  triangleOfThree
    (fun k : ULift.{u + 1} KeyExpr => (ULift.up (typing k.down) : ULift.{u + 1} (TypedSet L)))
    (fun T => meaning V ground ν base T.down) (fun k => direct k.down)
    fun k => meaning_typing k.down

/-- **Counts are kept**: the answers of the typed query that return a value are the answers of
the run's bag that return it, one for each stored occurrence. -/
theorem mem_meaning_returning (k : KeyExpr) (v : Fin 3) (z : ZFSet.{u}) :
    (z ∈ meaning V ground ν base (typing (L := L) k) ∧
        traceApp dstValue (first z) = numeral v.val) ↔
      ∃ i ∈ (runQuery k).filter (fun i => returned i = v),
        z = ZFSet.pair (numeral i.val) ∅ := by
  rw [mem_meaning]
  constructor
  · rintro ⟨⟨i, member, rfl⟩, value⟩
    rw [first_pair, dst_value] at value
    exact ⟨i, List.mem_filter.mpr
      ⟨member, decide_eq_true (Fin.ext (numeral_injective value))⟩, rfl⟩
  · rintro ⟨i, member, rfl⟩
    obtain ⟨member, value⟩ := List.mem_filter.mp member
    refine ⟨⟨i, member, rfl⟩, ?_⟩
    rw [first_pair, dst_value, of_decide_eq_true value]

/-- Positive example: **`hop a` returns `b` twice**, through the first and the fourth
occurrence, which are two different answers. -/
theorem hop_a_returns_b_twice :
    (runQuery (.node 0)).filter (fun i => returned i = 1) = [0, 3] ∧
      ZFSet.pair (numeral (0 : Fin 4).val) ∅ ≠
        (ZFSet.pair (numeral (3 : Fin 4).val) ∅ : ZFSet.{u}) :=
  ⟨by decide, fun same => absurd (numeral_injective (ZFSet.pair_inj.mp same).1) (by decide)⟩

variable (L V ground ν base) in
/-- **The triangle is not exact**: `hop a` and `hop (dst o3)` are different programs, and the
target of the third stored edge is `a`, so they have one set of answers. -/
theorem queryTriangle_loses : (queryTriangle L V ground ν base).LosesProgramInformation :=
  triangleOfThree_loses _ _ _ _ (left := ⟨.node 0⟩) (right := ⟨.dst 2⟩)
    (fun same => absurd (congrArg ULift.down same) (by decide))
    (show direct (.node 0) = direct (.dst 2) from rfl)

/-! ## A negative control -/

/-- **The bag read as the set of the values it returns**: one answer kept for each value, the
others with the same value dropped. -/
def onePerValue (l : List (Fin 4)) : List (Fin 4) :=
  l.pwFilter fun i j => returned i ≠ returned j

/-- Negative example: **read as the set of the values returned, the run loses a count, and the
three maps form no triangle.** At `hop a` the first and the fourth answer both return `b`; one
of them is dropped, and the typed query has both. -/
theorem onePerValue_disagrees :
    ¬ ∀ k : KeyExpr, meaning V ground ν base (typing (L := L) k) =
      answersSet (onePerValue (runQuery k)) := by
  intro agree
  have kept : onePerValue (runQuery (.node 0)) = [1, 3] := by decide
  have first_answer : (ZFSet.pair (numeral (0 : Fin 4).val) ∅ : ZFSet.{u}) ∈
      meaning V ground ν base (typing (L := L) (.node 0)) :=
    (mem_meaning _ _).mpr ⟨0, by decide, rfl⟩
  rw [agree, kept, mem_answersSet] at first_answer
  obtain ⟨i, member, same⟩ := first_answer
  have zero : (0 : Nat) = i.val := numeral_injective (ZFSet.pair_inj.mp same).1
  rcases List.mem_cons.mp member with rfl | member
  · exact absurd zero (by decide)
  · rw [List.mem_singleton] at member
    subst member
    exact absurd zero (by decide)

end Triangle

end Mettapedia.Languages.MeTTa.PrimeComparisons.MegalodonHOTG.Query
