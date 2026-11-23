import Mettapedia.Machines.Specialization.PathJoin
import Mathlib.Data.List.Nodup

/-! # Proof-relevant composition of finite supplied relations

Each relation argument is an ordered finite provider. Its receipt type can
carry an occurrence identity, a proof, or both. The result retains both
selected rows. The prepared two-read transform and direct enumeration
agree as lists, including equal receipts occurring at different positions. -/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization.RelationComposition

structure Row (Key Evidence : Type) where
  source : Key
  target : Key
  evidence : Evidence
  deriving DecidableEq, Repr

variable {Key Evidence : Type} [DecidableEq Key]

abbrev Relation (Key Evidence : Type) := List (Row Key Evidence)
abbrev Witness (Key Evidence : Type) := Row Key Evidence × Row Key Evidence

def compose (left right : Relation Key Evidence) (source target : Key) : List (Witness Key Evidence) :=
  (left.filter fun row => decide (row.source = source)).flatMap fun first =>
    (right.filter fun second => decide (second.source = first.target ∧ second.target = target)).map (first, ·)

def keys : PathJoin.EdgeKeys Key (Row Key Evidence) := ⟨Row.source, Row.target⟩

private def pair : List (Row Key Evidence) → List (Witness Key Evidence)
  | [first, second] => [(first, second)]
  | _ => []

def prepared (tables : PathJoin.Tables Key (Row Key Evidence)) (left right : Relation Key Evidence)
    (source target : Key) : List (Witness Key Evidence) :=
  let finish := fun key => decide (key = target)
  let plan := PathJoin.prepare keys tables finish [left, right]
  (PathJoin.execute keys tables finish plan.1 source).flatMap pair

theorem prepared_eq_compose (tables : PathJoin.Tables Key (Row Key Evidence)) (left right : Relation Key Evidence)
    (source target : Key) : prepared tables left right source target = compose left right source target := by
  simp only [prepared]
  rw [(PathJoin.prepare_correct keys tables (fun key => decide (key = target)) [left, right]).2 source]
  simp only [PathJoin.reference, List.map_cons, List.map_nil, PathJoin.paths, keys,
    compose, List.flatMap_assoc]
  apply List.flatMap_congr
  intro first _
  simp only [List.flatMap_map, List.map_flatMap, List.flatMap_assoc]
  induction right with
  | nil => rfl
  | cons second rest ih =>
    by_cases meets : second.source = first.target <;> by_cases ends : second.target = target <;>
      simpa [meets, ends, pair] using ih

theorem mem_compose (left right : Relation Key Evidence) (source target : Key) (first second : Row Key Evidence) :
    (first, second) ∈ compose left right source target ↔
      first ∈ left ∧ second ∈ right ∧ first.source = source ∧ second.source = first.target ∧ second.target = target := by
  simp [compose, List.mem_flatMap, List.mem_map, List.mem_filter]
  grind

/-- Named providers and composition form a first-class relation language.
A derived relation can supply either premise of another transform. -/
inductive Expr (Name : Type) where
  | base (name : Name)
  | chain (left right : Expr Name)
  deriving DecidableEq, Repr

inductive Proof (Key Evidence : Type) where
  | leaf (receipt : Evidence)
  | via (middle : Key) (left right : Proof Key Evidence)
  deriving DecidableEq, Repr

variable {Name : Type} (bank : Name → Relation Key Evidence)

def liftRow (r : Row Key Evidence) : Row Key (Proof Key Evidence) :=
  ⟨r.source, r.target, .leaf r.evidence⟩

def link (l r : Row Key (Proof Key Evidence)) : Row Key (Proof Key Evidence) :=
  ⟨l.source, r.target, .via l.target l.evidence r.evidence⟩

def denote : Expr Name → Relation Key (Proof Key Evidence)
  | .base name => (bank name).map liftRow
  | .chain a b =>
    let right := denote b
    (denote a).flatMap fun l => (right.filter fun r => decide (r.source = l.target)).map (link l)

def indexed (tables : PathJoin.Tables Key (Row Key (Proof Key Evidence))) :
    Expr Name → Relation Key (Proof Key Evidence)
  | .base name => (bank name).map liftRow
  | .chain a b =>
    let index := (PathJoin.buildWhere tables Row.source (fun _ => true) (indexed tables b)).1
    (indexed tables a).flatMap fun l => (tables.read index l.target).map (link l)

theorem indexed_exact (tables : PathJoin.Tables Key (Row Key (Proof Key Evidence))) (expr : Expr Name) :
    indexed bank tables expr = denote bank expr := by
  induction expr with
  | base => rfl
  | chain a b ha hb =>
    simp only [indexed, denote, ha, hb, PathJoin.buildWhere_exact, Bool.and_true]

/-- A row in the closure is justified by an input occurrence or a firing
of the two-read rule producing the indicated relation expression. -/
inductive Holds : Expr Name → Row Key (Proof Key Evidence) → Prop where
  | fact (name : Name) (r : Row Key Evidence) (stored : r ∈ bank name) :
    Holds (.base name) (liftRow r)
  | fire {a b : Expr Name} {l r : Row Key (Proof Key Evidence)} :
    Holds a l → Holds b r → r.source = l.target → Holds (.chain a b) (link l r)

theorem mem_iff_fires (expr : Expr Name) (row : Row Key (Proof Key Evidence)) :
    row ∈ denote bank expr ↔ Holds bank expr row := by
  induction expr generalizing row with
  | base name =>
    constructor
    · intro member
      obtain ⟨r, h, rfl⟩ := List.mem_map.mp member
      exact .fact name r h
    · intro h
      cases h with
      | fact _ r stored => exact List.mem_map.mpr ⟨r, stored, rfl⟩
  | chain a b ha hb =>
    constructor
    · intro member
      obtain ⟨l, hl, rights⟩ := List.mem_flatMap.mp member
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp rights
      obtain ⟨present, same⟩ := List.mem_filter.mp hr
      exact .fire ((ha l).mp hl) ((hb r).mp present) (of_decide_eq_true same)
    · intro h
      cases h with
      | @fire _ _ l r left right same =>
        exact List.mem_flatMap.mpr ⟨l, (ha l).mpr left, List.mem_map.mpr
          ⟨r, List.mem_filter.mpr ⟨(hb r).mpr right, decide_eq_true same⟩, rfl⟩⟩

omit [DecidableEq Key] in
/-- The middle is present in the proof tree. Together with the endpoints
it reconstructs both input rows of any successful join. -/
private theorem link_injective_on {l r l' r' : Row Key (Proof Key Evidence)}
    (aligned : r.source = l.target) (aligned' : r'.source = l'.target)
    (same : link l r = link l' r') : l = l' ∧ r = r' := by
  cases l; cases r; cases l'; cases r'
  simp_all [link]

theorem denote_nodup (distinct : ∀ name, (bank name).Nodup) (expr : Expr Name) :
    (denote bank expr).Nodup := by
  induction expr with
  | base name =>
    apply (distinct name).map
    intro l r eq
    cases l; cases r
    simpa [liftRow] using eq
  | chain a b left right =>
    apply List.nodup_flatMap.mpr
    constructor
    · intro l _
      apply List.Nodup.map_on _ (right.filter _)
      intro r hr r' hr' same
      exact (link_injective_on (of_decide_eq_true (List.mem_filter.mp hr).2)
        (of_decide_eq_true (List.mem_filter.mp hr').2) same).2
    · apply left.imp
      intro l l' different
      apply List.disjoint_left.mpr
      intro joined inside other
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp inside
      obtain ⟨r', hr', same⟩ := List.mem_map.mp other
      exact different (link_injective_on (of_decide_eq_true (List.mem_filter.mp hr).2)
        (of_decide_eq_true (List.mem_filter.mp hr').2) same.symm).1

namespace Controls

private def transport : String → Relation String String
  | "rail" => [⟨"east", "hub", "ticket"⟩, ⟨"east", "hub", "ticket"⟩]
  | "ferry" => [⟨"hub", "west", "crossing"⟩]
  | "bus" => [⟨"west", "pier", "transfer"⟩]
  | _ => []

private def trip : Expr String := .chain (.chain (.base "rail") (.base "ferry")) (.base "bus")

theorem a_composite_argument_keeps_equal_ticket_occurrences :
    let proof : Proof String String := .via "west" (.via "hub" (.leaf "ticket") (.leaf "crossing")) (.leaf "transfer")
    indexed transport PathJoin.functional trip = [⟨"east", "pier", proof⟩, ⟨"east", "pier", proof⟩] := by
  rw [indexed_exact]
  decide +kernel

theorem a_connection_in_the_opposite_direction_has_no_proof :
    indexed transport PathJoin.functional (.chain (.base "ferry") (.base "rail")) = [] := by
  rw [indexed_exact]
  decide +kernel

end Controls

end Mettapedia.Machines.Specialization.RelationComposition
