import Mettapedia.Machines.ConstructorContext
import Mettapedia.Machines.Cursor.TailSummary
import Mathlib.Tactic

/-!
# Allocation-indexed atom summaries for constructor holes

A child contributes inherited (OR) bits, required (AND) bits, structural
facts guarded by a validity bit, a variable summary, and two closure tests.
Closure tests are made at the parent's arena, using the child's home. A
context thus acts on a *located* summary; a bare closure bit is insufficient.

The aggregate is a product monoid. Head adjustments and the parent's home
are installed only at the end. Fixed siblings can be aggregated at entry;
filling the hole needs two aggregate merges, independent of sibling count.
Bit families are parameters: finite native words instantiate them without
fixing a language's set of properties in the abstract theory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorSummary

open ConstructorContext Cursor.TailSummary

universe u
variable {Bit : Type u}

theorem vars_join_assoc (a b c : Vars) :
    Vars.join (Vars.join a b) c = Vars.join a (Vars.join b c) := by
  cases a <;> cases b <;> cases c <;> simp [Vars.join]
  all_goals split_ifs <;> simp_all

@[ext] structure Aggregate (Bit : Type u) where
  inherited : Bit → Bool
  required : Bit → Bool
  facts : Bit → Bool
  valid : Bool
  closed : Bool
  generation : Bool
  vars : Vars

namespace Aggregate

def unit : Aggregate Bit :=
  ⟨fun _ => false, fun _ => true, fun _ => false, true, true, true, .none⟩

def merge (a b : Aggregate Bit) : Aggregate Bit :=
  ⟨fun i => a.inherited i || b.inherited i,
   fun i => a.required i && b.required i,
   fun i => a.facts i || b.facts i,
   a.valid && b.valid, a.closed && b.closed,
   a.generation && b.generation, Vars.join a.vars b.vars⟩

theorem merge_assoc (a b c : Aggregate Bit) :
    merge (merge a b) c = merge a (merge b c) := by
  ext <;> simp [merge, Bool.or_assoc, Bool.and_assoc, vars_join_assoc]

@[simp] theorem unit_merge (a : Aggregate Bit) : merge unit a = a := by
  ext <;> simp [merge, unit, Vars.join]

@[simp] theorem merge_unit (a : Aggregate Bit) : merge a unit = a := by
  ext <;> simp [merge, unit, Vars.join_none]

def fold (xs : List (Aggregate Bit)) : Aggregate Bit := xs.foldr merge unit

theorem fold_append (xs ys : List (Aggregate Bit)) :
    fold (xs ++ ys) = merge (fold xs) (fold ys) := by
  induction xs with
  | nil => simp [fold]
  | cons x xs ih =>
      simp only [List.cons_append, fold, List.foldr_cons] at *
      rw [ih, merge_assoc]

end Aggregate

/-- Summary of a completed atom. `generation` is the stored additional bit;
`closed || (valid && generation)` is the predicate used when admitting its generation. -/
structure Summary (Bit : Type u) where
  home : Home
  aggregate : Aggregate Bit

/-- The constructor's fixed allocation and fixed head-specific adjustments.
The runtime must identify the constructor head before choosing this plan. -/
structure Label (Bit : Type u) where
  arena : Nat
  older : Option Nat
  headAdds : Bit → Bool
  headForbids : Bit → Bool

def sameArena (here : Nat) : Home → Bool
  | .global => true
  | .arena there => there == here

def generationAdmits (label : Label Bit) (child : Summary Bit) : Bool :=
  match child.home with
  | .global => child.aggregate.closed
  | .arena there =>
      (there == label.arena || label.older == some there) &&
        (child.aggregate.closed || (child.aggregate.valid && child.aggregate.generation))

/-- Normalize one child's allocation-dependent contribution for this parent.
The ordinary structural facts exclude the separate generation/slack bits. -/
def contribution (label : Label Bit) (child : Summary Bit) : Aggregate Bit :=
  { child.aggregate with
    closed := child.aggregate.closed && sameArena label.arena child.home
    generation := generationAdmits label child }

/-- Native head adjustments and validity masking happen after the child fold. -/
def finish (label : Label Bit) (a : Aggregate Bit) : Summary Bit :=
  ⟨.arena label.arena,
   { a with
     inherited := fun i => a.inherited i || label.headAdds i
     required := fun i => a.required i && !label.headForbids i
     facts := fun i => a.valid && a.facts i
     generation := label.older.isSome && a.generation && !a.closed && a.valid }⟩

def combine (label : Label Bit) (children : List (Summary Bit)) : Summary Bit :=
  finish label (Aggregate.fold (children.map (contribution label)))

/-- Fixed siblings are scanned once while entering the context. -/
structure Prepared (Bit : Type u) where
  label : Label Bit
  left : Aggregate Bit
  right : Aggregate Bit

def prepare (frame : Frame (Label Bit) (Summary Bit)) : Prepared Bit :=
  ⟨frame.label, Aggregate.fold (frame.before.map (contribution frame.label)),
    Aggregate.fold (frame.after.map (contribution frame.label))⟩

/-- Two merges and one final adjustment; no traversal of the fixed siblings. -/
def complete (prepared : Prepared Bit) (hole : Summary Bit) : Summary Bit :=
  finish prepared.label (Aggregate.merge prepared.left
    (Aggregate.merge (contribution prepared.label hole) prepared.right))

theorem complete_eq_frame (frame : Frame (Label Bit) (Summary Bit))
    (hole : Summary Bit) :
    complete (prepare frame) hole = frame.apply combine hole := by
  simp only [complete, prepare, Frame.apply, combine, List.map_append,
    List.map_cons, Aggregate.fold_append]
  rfl

/-- A located recursive value model, providing an actual summary algebra. -/
inductive Term (Bit : Type u)
  | resident (summary : Summary Bit)
  | node (label : Label Bit) (children : List (Term Bit))

def summarize : Term Bit → Summary Bit
  | .resident summary => summary
  | .node label children => combine label (children.map summarize)

def algebra : SummaryAlgebra (Label Bit) (Term Bit) (Summary Bit) where
  build := Term.node
  observe := summarize
  combine := combine
  build_observe := by intros; simp [summarize]

/-- The precomputed per-cell action agrees with the full recursive fold. -/
theorem prepared_summary_exact (frame : Frame (Label Bit) (Term Bit))
    (value : Term Bit) :
    complete (prepare (frame.map summarize)) (summarize value) =
      summarize (frame.apply Term.node value) := by
  rw [complete_eq_frame]
  exact ((algebra (Bit := Bit)).observe_frame frame value).symm

/-- Every entry of the backward summary pass is the exact summary of the
corresponding suffix value, with its own allocation context. -/
theorem all_cells_exact (frames : List (Frame (Label Bit) (Term Bit)))
    (value : Term Bit) (index : Nat) (within : index ≤ frames.length) :
    ((algebra (Bit := Bit)).summaries frames value)[index]? =
      some (summarize (plug Term.node (frames.drop index) value)) :=
  (algebra (Bit := Bit)).summaries_at frames value index within

/-! Arena renaming preserves the actual allocation-dependent predicates only
when distinct arenas stay distinct and the older link moves with its label.
These laws transport a justified summary; they do not validate heap epochs,
interning tables, scalar caches, or ownership of opaque resources. -/

def Summary.mapArena (arena : Nat → Nat) (summary : Summary Bit) : Summary Bit :=
  ⟨summary.home.map arena, summary.aggregate⟩

def Label.mapArena (arena : Nat → Nat) (label : Label Bit) : Label Bit :=
  { label with arena := arena label.arena, older := label.older.map arena }

def Prepared.mapArena (arena : Nat → Nat) (prepared : Prepared Bit) : Prepared Bit :=
  { prepared with label := prepared.label.mapArena arena }

theorem Summary.mapArena_id (summary : Summary Bit) : summary.mapArena id = summary := by
  cases summary
  simp only [Summary.mapArena, Home.map_id]

theorem Summary.mapArena_comp (first second : Nat → Nat) (summary : Summary Bit) :
    (summary.mapArena first).mapArena second = summary.mapArena (second ∘ first) := by
  simp only [Summary.mapArena, Home.map_comp]

theorem Label.mapArena_id (label : Label Bit) : label.mapArena id = label := by
  cases label
  simp only [Label.mapArena, id_eq, Option.map_id]

theorem Label.mapArena_comp (first second : Nat → Nat) (label : Label Bit) :
    (label.mapArena first).mapArena second = label.mapArena (second ∘ first) := by
  simp only [Label.mapArena, Option.map_map, Function.comp_def]

private theorem arena_beq_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (one two : Nat) : (arena one == arena two) = (one == two) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, injective.eq_iff]

private theorem older_beq_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (one two : Option Nat) : (one.map arena == two.map arena) = (one == two) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Option.map_inj_right (f := arena) (fun _ _ equal => injective equal)]

theorem sameArena_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (here : Nat) (home : Home) :
    sameArena (arena here) (home.map arena) = sameArena here home := by
  cases home with
  | global => rfl
  | arena there => exact arena_beq_map arena injective there here

theorem generationAdmits_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (label : Label Bit) (child : Summary Bit) :
    generationAdmits (label.mapArena arena) (child.mapArena arena) =
      generationAdmits label child := by
  rcases child with ⟨home, aggregate⟩
  cases home with
  | global => rfl
  | arena there =>
    have older := older_beq_map arena injective label.older (some there)
    simpa only [generationAdmits, Label.mapArena, Summary.mapArena, Home.map,
      arena_beq_map arena injective, Option.map_some] using
      congrArg (fun same => (there == label.arena || same) &&
        (aggregate.closed || (aggregate.valid && aggregate.generation))) older

theorem contribution_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (label : Label Bit) (child : Summary Bit) :
    contribution (label.mapArena arena) (child.mapArena arena) = contribution label child := by
  change { child.aggregate with
    closed := child.aggregate.closed && sameArena (arena label.arena) (child.home.map arena)
    generation := generationAdmits (label.mapArena arena) (child.mapArena arena) } = _
  rw [sameArena_map arena injective, generationAdmits_map arena injective]
  rfl

theorem finish_map (arena : Nat → Nat) (label : Label Bit) (aggregate : Aggregate Bit) :
    finish (label.mapArena arena) aggregate = (finish label aggregate).mapArena arena := by
  simp only [finish, Label.mapArena, Summary.mapArena, Home.map, Option.isSome_map]

theorem combine_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (label : Label Bit) (children : List (Summary Bit)) :
    combine (label.mapArena arena) (children.map (Summary.mapArena arena)) =
      (combine label children).mapArena arena := by
  simp only [combine, List.map_map, Function.comp_def, contribution_map arena injective]
  exact finish_map arena label _

/-- A prepared constructor keeps its fixed aggregates and its constant amount
of completion work while its arena label and the hole move together. -/
theorem complete_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (prepared : Prepared Bit) (hole : Summary Bit) :
    complete (prepared.mapArena arena) (hole.mapArena arena) =
      (complete prepared hole).mapArena arena := by
  simp only [complete, Prepared.mapArena, contribution_map arena injective]
  exact finish_map arena prepared.label _

namespace Controls

def plain (arena : Nat) (older : Option Nat := none) : Label Unit :=
  ⟨arena, older, fun _ => false, fun _ => false⟩

def leaf (arena : Nat) : Summary Unit := ⟨.arena arena, Aggregate.unit⟩

/-- Equal closure bits at different homes cannot be substituted for one
another in a parent closure test. -/
theorem child_home_is_necessary :
    (leaf 1).aggregate.closed = (leaf 2).aggregate.closed ∧
    (combine (plain 1) [leaf 1]).aggregate.closed = true ∧
    (combine (plain 1) [leaf 2]).aggregate.closed = false := by decide

/-- Linking the older arena admits a child without claiming same-arena closure. -/
theorem older_arena_is_distinct :
    (combine (plain 1 (some 2)) [leaf 2]).aggregate.closed = false ∧
    (combine (plain 1 (some 2)) [leaf 2]).aggregate.generation = true := by decide

/-- A generation bit without valid structural facts is not evidence of
closure, matching the native generation-admission predicate. -/
theorem invalid_generation_is_not_admitted :
    let child : Summary Unit := ⟨.arena 2,
      { Aggregate.unit with closed := false, valid := false }⟩
    generationAdmits (plain 1 (some 2)) child = false := by decide

/-- Facts from an invalid child do not become a valid parent cache. -/
theorem unknown_facts_stay_unknown :
    let child : Summary Unit := ⟨.global,
      { Aggregate.unit with facts := fun _ => true, valid := false }⟩
    (combine (plain 1) [child]).aggregate.valid = false ∧
    (combine (plain 1) [child]).aggregate.facts () = false := by decide

/-- The frame's head adjustment cannot be omitted merely because all
children share the same ordinary bit fold. -/
theorem head_adjustment_is_necessary :
    let special : Label Unit := { plain 1 with headAdds := fun _ => true }
    (combine special [leaf 1]).aggregate.inherited () = true ∧
    (combine (plain 1) [leaf 1]).aggregate.inherited () = false := by decide

/-- Ignoring the hole's variable summary loses a real distinction. -/
theorem hole_vars_are_necessary :
    let child : Summary Unit := ⟨.arena 1,
      { Aggregate.unit with vars := .one 7 }⟩
    (combine (plain 1) [child]).aggregate.vars = .one 7 ∧
    (combine (plain 1) []).aggregate.vars = .none := by decide

/-- Moving both distinct domains and the older edge preserves the two
different native closure predicates. -/
theorem mapped_older_edge_preserves_reuse :
    (combine ((plain 17 (some 29)).mapArena (· + 1000))
      [(leaf 29).mapArena (· + 1000)]).aggregate.closed = false ∧
    (combine ((plain 17 (some 29)).mapArena (· + 1000))
      [(leaf 29).mapArena (· + 1000)]).aggregate.generation = true := by decide

/-- Merging two allocation domains invents a same-arena reuse decision even
though the child's ordinary property bits did not change. -/
theorem coalesced_arenas_invent_reuse :
    (contribution (plain 17) (leaf 29)).closed = false ∧
    (contribution ((plain 17).mapArena (fun _ => 1000))
      ((leaf 29).mapArena (fun _ => 1000))).closed = true := by decide

/-- Omitting the transported older link loses a legitimate generation reuse. -/
theorem missing_older_edge_loses_reuse :
    generationAdmits (plain 17 (some 29)) (leaf 29) = true ∧
    generationAdmits (plain 1017) ((leaf 29).mapArena (· + 1000)) = false := by decide

/-- Moving the hole while keeping its old constructor label also changes the
allocation-dependent decision. -/
theorem unmoved_label_loses_reuse :
    (contribution (plain 17) (leaf 17)).closed = true ∧
    (contribution (plain 17) ((leaf 17).mapArena (· + 1000))).closed = false := by decide

end Controls

end Mettapedia.Machines.ConstructorSummary
