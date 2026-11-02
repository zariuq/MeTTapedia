import Mettapedia.Machines.NamedStoreModel

/-!
# Store-aware navigation and a zipper over named shapes

The reader follows a requested path by exposing only the current named body.
It never invokes whole-term expansion. Its independent reference walks a
fully expanded term; valid recursive shape stores give exactly the same
selected subterm, including invalid-path refusals. Zipper frames retain the
sibling and restore the same denotation, even when the parent had a name.

The checked oracle uses the constructed recursive body model. A native reader
must realize its exposure contract and preserve frame lifetimes separately.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NamedShapeCursor

open ShapeStore NamedShapeGraph NamedStoreModel

variable {α Name : Type}

def expose (heap : Heap α Name) : Expr α Name → Option (Expr α Name)
  | .ref n => heap n
  | e => some e

def step (heap : Heap α Name) (right : Bool) (e : Expr α Name) : Option (Expr α Name) :=
  (expose heap e).bind fun head => match head with
    | .node l r => some (if right then r else l)
    | _ => none

def seek (heap : Heap α Name) : List Bool → Expr α Name → Option (Expr α Name)
  | [], e => some e
  | side :: rest, e => (step heap side e).bind (seek heap rest)

def subterm : List Bool → Tm α → Option (Tm α)
  | [], t => some t
  | _ :: _, .atom _ => none
  | side :: rest, .node l r => subterm rest (if side then r else l)

theorem quoteBody_not_ref (name : Tm α → Name) (policy : Policy α)
    (t : Tm α) (n : Name) : quoteBody name policy t ≠ .ref n := by
  cases t <;> simp [quoteBody]

theorem expose_model (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (e : Expr α Name) (t : Tm α) (valid : e.eval read = some t) :
    ∃ head, expose (bodies read name policy) e = some head ∧
      (∀ n, head ≠ .ref n) ∧ head.eval read = some t := by
  cases e with
  | atom a => exact ⟨.atom a, rfl, (by intro n h; cases h), valid⟩
  | node l r => exact ⟨.node l r, rfl, (by intro n h; cases h), valid⟩
  | ref n =>
      exact ⟨quoteBody name policy t, by simp [expose, bodies, show read n = some t from valid],
        quoteBody_not_ref name policy t, quoteBody_eval name read roundtrip policy t⟩

/-- The computed focus agrees with tree navigation; no full expansion occurs
in `seek`. Evaluating the focus here specifies the observation to compare. -/
theorem seek_refines (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (path : List Bool) (e : Expr α Name) (t : Tm α) (valid : e.eval read = some t) :
    (seek (bodies read name policy) path e).bind (Expr.eval read) = subterm path t := by
  induction path generalizing e t with
  | nil => simpa [seek, subterm] using valid
  | cons side rest ih =>
      obtain ⟨head, exposed, notRef, meaning⟩ := expose_model read name roundtrip policy e t valid
      cases head with
      | ref n => exact False.elim (notRef n rfl)
      | atom a =>
          have equal : Tm.atom a = t := Option.some.inj meaning
          subst t
          simp [seek, step, exposed, subterm]
      | node l r =>
          obtain ⟨tl, hl, tail⟩ := Option.bind_eq_some_iff.mp meaning
          obtain ⟨tr, hr, equal⟩ := Option.map_eq_some_iff.mp tail
          subst t
          cases side <;> simp [seek, step, exposed, subterm, ih l tl hl, ih r tr hr]

theorem seek_append (heap : Heap α Name) (first second : List Bool) (e : Expr α Name) :
    seek heap (first ++ second) e = (seek heap first e).bind (seek heap second) := by
  induction first generalizing e with
  | nil => rfl
  | cons side rest ih => simp [seek, ih, Option.bind_assoc]

structure Frame (α Name : Type) where
  right : Bool
  sibling : Expr α Name
  deriving DecidableEq

def Frame.plug (frame : Frame α Name) (focus : Expr α Name) : Expr α Name :=
  if frame.right then .node frame.sibling focus else .node focus frame.sibling

def rebuild : List (Frame α Name) → Expr α Name → Expr α Name
  | [], e => e
  | frame :: rest, e => rebuild rest (frame.plug e)

structure Cursor (α Name : Type) where
  focus : Expr α Name
  context : List (Frame α Name)
  deriving DecidableEq

def down (heap : Heap α Name) (right : Bool) (cursor : Cursor α Name) : Option (Cursor α Name) :=
  (expose heap cursor.focus).bind fun head => match head with
    | .node l r => some
        ⟨if right then r else l, ⟨right, if right then l else r⟩ :: cursor.context⟩
    | _ => none

def up (cursor : Cursor α Name) : Option (Cursor α Name) :=
  match cursor.context with
  | [] => none
  | frame :: rest => some ⟨frame.plug cursor.focus, rest⟩

theorem rebuild_eval_congr (read : Name → Option (Tm α)) (frames : List (Frame α Name))
    (a b : Expr α Name) (same : a.eval read = b.eval read) :
    (rebuild frames a).eval read = (rebuild frames b).eval read := by
  induction frames generalizing a b with
  | nil => exact same
  | cons frame rest ih =>
      apply ih
      cases frame with
      | mk right sibling => cases right <;> simp [Frame.plug, Expr.eval, same]

theorem up_preserves_rebuild (before after : Cursor α Name) (moved : up before = some after) :
    rebuild after.context after.focus = rebuild before.context before.focus := by
  cases before with
  | mk focus frames =>
      cases frames with
      | nil => simp [up] at moved
      | cons frame rest =>
          have equal : (⟨frame.plug focus, rest⟩ : Cursor α Name) = after := Option.some.inj moved
          subst after
          rfl

theorem down_preserves_meaning (read : Name → Option (Tm α)) (name : Tm α → Name)
    (roundtrip : ∀ t, read (name t) = some t) (policy : Policy α)
    (before after : Cursor α Name) (right : Bool) (t : Tm α)
    (valid : before.focus.eval read = some t)
    (moved : down (bodies read name policy) right before = some after) :
    (rebuild after.context after.focus).eval read =
      (rebuild before.context before.focus).eval read := by
  obtain ⟨head, exposed, _, meaning⟩ := expose_model read name roundtrip policy before.focus t valid
  unfold down at moved
  rw [exposed] at moved
  cases head with
  | atom a => simp at moved
  | ref n => simp at moved
  | node l r =>
      cases right <;>
        simp only [Option.bind_some, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at moved
      all_goals subst after
      all_goals apply rebuild_eval_congr read before.context
      all_goals exact meaning.trans valid.symm

namespace Controls

open NamedShapeGraph.Controls (heap)

def root : Expr String (Bool × Nat) := .ref (true, 1)

/-- Both branches of a shared graph select the same name, but remain two paths. -/
example : seek heap [false] root = some (.ref (false, 0)) ∧
    seek heap [true] root = some (.ref (false, 0)) := by decide

example : seek heap [false, true] root = none := by decide
example : seek heap [false] (.ref (true, 9)) = none := by decide

/-- Moving up restores an inline constructor, not necessarily the old raw name. -/
theorem up_after_down_need_not_restore_encoding :
    ((down heap false ⟨root, []⟩).bind up).map Cursor.focus =
      some (.node (.ref (false, 0)) (.ref (false, 0))) ∧
    ((down heap false ⟨root, []⟩).bind up).map Cursor.focus ≠ some root := by decide

end Controls

#print axioms seek_refines
#print axioms seek_append
#print axioms down_preserves_meaning
#print axioms up_preserves_rebuild

end Mettapedia.Machines.NamedShapeCursor
