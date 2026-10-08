import Mettapedia.CategoryTheory.GroundPathRelativePushout
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators

/-!
# Sorted closed constructors and linear frame contexts

Every frame retains its actual constructor, selected argument position and
all supplied sibling terms. A context is a typed path of such frames, acting
by constructor filling. Closed terms remain constructor trees, including the
distinguished cut when an interactive signature supplies one; they are not
replaced by opaque class identifiers.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath
open scoped BigOperators

universe u v

-- The two carrier universes are independent, as in a bundled category.
set_option linter.checkUnivs false in
structure Signature where
  Srt : Type u
  Constructor : Type v
  arity : Constructor → Nat
  input : (constructor : Constructor) → Fin (arity constructor) → Srt
  output : Constructor → Srt

inductive Term (signature : Signature.{u,v}) : signature.Srt → Type (max u v) where
  | node (constructor : signature.Constructor)
      (arguments : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)) :
      Term signature (signature.output constructor)

/-- No value is stored at the selected position; every stored sibling is an
actual closed constructor term of the independently declared argument sort. -/
inductive Frame (signature : Signature.{u,v}) : signature.Srt → signature.Srt → Type (max u v) where
  | slot (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
      (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
        Term signature (signature.input constructor other)) :
      Frame signature (signature.input constructor position) (signature.output constructor)

namespace Frame

variable {signature : Signature.{u,v}}

def fill {source target : signature.Srt} (frame : Frame signature source target)
    (supplied : Term signature source) : Term signature target := by
  classical
  cases frame with
  | slot constructor position siblings =>
    exact .node constructor (fun other =>
      if same : other = position then same.symm ▸ supplied else siblings other same)

@[simp]
theorem fill_slot (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
    (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
      Term signature (signature.input constructor other))
    (supplied : Term signature (signature.input constructor position)) :
    fill (.slot constructor position siblings) supplied = .node constructor
      (fun other => if same : other = position then same.symm ▸ supplied else siblings other same) := rfl

end Frame

instance frameQuiver (signature : Signature.{u,v}) : Quiver.{max u v} signature.Srt where
  Hom := Frame signature

def action (signature : Signature.{u,v}) : Action signature.Srt where
  Value := Term signature
  frame := Frame.fill

abbrev Context (signature : Signature.{u,v}) (source target : signature.Srt) :=
  @Quiver.Path signature.Srt (frameQuiver signature) source target

abbrev ContextObject (signature : Signature.{u,v}) := Object (action signature)

def contextArrow (signature : Signature.{u,v}) {source target : signature.Srt}
    (context : Context signature source target) :
    (.interface source : ContextObject signature) ⟶ .interface target :=
  Mettapedia.CategoryTheory.GroundPath.contextArrow (action signature) context

def termArrow (signature : Signature.{u,v}) {target : signature.Srt}
    (term : Term signature target) : (.origin : ContextObject signature) ⟶ .interface target :=
  valueArrow (action signature) term

theorem termArrow_comp (signature : Signature.{u,v}) {source target : signature.Srt}
    (term : Term signature source) (context : Context signature source target) :
    termArrow signature term ≫ contextArrow signature context =
      termArrow signature ((action signature).path context term) := rfl

theorem hasRelativePushouts (signature : Signature.{u,v}) {first second : signature.Srt}
    (firstTerm : Term signature first) (secondTerm : Term signature second) :
    Mettapedia.GSLT.RelativePushout.HasRelativePushouts
      (termArrow signature firstTerm) (termArrow signature secondTerm) :=
  ground_hasRelativePushouts (action signature) firstTerm secondTerm

/-- A term with an explicit hole and supplied closed sibling subtrees. -/
inductive ContextSyntax (signature : Signature.{u,v}) (holeSort : signature.Srt) :
    signature.Srt → Type (max u v) where
  | hole : ContextSyntax signature holeSort holeSort
  | closed {sort : signature.Srt} (term : Term signature sort) : ContextSyntax signature holeSort sort
  | node (constructor : signature.Constructor)
      (arguments : (position : Fin (signature.arity constructor)) →
        ContextSyntax signature holeSort (signature.input constructor position)) :
      ContextSyntax signature holeSort (signature.output constructor)

namespace ContextSyntax

variable {signature : Signature.{u,v}} {holeSort : signature.Srt}

def holeCount : {sort : signature.Srt} → ContextSyntax signature holeSort sort → Nat
  | _, .hole => 1
  | _, .closed _ => 0
  | _, .node _ arguments => ∑ position, holeCount (arguments position)

def fill (supplied : Term signature holeSort) : {sort : signature.Srt} →
    ContextSyntax signature holeSort sort → Term signature sort
  | _, .hole => supplied
  | _, .closed term => term
  | _, .node constructor arguments => .node constructor (fun position => fill supplied (arguments position))

def wrap {source target : signature.Srt} (frame : Frame signature source target)
    (inner : ContextSyntax signature holeSort source) : ContextSyntax signature holeSort target := by
  classical
  cases frame with
  | slot constructor position siblings =>
    exact .node constructor (fun other =>
      if same : other = position then same.symm ▸ inner else .closed (siblings other same))

theorem holeCount_wrap {source target : signature.Srt} (frame : Frame signature source target)
    (inner : ContextSyntax signature holeSort source) :
    holeCount (wrap frame inner) = holeCount inner := by
  classical
  cases frame with
  | slot constructor position siblings =>
    simp only [wrap, holeCount]
    have counted : (fun other => holeCount (if same : other = position then same.symm ▸ inner
        else closed (siblings other same))) = fun other => if other = position then holeCount inner else 0 := by
      funext other
      split_ifs with same
      · subst other; rfl
      · rfl
    rw [counted]
    simpa only [Finset.mem_univ, if_true] using
      Finset.sum_ite_eq' Finset.univ position (fun _ => holeCount inner)

theorem fill_wrap {source target : signature.Srt} (frame : Frame signature source target)
    (inner : ContextSyntax signature holeSort source) (supplied : Term signature holeSort) :
    fill supplied (wrap frame inner) = Frame.fill frame (fill supplied inner) := by
  classical
  cases frame with
  | slot constructor position siblings =>
    simp only [wrap, fill, Frame.fill]
    congr 1
    funext other
    split_ifs with same
    · subst other; rfl
    · rfl

end ContextSyntax

def readContext (signature : Signature.{u,v}) {source target : signature.Srt}
    (context : Context signature source target) : ContextSyntax signature source target :=
  @Quiver.Path.rec signature.Srt (frameQuiver signature) source
    (fun target _ => ContextSyntax signature source target) .hole
    (fun _ frame inductionHypothesis => ContextSyntax.wrap frame inductionHypothesis) target context

theorem readContext_holeCount (signature : Signature.{u,v}) {source target : signature.Srt}
    (context : Context signature source target) : (readContext signature context).holeCount = 1 := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change (ContextSyntax.wrap frame (readContext signature previous)).holeCount = 1
    rw [ContextSyntax.holeCount_wrap, inductionHypothesis]

theorem readContext_fill (signature : Signature.{u,v}) {source target : signature.Srt}
    (context : Context signature source target) (supplied : Term signature source) :
    (readContext signature context).fill supplied = (action signature).path context supplied := by
  induction context with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    change (ContextSyntax.wrap frame (readContext signature previous)).fill supplied =
      Frame.fill frame ((action signature).path previous supplied)
    rw [ContextSyntax.fill_wrap, inductionHypothesis]

end Mettapedia.OSLF.SortedConstructors
