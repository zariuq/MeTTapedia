import Mettapedia.OSLF.Syntax.SortedCommutativeValues
import Mettapedia.CategoryTheory.MixedResidueRelativePushout

/-!
# Genuine sorted frames acting on independently formed equation classes

Each frame retains the actual free constructor, selected argument position and
all child equation classes at their declared sorts. Reading the complete head
and selected coordinate earns frame cancellation. Parallel cancellation is
earned from the separate inventory theorem, yielding actual mixed-context
RPOs on these closed equation classes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors

universe u v

variable (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop)

inductive Frame : signature.Srt → signature.Srt → Type (max u v) where
  | slot (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
      (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
        Class signature Parallel (signature.input constructor other)) :
      Frame (signature.input constructor position) (signature.output constructor)

variable {signature Parallel}

namespace Frame

def insert (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
    (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
      Class signature Parallel (signature.input constructor other))
    (supplied : Class signature Parallel (signature.input constructor position)) :
    (other : Fin (signature.arity constructor)) → Class signature Parallel (signature.input constructor other) :=
  fun other => if same : other = position then same.symm ▸ supplied else siblings other same

theorem insert_injective (constructor : signature.Constructor) (position : Fin (signature.arity constructor))
    (siblings : (other : Fin (signature.arity constructor)) → other ≠ position →
      Class signature Parallel (signature.input constructor other)) :
    Function.Injective (insert constructor position siblings) := by
  intro first second same
  have picked := congrFun same position
  simpa only [insert, dite_true] using picked

def fill {source target : signature.Srt} :
    Frame signature Parallel source target → Class signature Parallel source → Class signature Parallel target
  | .slot constructor position siblings => fun supplied =>
      (Head.node constructor (insert constructor position siblings supplied)).class

theorem fill_injective {source target : signature.Srt} (frame : Frame signature Parallel source target) :
    Function.Injective frame.fill := by
  cases frame with
  | slot constructor position siblings =>
    intro first second same
    have heads := Head.class_injective same
    have arguments : insert constructor position siblings first = insert constructor position siblings second := by
      simpa only [Head.node.injEq, heq_eq_eq, true_and] using heads
    exact insert_injective constructor position siblings arguments

end Frame

/-- The selected context interface retains its original declared sort. -/
structure Interface (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) where
  sort : signature.Srt

def interfaceEquiv (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) :
    Interface signature Parallel ≃ signature.Srt where
  toFun := Interface.sort
  invFun := Interface.mk
  left_inv vertex := by cases vertex; rfl
  right_inv _ := rfl

instance mixedQuiver (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) :
    Quiver (Interface signature Parallel) where
  Hom source target := Frame signature Parallel source.sort target.sort

def mixedAction (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) :
    Mettapedia.CategoryTheory.MixedResidue.Action
      (fun vertex : Interface signature Parallel =>
        ResiduePayload (signature := signature) (Parallel := Parallel) vertex.sort) where
  Value vertex := Class signature Parallel vertex.sort
  residue := residue
  residue_zero := residue_zero
  residue_add := residue_add
  frame := Frame.fill

theorem mixedCancellative (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) :
    (mixedAction signature Parallel).Cancellative where
  residue_injective := residue_injective
  frame_injective := Frame.fill_injective

abbrev MixedContext (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop)
    (source target : signature.Srt) :=
  Mettapedia.CategoryTheory.MixedResidue.Context
    (fun vertex : Interface signature Parallel =>
      ResiduePayload (signature := signature) (Parallel := Parallel) vertex.sort) ⟨source⟩ ⟨target⟩

abbrev MixedObject (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) :=
  Mettapedia.CategoryTheory.MixedResidue.Object (mixedAction signature Parallel)

def valueArrow {sort : signature.Srt} (supplied : Class signature Parallel sort) :
    (.origin : MixedObject signature Parallel) ⟶ .interface ⟨sort⟩ :=
  Mettapedia.CategoryTheory.MixedResidue.valueArrow (target := ⟨sort⟩)
    (mixedAction signature Parallel) supplied

def contextArrow {source target : signature.Srt} (supplied : MixedContext signature Parallel source target) :
    (.interface ⟨source⟩ : MixedObject signature Parallel) ⟶ .interface ⟨target⟩ :=
  Mettapedia.CategoryTheory.MixedResidue.contextArrow (mixedAction signature Parallel) supplied

theorem value_context_comp {source target : signature.Srt}
    (supplied : Class signature Parallel source) (context : MixedContext signature Parallel source target) :
    valueArrow supplied ≫ contextArrow context = valueArrow ((mixedAction signature Parallel).read context supplied) := rfl

theorem mixed_hasRelativePushouts {first second : signature.Srt}
    (firstValue : Class signature Parallel first) (secondValue : Class signature Parallel second) :
    Mettapedia.GSLT.RelativePushout.HasRelativePushouts
      (Mettapedia.CategoryTheory.MixedResidue.valueArrow (target := ⟨first⟩)
        (mixedAction signature Parallel) firstValue)
      (Mettapedia.CategoryTheory.MixedResidue.valueArrow (target := ⟨second⟩)
        (mixedAction signature Parallel) secondValue) := by
  classical
  exact Mettapedia.CategoryTheory.MixedResidue.closed_hasRelativePushouts
    (first := ⟨first⟩) (second := ⟨second⟩) (mixedAction signature Parallel)
      (mixedCancellative signature Parallel) firstValue secondValue

theorem mixed_redex_relativePushouts {first second : MixedObject signature Parallel}
    (agent : (.origin : MixedObject signature Parallel) ⟶ first)
    (redex : (.origin : MixedObject signature Parallel) ⟶ second) :
    Mettapedia.GSLT.RelativePushout.HasRelativePushouts agent redex := by
  classical
  exact Mettapedia.CategoryTheory.MixedResidue.redex_relativePushouts
    (mixedAction signature Parallel) (mixedCancellative signature Parallel) agent redex

theorem mixed_bisimulation_congruence
    (rules : Mettapedia.GSLT.RedexRelativeCongruence.ReactionRule
      (.origin : MixedObject signature Parallel) → Prop)
    {source target : MixedObject signature Parallel}
    {left right : (.origin : MixedObject signature Parallel) ⟶ source}
    (related : Mettapedia.GSLT.RedexRelativeCongruence.IPOBisimilar rules left right)
    (context : source ⟶ target) :
    Mettapedia.GSLT.RedexRelativeCongruence.IPOBisimilar rules (left ≫ context) (right ≫ context) := by
  classical
  exact Mettapedia.CategoryTheory.MixedResidue.bisimulation_congruence
    (mixedAction signature Parallel) (mixedCancellative signature Parallel) rules related context

end Mettapedia.OSLF.SortedCommutative
