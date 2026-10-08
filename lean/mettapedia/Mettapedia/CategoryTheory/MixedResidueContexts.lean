import Mathlib.Data.Multiset.UnionInter
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.CategoryTheory.Category.Basic

/-!
# Typed constructor frames interleaved with parallel residues

A context retains every genuine typed frame and its complete local residue.
Composition merges only the two residues at a common interface. Frames never
commute through residues. Taking an empty residue carrier at a fresh sort
therefore adds no parallel equations at that sort. The category operations
are constructed from these normal forms, independently of any ground action.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.MixedResidue

open _root_.CategoryTheory

universe u v w

variable {Vertex : Type u} [Quiver.{v} Vertex] (Payload : Vertex → Type w)

inductive Context : Vertex → Vertex → Type (max u v w) where
  | parallel {sort} (residue : Multiset (Payload sort)) : Context sort sort
  | frame {source middle target} (residue : Multiset (Payload target))
      (edge : middle ⟶ target) (inner : Context source middle) : Context source target

namespace Context

variable {Payload}

def outerBag {source target : Vertex} : Context Payload source target → Multiset (Payload target)
  | .parallel residue => residue
  | .frame residue _ _ => residue

def zeroOuter {source target : Vertex} : Context Payload source target → Context Payload source target
  | .parallel _ => .parallel 0
  | .frame _ edge inner => .frame 0 edge inner

def addOuter {source target : Vertex} (residue : Multiset (Payload target)) :
    Context Payload source target → Context Payload source target
  | .parallel previous => .parallel (residue + previous)
  | .frame previous edge inner => .frame (residue + previous) edge inner

def comp {source middle target : Vertex} (inner : Context Payload source middle) :
    Context Payload middle target → Context Payload source target
  | .parallel residue => inner.addOuter residue
  | .frame residue edge outer => .frame residue edge (inner.comp outer)

def frameCount {source target : Vertex} : Context Payload source target → Nat
  | .parallel _ => 0
  | .frame _ _ inner => inner.frameCount + 1

@[simp] theorem outerBag_addOuter {source target : Vertex}
    (residue : Multiset (Payload target)) (context : Context Payload source target) :
    (context.addOuter residue).outerBag = residue + context.outerBag := by
  cases context <;> rfl

@[simp] theorem zeroOuter_addOuter {source target : Vertex}
    (residue : Multiset (Payload target)) (context : Context Payload source target) :
    (context.addOuter residue).zeroOuter = context.zeroOuter := by
  cases context <;> rfl

theorem rebuild {source target : Vertex} (context : Context Payload source target) :
    context.zeroOuter.addOuter context.outerBag = context := by
  cases context <;> simp only [zeroOuter, outerBag, addOuter, add_zero]

theorem addOuter_zero {source target : Vertex} (context : Context Payload source target) :
    context.addOuter 0 = context := by
  cases context <;> simp only [addOuter, zero_add]

theorem addOuter_add {source target : Vertex}
    (first second : Multiset (Payload target)) (context : Context Payload source target) :
    (context.addOuter second).addOuter first = context.addOuter (first + second) := by
  cases context <;> simp only [addOuter, add_assoc]

theorem addOuter_injective {source target : Vertex} (residue : Multiset (Payload target)) :
    Function.Injective (addOuter (source := source) residue) := by
  intro first second same
  have bags : first.outerBag = second.outerBag := by
    have actual := congrArg outerBag same
    rw [outerBag_addOuter, outerBag_addOuter] at actual
    exact add_left_cancel actual
  have tails : first.zeroOuter = second.zeroOuter := by
    have actual := congrArg zeroOuter same
    rw [zeroOuter_addOuter, zeroOuter_addOuter] at actual
    exact actual
  exact first.rebuild.symm.trans
    ((congrArg₂ (fun residue context => context.addOuter residue) bags tails).trans second.rebuild)

theorem comp_addOuter {source middle target : Vertex}
    (inner : Context Payload source middle) (outer : Context Payload middle target)
    (residue : Multiset (Payload target)) :
    inner.comp (outer.addOuter residue) = (inner.comp outer).addOuter residue := by
  cases outer with
  | parallel previous =>
    exact (addOuter_add residue previous inner).symm
  | frame => rfl

theorem identity_comp {source target : Vertex} (context : Context Payload source target) :
    (parallel 0).comp context = context := by
  induction context with
  | parallel residue => exact congrArg parallel (add_zero residue)
  | frame residue edge inner inductionHypothesis =>
    exact congrArg (frame residue edge) inductionHypothesis

theorem comp_identity {source target : Vertex} (context : Context Payload source target) :
    context.comp (parallel 0) = context := addOuter_zero context

theorem comp_assoc {first second third fourth : Vertex}
    (before : Context Payload first second) (middle : Context Payload second third)
    (after : Context Payload third fourth) :
    (before.comp middle).comp after = before.comp (middle.comp after) := by
  induction after with
  | parallel residue => exact (comp_addOuter before middle residue).symm
  | frame residue edge outer inductionHypothesis =>
    exact congrArg (frame residue edge) inductionHypothesis

@[simp] theorem frameCount_addOuter {source target : Vertex}
    (residue : Multiset (Payload target)) (context : Context Payload source target) :
    (context.addOuter residue).frameCount = context.frameCount := by
  cases context <;> rfl

@[simp] theorem frameCount_comp {source middle target : Vertex}
    (inner : Context Payload source middle) (outer : Context Payload middle target) :
    (inner.comp outer).frameCount = inner.frameCount + outer.frameCount := by
  induction outer with
  | parallel residue => exact frameCount_addOuter residue inner
  | frame residue edge outer inductionHypothesis =>
    change (inner.comp outer).frameCount + 1 = inner.frameCount + (outer.frameCount + 1)
    rw [inductionHypothesis, Nat.add_assoc]

theorem frame_injective {source middle target : Vertex}
    (residue : Multiset (Payload target)) (edge : middle ⟶ target) :
    Function.Injective (frame (source := source) residue edge) := by
  intro first second same
  simpa only [frame.injEq, heq_eq_eq, true_and, and_true] using same

theorem comp_cancel_post {source middle target : Vertex}
    (outer : Context Payload middle target) {first second : Context Payload source middle}
    (same : first.comp outer = second.comp outer) : first = second := by
  induction outer with
  | parallel residue => exact addOuter_injective residue same
  | frame residue edge outer inductionHypothesis =>
    exact inductionHypothesis (frame_injective residue edge same)

end Context

end Mettapedia.CategoryTheory.MixedResidue
