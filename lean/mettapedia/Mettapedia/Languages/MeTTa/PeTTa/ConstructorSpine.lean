import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSequence

/-!
# Strict data construction using the existing native list constructor

The expansion introduces no logical variables, store effects, copy scopes or
error-catching boundary. It is a reference lowering; its administrative source
steps remain distinct from a backend's direct data-construction control.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Unifying

def empty : Atom := .expression [.symbol "quote",.expression []]
def cons (first tail : Atom) : Atom := .expression [.symbol "cons-atom",first,tail]

def build : List Atom → Atom
  | [] => empty
  | first :: rest => cons first (build rest)

theorem cons_registered : StdLib.known "cons-atom" = true := by decide

theorem cons_strict (registry : SpaceSemantics.Program) (index : Nat) :
    Eval.argumentIsRaw registry "cons-atom" index = false := by
  simp [Eval.argumentIsRaw,cons_registered,StdLib.rawArgument]

theorem empty_step (registry : SpaceSemantics.Program) (base : Configuration) (bindings : Subst) :
    step registry {base with control := .evaluate bindings empty} =
      some {base with control := .returned [⟨.expression [],bindings⟩]} := rfl

theorem cons_enter_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (first tail : Atom) :
    step registry {base with control := .evaluate bindings (cons first tail)} =
      some {base with control := .arguments bindings (.function "cons-atom") [first,tail] [] 0} := rfl

theorem cons_head_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (first tail : Atom) :
    step registry {base with control := .arguments bindings (.function "cons-atom") [first,tail] [] 0} =
      some {base with
        control := .evaluate bindings first
        frames := .argument (.function "cons-atom") [tail] [] 0 :: base.frames} := rfl

theorem cons_tail_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (first tail : Atom) :
    step registry {base with control := .arguments bindings (.function "cons-atom") [tail] [first] 1} =
      some {base with
        control := .evaluate bindings tail
        frames := .argument (.function "cons-atom") [] [first] 1 :: base.frames} := rfl

theorem cons_finish_step (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (first : Atom) (tail : List Atom) :
    step registry {base with
      control := .arguments bindings (.function "cons-atom") [] [first,.expression tail] 2} =
      some {base with control := .returned [⟨.expression
        (resolve bindings first :: applySubst.applySubstList bindings tail),bindings⟩]} := rfl

theorem cons_finish_normal (registry : SpaceSemantics.Program) (base : Configuration)
    (bindings : Subst) (first : Atom) (tail : List Atom)
    (normal : Unbound bindings (.expression tail)) :
    step registry {base with
      control := .arguments bindings (.function "cons-atom") [] [first,.expression tail] 2} =
      some {base with control := .returned [⟨.expression (resolve bindings first :: tail),bindings⟩]} := by
  have fixed := resolve_of_unbound (.expression tail) normal
  change Atom.expression (applySubst.applySubstList bindings tail) = .expression tail at fixed
  rw [cons_finish_step,Atom.expression.inj fixed]

/-- Any actual head prefix lifts above the constructor's waiting frames.
No completed answer or terminating operand is required. -/
theorem head_prefix {registry : SpaceSemantics.Program} {before pending : Configuration}
    (bindings : Subst) (first tail : Atom)
    (path : Relation.ReflTransGen (Transition registry)
      {before with control := .evaluate bindings first,frames := []} pending)
    (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
      {before with control := .evaluate bindings (cons first tail),frames}
      (appendFrames pending (.argument (.function "cons-atom") [tail] [] 0 :: frames)) := by
  have entered := step_transition (cons_enter_step registry {before with frames} bindings first tail)
  have demanded := step_transition (cons_head_step registry {before with frames} bindings first tail)
  have lifted := steps_append_frames path (.argument (.function "cons-atom") [tail] [] 0 :: frames)
  simpa only [appendFrames,List.nil_append] using
    ((Relation.ReflTransGen.single entered).tail demanded).trans lifted

theorem tail_prefix {registry : SpaceSemantics.Program} {before pending : Configuration}
    (bindings : Subst) (first tail : Atom)
    (path : Relation.ReflTransGen (Transition registry)
      {before with control := .evaluate bindings tail,frames := []} pending)
    (frames : List Frame) :
    Relation.ReflTransGen (Transition registry)
      {before with control := .arguments bindings (.function "cons-atom") [tail] [first] 1,frames}
      (appendFrames pending (.argument (.function "cons-atom") [] [first] 1 :: frames)) := by
  have entered := step_transition (cons_tail_step registry {before with frames} bindings first tail)
  have lifted := steps_append_frames path (.argument (.function "cons-atom") [] [first] 1 :: frames)
  simpa only [appendFrames,List.nil_append] using Relation.ReflTransGen.head entered lifted

end Mettapedia.Languages.MeTTa.PeTTa.ConstructorSpine
