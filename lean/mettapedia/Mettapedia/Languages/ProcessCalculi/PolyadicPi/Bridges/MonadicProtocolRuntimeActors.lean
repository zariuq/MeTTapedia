import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolIdleFrame

/-!
# Actual heads of a mixed offered and committed tuple registry

Uncommitted publications and callback waiters are distinguished from the
three committed private phases. Actor descriptors retain the actual source
occurrence and lowered guard. Their computed list is an equation about the
existing process syntax; equal payloads and simultaneous offers stay distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeActors

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState ScopedActiveFrontier ActiveMarking ActiveGuardedBodies

inductive Origin (n : Nat) where
  | publication (owner : Fin n)
  | waiter (owner : Fin n)
  | privateActor (owner : Fin n) (kind : AtomKind)
  | idle (index : Nat)
  | suspended

inductive Actor (n : Nat) (Γ : Ctx sig) where
  | publication (owner : Fin n) (channel : Name Γ)
  | waiter (owner : Fin n) (first second : Name Γ)
  | output (owner : Fin n) (kind : OutputKind) (call : Call Γ)
  | input (owner : Fin n) (kind : InputKind) (call : Call Γ)

def Actor.origin {n : Nat} {Γ : Ctx sig} : Actor n Γ → Origin n
  | .publication owner _ => .publication owner
  | .waiter owner _ _ => .waiter owner
  | .output owner kind _ => .privateActor owner (.output kind)
  | .input owner kind _ => .privateActor owner (.input kind)

def waiterCall {Γ : Ctx sig} (first second : Name Γ) : Call Γ := ⟨first, second, nil⟩

def Actor.render {n : Nat} {Γ : Ctx sig} : Actor n Γ → Proc (World n Γ)
  | .publication owner channel => out1 (rename (ambient n) channel) (keyName n owner .session)
  | .waiter owner first second => placedInput n owner .callback (waiterCall first second)
  | .output owner kind call => placedOutput n owner kind call
  | .input owner kind call => placedInput n owner kind call

def Actor.marks {n : Nat} {Γ : Ctx sig} (actor : Actor n Γ) : ActiveMarking.Tree (Origin n) :=
  ActiveSyntaxMarking.mark actor.origin actor.render

def Actor.observation {n : Nat} {Γ : Ctx sig} :
    Actor n Γ → Observation (Origin n) (.nm :: World n Γ)
  | .publication owner channel => output1 (.publication owner)
      (rename (ambient n) channel) (keyName n owner .session) (StructuralOwnership.inclusion n)
  | .waiter owner first second => input1 (.waiter owner) (keyName n owner .session)
      (rename (liftRen (placement n owner) [.nm]) (inputBody .callback (waiterCall first second)))
      (StructuralOwnership.inclusion n)
  | .output owner kind call => output1 (.privateActor owner (.output kind))
      (keyName n owner kind.port) (placedDatum n owner kind call) (StructuralOwnership.inclusion n)
  | .input owner kind call => input1 (.privateActor owner (.input kind))
      (keyName n owner kind.port)
      (rename (liftRen (placement n owner) [.nm]) (inputBody kind call)) (StructuralOwnership.inclusion n)

theorem Actor.fits {n : Nat} {Γ : Ctx sig} (actor : Actor n Γ) :
    Fits actor.marks actor.render := ActiveSyntaxMarking.mark_fits _ _

theorem Actor.observes {n : Nat} {Γ : Ctx sig} (actor : Actor n Γ) :
    observe (fun _ : Origin n => (Var.zero : Var (.nm :: World n Γ) .nm))
      actor.marks actor.render (StructuralOwnership.inclusion n) = {actor.observation} := by
  cases actor with
  | publication => simp only [Actor.marks, Actor.render, Actor.origin, Actor.observation,
      ActiveSyntaxMarking.mark, out1, observe]
  | waiter =>
      simp only [Actor.marks, Actor.render, Actor.origin, Actor.observation]
      rw [input_header]
      simp only [ActiveSyntaxMarking.mark, inp1, observe]
      rfl
  | output =>
      simp only [Actor.marks, Actor.render, Actor.origin, Actor.observation]
      rw [output_header]
      simp only [ActiveSyntaxMarking.mark, out1, observe]
  | input =>
      simp only [Actor.marks, Actor.render, Actor.origin, Actor.observation]
      rw [input_header]
      simp only [ActiveSyntaxMarking.mark, inp1, observe]

def privateActor {Γ : Ctx sig} {n : Nat} (owner : Fin n) (call : Call Γ) : AtomKind → Actor n Γ
  | .output kind => .output owner kind call
  | .input kind => .input owner kind call

def slotActors {Γ : Ctx sig} {n : Nat} (owner : Fin n) : Slot Γ → List (Actor n Γ)
  | .offered channel first second => [.publication owner channel, .waiter owner first second]
  | .pending phase call => (atoms phase).map (privateActor owner (loweredCall call))
  | .released _ => []

def Live {Γ : Ctx sig} : Slot Γ → Prop
  | .offered _ _ _ | .pending _ _ => True
  | .released call => readback call = nil

theorem slot_equation {Γ : Ctx sig} {n : Nat} (owner : Fin n) (slot : Slot Γ)
    (live : Live slot) : StructuralEq (slot.placed n owner)
      (parallel ((slotActors owner slot).map Actor.render)) := by
  cases slot with
  | released call =>
      change readback call = nil at live
      rw [released_placed, live, lower_nil]
      change StructuralEq (rename (ambient n) nil) nil
      exact .refl _
  | offered channel first second =>
      have shape : (Slot.offered channel first second).placed n owner =
          par (Actor.render (.publication owner channel)) (Actor.render (.waiter owner first second)) := by
        simp only [Slot.placed, Slot.template, weaken, rename_comp, rename_par, rename_out1,
          sendFields, rename_inp1, Actor.render, placedInput, inputTemplate, inputBody, waiterCall]
        rfl
      rw [shape]
      change StructuralEq (par _ _) (par _ (par _ nil))
      exact .par (.refl _) (StructuralEq.parUnit _).symm
  | pending phase call =>
      have source := (contents_atoms phase (loweredCall call)).rename (placement n owner)
      rw [parallel_rename, List.map_map] at source
      refine source.trans ?_
      rw [slotActors, List.map_map]
      simp only [Function.comp_def]
      have equal : (fun kind => rename (placement n owner) (atomTemplate kind (loweredCall call))) =
          (fun kind => Actor.render (privateActor owner (loweredCall call) kind)) := by
        funext kind
        cases kind <;> rfl
      rw [equal]
      exact .refl _

def entries {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) : List (Actor n Γ) :=
  (List.finRange n).flatMap (fun owner => slotActors owner (registry owner))

def parallelMarks {Γ : Ctx sig} {n : Nat} : List (Actor n Γ) → ActiveMarking.Tree (Origin n)
  | [] => .nil
  | first :: rest => .par first.marks (parallelMarks rest)

theorem parallel_fits {Γ : Ctx sig} {n : Nat} (actors : List (Actor n Γ)) :
    Fits (parallelMarks actors) (parallel (actors.map Actor.render)) := by
  induction actors with
  | nil => exact .nil
  | cons first rest ih => exact .par first.fits ih

theorem observe_parallel {Γ : Ctx sig} {n : Nat} (actors : List (Actor n Γ))
    (observation : Observation (Origin n) (.nm :: World n Γ)) :
    observation ∈ observe (fun _ => Var.zero) (parallelMarks actors)
        (parallel (actors.map Actor.render)) (StructuralOwnership.inclusion n) ↔
      ∃ actor ∈ actors, observation = actor.observation := by
  induction actors with
  | nil => simp only [parallelMarks, List.map_nil, parallel, nil, observe, Set.mem_empty_iff_false,
      List.not_mem_nil, false_and, exists_false]
  | cons first rest ih =>
      simp only [parallelMarks, List.map_cons, parallel, par, observe, Set.mem_union,
        first.observes, Set.mem_singleton_iff, ih, List.mem_cons]
      constructor
      · rintro (same | ⟨actor, member, same⟩)
        · exact ⟨first, Or.inl rfl, same⟩
        · exact ⟨actor, Or.inr member, same⟩
      · rintro ⟨actor, equal | member, same⟩
        · subst actor; exact Or.inl same
        · exact Or.inr ⟨actor, member, same⟩

def assembly {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : Proc Γ) : Proc (World n Γ) :=
  par (parallel ((entries registry).map Actor.render)) (rename (ambient n) (lower frame))

def assemblyMarks {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : List (Proc Γ)) : ActiveMarking.Tree (Origin n) :=
  .par (parallelMarks (entries registry)) (IdleFrame.marks Origin.idle 0 frame)

theorem assembly_fits {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (frame : List (Proc Γ)) :
    Fits (assemblyMarks registry frame) (assembly registry (parallel frame)) := by
  refine .par (parallel_fits _) ?_
  have fitted := (IdleFrame.marks_fits (Origin.idle (n := n)) 0 frame).rename (ambient n)
  rw [IdleFrame.parallel_lower] at fitted
  exact fitted

private theorem slots_equation {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (owners : List (Fin n)) :
    StructuralEq (parallel (owners.map (fun owner => (registry owner).placed n owner)))
      (parallel ((owners.flatMap (fun owner => slotActors owner (registry owner))).map Actor.render)) := by
  induction owners with
  | nil => exact .refl _
  | cons owner rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, parallel]
      exact (StructuralEq.par (slot_equation owner (registry owner) (live owner)) ih).trans (parallel_append _ _)

theorem registry_equation {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (frame : Proc Γ) (live : ∀ owner, Live (registry owner)) :
    StructuralEq (registryTarget registry frame) (assembly registry frame) :=
  .par (slots_equation registry live _) (.refl _)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeActors
