import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulHelper

/-!
# Escape-relative transport of helper firings: the name-blind diamond, both sides

* **The helper transport is natural** (`Helpers.helperNatural`): its frame isomorphisms are the
  interface's, the lifted isomorphism of a result commutes with the inclusion of the old names, and
  a result is renamed as its start. Helper occurrences carry no rows, and helper firings record and
  publish nothing (`Helpers.helperEscape`, the silent escape data), so the escape-relative helper transport is
  `helperTransport.escaping helperNatural helperEscape`.

## The review's control C1

A frame with two parameterless holes `X` and `Y`; two helper firings that make occurrence `1` and a
fresh helper, valued `X` and valued `Y`.

* **The underlying transport identifies them** (`EscapeControls.base_identifies`): swapping the holes
  carries one to the other, whatever a client knows.
* **With both holes private, the escape-relative transport identifies them too**
  (`EscapeControls.private_identified`): they are trace equivalent, and one arrow of its trace
  category (`EscapeControls.private_one_trace`).
* **With `X` public, it does not** (`EscapeControls.public_not_identified`): an isomorphism of the
  start must carry `X` to itself at every solution of the (empty) knowledge, hence fix `X`, so it carries the firing valued `X` to itself and never to the firing valued `Y`.

## Occurrence identities: renamed while private, fixed once held

* **Private identities are renamed** (`EscapeControls.private_made_identified`): the firings that
  make occurrence `1` and occurrence `2`, with the same helper and value, are trace equivalent when
  no client knows either identity: the renaming that exchanges them is an isomorphism of the start.
* **Held identities are fixed** (`EscapeControls.escaped_made_not_identified`): when the environment
  holds a reference to `1`, every isomorphism of the start renames by an automorphism of its record,
  which fixes `1`, and the two firings are not trace equivalent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Interface.Frames (Frame)
open Observation (Record)

namespace Helpers

variable {S : Signature} {O : Type} [DecidableEq O]

/-- **The helper transport is natural.** -/
theorem helperNatural : (helperTransport (S := S) (O := O)).Natural where
  refl _ := Frames.Agree.refl _
  symm _ := Frames.Agree.refl _
  trans _ _ := Frames.Agree.refl _
  result_move i f admitted := Frames.Agree.of_eq (by
    show Assignment.compose (lift i.frame.hom f.helper) (helperStep.along f admitted) =
      Assignment.compose (helperStep.along (f.carry i.rename i.frame.hom) _) i.frame.hom
    rw [along_eq]
    exact (compose_lift_incl i.frame.hom f.helper).trans
      (congrArg (fun a => Assignment.compose a i.frame.hom) (along_eq (f.carry i.rename i.frame.hom) _).symm))
  result_alike {s} {f} _ same _ _ := by
    subst same
    exact Frames.Agree.of_eq (Assignment.compose_identity_left _)
  rename_refl _ := rfl
  rename_symm _ := rfl
  rename_trans _ _ := rfl
  rename_result_move _ _ _ := rfl
  rename_result_alike {s} {f} _ same _ _ := by
    subst same
    rfl

/-- Helper occurrences carry no rows, and helper firings record and publish nothing. -/
def helperEscape : (helperTransport (S := S) (O := O)).Escape := Transport.Escape.silent _

namespace EscapeControls

open Consumer (tiny)

/-- Two parameterless holes: `X` is `true`, `Y` is `false`. -/
abbrev holes : Frame tiny := ⟨Bool, fun _ => ([], ())⟩

/-- The hole `b`, as a term. -/
def hole (b : Bool) : Term (signature tiny holes.arity) [] () := generator holes.arity b

/-- Which hole heads an observation. -/
def whichHole : Observation tiny holes.arity → Bool
  | ⟨_, _, .op (.inr (.mk b)) _⟩ => b
  | _ => false

theorem hole_ne : observe (hole true) ≠ observe (hole false) := fun same => by
  have heads := congrArg whichHole same
  exact absurd heads (by decide)

/-- Swapping the two holes. -/
def swapHoles : Assignment holes.arity holes.arity := fun b => generator holes.arity (!b)

theorem swapHoles_swapHoles : Assignment.compose swapHoles swapHoles = generator holes.arity := by
  funext b
  show instantiate swapHoles (generator holes.arity (!b)) = generator holes.arity b
  rw [instantiate_generator]
  cases b <;> rfl

/-- Swapping the two holes is an isomorphism of frames. -/
def swapIso : (Frames.contextual tiny).Iso holes holes where
  hom := swapHoles
  inv := swapHoles
  inv_hom t := by
    show instantiateObservation swapHoles (instantiateObservation swapHoles t) = t
    rw [instantiateObservation_comp, swapHoles_swapHoles, instantiateObservation_identity]
  hom_inv t := by
    show instantiateObservation swapHoles (instantiateObservation swapHoles t) = t
    rw [instantiateObservation_comp, swapHoles_swapHoles, instantiateObservation_identity]

theorem swap_hole (b : Bool) : instantiate swapHoles (hole b) = hole (!b) :=
  instantiate_generator swapHoles b

/-- The state at the two holes, with no knowledge and no occurrences. -/
abbrev start : State tiny Nat := ⟨holes, [], ∅⟩

/-- The helper firing valued by the hole `b`: it makes occurrence `1` and a parameterless helper. -/
def valued (b : Bool) : Firing start := ⟨1, ([], ()), hole b, []⟩

theorem valued_admitted (b : Bool) : helperStep.Admits (valued b) :=
  (admits_iff (valued b)).mpr
    ⟨⟨holes, generator holes.arity, Frames.models_nil _⟩, Finset.notMem_empty _, asks_nil⟩

/-- Swapping the holes, as an isomorphism of the start. -/
def startSwap : helperStep.StateIso start start := ⟨swapIso, fun _ _ => Iff.rfl, Equiv.refl Nat, rfl⟩

/-- The swap carries the firing valued `X` to the firing valued `Y`. -/
theorem moved : helperTransport.Alike (helperTransport.move startSwap (valued true)) (valued false) :=
  Firing.mk_congr _ _ (swap_hole true) rfl

/-- **The underlying transport identifies the two firings.** -/
theorem base_identifies :
    helperTransport.TraceEquiv start (.cons (valued true) (valued_admitted true) (.nil _))
      (.cons (valued false) (valued_admitted false) (.nil _)) :=
  .rel _ _ (.inr (Transport.Similar.single startSwap (valued_admitted true) (valued_admitted false) moved))

/-- The escape-relative helper transport. -/
abbrev escaping : Transport (helperEscape (S := tiny) (O := Nat)).step :=
  helperTransport.escaping helperNatural helperEscape

/-- Both holes private. -/
abbrev bothPrivate : Escaped (helperStep (S := tiny) (O := Nat)).toStep := ⟨start, [], []⟩

/-- `X` public. -/
abbrev xPublic : Escaped (helperStep (S := tiny) (O := Nat)).toStep := ⟨start, [observe (hole true)], []⟩

/-- The one-firing run valued `b`, from the private start. -/
abbrev privateRun (b : Bool) : (helperEscape (S := tiny) (O := Nat)).step.Run bothPrivate :=
  .cons (valued b) (valued_admitted b) (.nil _)

/-- The one-firing run valued `b`, from the start where `X` is public. -/
abbrev publicRun (b : Bool) : (helperEscape (S := tiny) (O := Nat)).step.Run xPublic :=
  .cons (valued b) (valued_admitted b) (.nil _)

/-- The swap, relative to an environment that knows neither hole. -/
def privateSwap : escaping.Iso bothPrivate bothPrivate := ⟨startSwap, .nil, rfl⟩

/-- **With both holes private, the two firings are identified.** -/
theorem private_identified :
    escaping.TraceEquiv bothPrivate (privateRun true) (privateRun false) :=
  .rel _ _ (.inr (Transport.Similar.single privateSwap (valued_admitted true) (valued_admitted false) moved))

/-- **With `X` public, the two firings are not identified.** -/
theorem public_not_identified :
    ¬ escaping.TraceEquiv xPublic (publicRun true) (publicRun false) := by
  intro equivalent
  have similar := equivalent.similar_of_length_le_one (Nat.le_refl _)
  obtain ⟨i, moving, -⟩ := Transport.similar_cons_cons.mp similar
  have atIdentity : instantiateObservation (generator holes.arity)
      (instantiateObservation i.base.frame.hom (observe (hole true))) =
        instantiateObservation (generator holes.arity) (observe (hole true)) :=
    (List.forall₂_cons.mp i.names).1 holes (generator holes.arity) (Frames.models_nil _)
  have fixed : instantiateObservation i.base.frame.hom (observe (hole true)) = observe (hole true) := by
    rwa [instantiateObservation_identity, instantiateObservation_identity] at atIdentity
  rw [instantiateObservation_observe] at fixed
  have value : (⟨i.base.rename 1, ([], ()), instantiate i.base.frame.hom (hole true),
      (Frames.contextual tiny).applyStore i.base.frame.hom []⟩ : Firing start) =
      ⟨1, ([], ()), hole false, []⟩ := moving
  have carried : instantiate i.base.frame.hom (hole true) = hole false := by
    injection value
  exact hole_ne (fixed.symm.trans (congrArg observe carried))

/-- The helper firing that makes occurrence `o` and a parameterless helper valued `X`. -/
def making (o : Nat) : Firing start := ⟨o, ([], ()), hole true, []⟩

theorem making_admitted (o : Nat) : helperStep.Admits (making o) :=
  (admits_iff (making o)).mpr
    ⟨⟨holes, generator holes.arity, Frames.models_nil _⟩, Finset.notMem_empty _, asks_nil⟩

/-- Renaming occurrences `1` and `2` into each other, over the identity of the frame. -/
def occurrenceSwap : helperStep.StateIso start start :=
  ⟨Frames.Iso.refl holes, Frames.Iso.equivalent_refl (X := Frames.contextual tiny) [], Equiv.swap 1 2, rfl⟩

/-- The renaming carries the firing that makes `1` to the firing that makes `2`. -/
theorem made_moved :
    helperTransport.Alike (helperTransport.move occurrenceSwap (making 1)) (making 2) :=
  Firing.mk_congr_made (Equiv.swap_apply_left 1 2) _ (instantiate_identity (hole true)) rfl

/-- The renaming, relative to an environment that knows neither occurrence. -/
def privateRename : escaping.Iso bothPrivate bothPrivate := ⟨occurrenceSwap, .nil, rfl⟩

/-- **Making occurrence `1` and making occurrence `2`, with the same helper and value, are identified
while both identities are private.** -/
theorem private_made_identified :
    escaping.TraceEquiv bothPrivate (.cons (making 1) (making_admitted 1) (.nil _))
      (.cons (making 2) (making_admitted 2) (.nil _)) :=
  .rel _ _ (.inr (Transport.Similar.single privateRename (making_admitted 1) (making_admitted 2)
    made_moved))

/-- The environment holds a reference to occurrence `1`. -/
def holder : Record Nat := Record.references [1]

/-- Occurrence `1` escaped. -/
abbrev heldOne : Escaped (helperStep (S := tiny) (O := Nat)).toStep := ⟨start, [], holder⟩

/-- **Once occurrence `1` has escaped, the two firings are not identified**: every isomorphism of the
start renames by an automorphism of the record, which fixes `1`, so it carries the firing that
makes `1` to itself. -/
theorem escaped_made_not_identified :
    ¬ escaping.TraceEquiv heldOne (.cons (making 1) (making_admitted 1) (.nil _))
      (.cons (making 2) (making_admitted 2) (.nil _)) := by
  intro equivalent
  have similar := equivalent.similar_of_length_le_one (Nat.le_refl _)
  obtain ⟨i, moving, -⟩ := Transport.similar_cons_cons.mp similar
  have fixed : i.base.rename 1 = 1 :=
    Record.references_rename_eq_iff.mp i.record 1 (List.mem_singleton_self 1)
  have made : i.base.rename 1 = 2 := congrArg Firing.made moving
  exact absurd (fixed.symm.trans made) (by decide)

/-- The two one-firing runs from the private start end in one class. -/
theorem private_ends :
    escaping.Same (privateRun false).last (privateRun true).last :=
  (Transport.TraceEquiv.same_last private_identified).symm

/-- The one-firing run valued `b` from the private start, as an arrow of the trace category. -/
def privateArrow (b : Bool) :
    escaping.Arrow (Transport.StateClass.mk escaping bothPrivate)
      (Transport.StateClass.mk escaping (privateRun true).last) where
  start := bothPrivate
  run := privateRun b
  start_mem := rfl
  last_mem := by
    cases b
    · exact (Transport.StateClass.mk_eq_mk_iff escaping).mpr private_ends
    · rfl

/-- **With both holes private, the two firings are one arrow of the trace category.** -/
theorem private_one_trace :
    (Quot.mk _ (privateArrow true) : escaping.Trace _ _) = Quot.mk _ (privateArrow false) :=
  Quot.sound ⟨privateRun false,
    Transport.TraceEquiv.similar_of_length_le_one private_identified (Nat.le_refl _), .refl _⟩

end EscapeControls

end Helpers

#print axioms Helpers.helperNatural
#print axioms Helpers.helperEscape
#print axioms Helpers.EscapeControls.base_identifies
#print axioms Helpers.EscapeControls.private_identified
#print axioms Helpers.EscapeControls.public_not_identified
#print axioms Helpers.EscapeControls.private_one_trace
#print axioms Helpers.EscapeControls.private_made_identified
#print axioms Helpers.EscapeControls.escaped_made_not_identified

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
