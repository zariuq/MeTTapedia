import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementSuffix

/-!
# Continuing finite comparison certificates

A raw certificate is the actual path of oriented generators before inverse
cancellation. Its continuation moves through the retained boundary maps.
Backward generators use an explicit similarity correction and the inverse
of the extended generator. The construction chooses no witness of a mere
trace proposition. Its event permutation is the original certificate's
permutation, extended to the continuation positions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

abbrev Oriented (transport : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)
    {start : State} (first second : Object transport start) :=
  Generator transport first second ⊕ Generator transport second first

abbrev RawCell (transport : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)
    {start : State} (first second : Object transport start) :=
  @Quiver.Path (Quiver.Symmetrify (Object transport start))
    (Quiver.symmetrifyQuiver (Object transport start)) first second

def rawIdentity {start : State} (run : Object T start) : RawCell T run run :=
  @Quiver.Path.nil (Quiver.Symmetrify (Object T start)) (Quiver.symmetrifyQuiver (Object T start)) run

def Oriented.toPath {start : State} {first second : Object T start}
    (edge : Oriented T first second) : RawCell T first second :=
  @Quiver.Path.cons (Quiver.Symmetrify (Object T start)) (Quiver.symmetrifyQuiver (Object T start))
    first first second (rawIdentity first) edge

/-- Mathlib reversal with the symmetric generator quiver fixed explicitly. -/
def rawReverse {start : State} {first second : Object T start}
    (path : RawCell T first second) : RawCell T second first :=
  @Quiver.Path.reverse (Quiver.Symmetrify (Object T start))
    (@Quiver.symmetrifyQuiver (Object T start) (generatorQuiver T start))
    (@Quiver.instHasReverseSymmetrify (Object T start) (generatorQuiver T start)) first second path

def Oriented.boundary {start : State} {first second : Object T start} :
    Oriented T first second → T.Iso first.last second.last
  | .inl forward => forward.boundary
  | .inr backward => T.symm backward.boundary

def Oriented.position {start : State} {first second : Object T start} : Oriented T first second → Nat → Nat
  | .inl forward => forward.position
  | .inr backward => backward.position

def rawToCell {start : State} {first second : Object T start} (path : RawCell T first second) :
    Cell T first second := Quot.mk _ path

def Oriented.cell {start : State} {first second : Object T start} : Oriented T first second → Cell T first second
  | .inl forward => generator T forward
  | .inr backward => CategoryTheory.Groupoid.inv (generator T backward)

theorem rawToCell_cons {start : State} {first middle last : Object T start}
    (path : RawCell T first middle) (edge : Oriented T middle last) :
    rawToCell (path.cons edge) = rawToCell path ≫ (Oriented.cell edge) := by
  cases edge with
  | inl => rfl
  | inr => rfl

def rawPosition {start : State} {first second : Object T start}
    (path : RawCell T first second) (index : Nat) : Nat := by
  induction path with
  | nil => exact index
  | cons earlier edge ih => exact Oriented.position edge ih

theorem Oriented.events_val {start : State} {first second : Object T start}
    (edge : Oriented T first second) (event : Fin first.word.length) :
    (events T (Oriented.cell edge) event).val = (Oriented.position edge) event.val := by
  cases edge with
  | inl forward =>
      rw [Oriented.cell, events_generator]
      exact forward.events_val event
  | inr backward =>
      rw [Oriented.cell, CategoryTheory.Groupoid.inv_eq_inv, events_inv, events_generator]
      exact backward.events_inv_val event

theorem raw_events {start : State} {first second : Object T start} (path : RawCell T first second)
    (event : Fin first.word.length) :
    (events T (rawToCell path) event).val = rawPosition path event.val := by
  induction path with
  | nil =>
      change (events T (𝟙 (object T first)) event).val = event.val
      rw [events_id]
      rfl
  | cons path edge ih =>
      rw [rawToCell_cons, events_comp]
      exact ((Oriented.events_val edge) (events T (rawToCell path) event)).trans (congrArg (Oriented.position edge) ih)

def tailThrough {start : State} {first second : Object T start}
    (path : RawCell T first second) (continuation : P.Run first.last) : P.Run second.last := by
  induction path with
  | nil => exact continuation
  | cons earlier edge ih => exact T.moveRun (Oriented.boundary edge) ih

def rightEdge {start : State} {first second : Object T start} (edge : Oriented T first second)
    (continuation : P.Run first.last) :
    Cell T (first.append continuation) (second.append (T.moveRun (Oriented.boundary edge) continuation)) :=
  match edge with
  | .inl forward => generator T (forward.extend continuation)
  | .inr backward =>
      let moved := T.moveRun (T.symm backward.boundary) continuation
      let roundtrip := (SimilarityWitness.moveRun (T.symm backward.boundary) continuation).trans
        (SimilarityWitness.moveRun backward.boundary moved)
      generator T (.inl ((SimilarityWitness.refl first).append roundtrip)) ≫
        CategoryTheory.Groupoid.inv (generator T (backward.extend moved))

def rightCell {start : State} {first second : Object T start}
    (path : RawCell T first second) (continuation : P.Run first.last) :
    Cell T (first.append continuation) (second.append (tailThrough path continuation)) := by
  induction path with
  | nil => exact 𝟙 (object T (first.append continuation))
  | cons earlier edge ih => exact ih ≫ rightEdge edge (tailThrough earlier continuation)

theorem tailThrough_length {start : State} {first second : Object T start}
    (path : RawCell T first second) (continuation : P.Run first.last) :
    (tailThrough path continuation).word.length = continuation.word.length := by
  induction path with
  | nil => rfl
  | cons earlier edge ih =>
      exact (Similar.length_eq (Similar.moveRun (Oriented.boundary edge) (tailThrough earlier continuation))).symm.trans ih

theorem rightEdge_events {start : State} {first second : Object T start} (edge : Oriented T first second)
    (continuation : P.Run first.last) (event : Fin (first.append continuation).word.length) :
    (events T (rightEdge edge continuation) event).val = (Oriented.position edge) event.val := by
  cases edge with
  | inl forward =>
      rw [rightEdge, events_generator]
      exact ((forward.extend continuation).events_val event).trans (forward.position_extend continuation event.val)
  | inr backward =>
      let moved := T.moveRun (T.symm backward.boundary) continuation
      let roundtrip := (SimilarityWitness.moveRun (T.symm backward.boundary) continuation).trans
        (SimilarityWitness.moveRun backward.boundary moved)
      let correction := (SimilarityWitness.refl first).append roundtrip
      dsimp only [rightEdge]
      rw [events_comp, CategoryTheory.Groupoid.inv_eq_inv, events_inv, events_generator, events_generator]
      exact ((backward.extend moved).events_inv_val (correction.events event)).trans
        ((backward.position_extend moved _).trans (congrArg backward.position (correction.events_val event)))

theorem rightCell_events {start : State} {first second : Object T start} (path : RawCell T first second)
    (continuation : P.Run first.last) (event : Fin (first.append continuation).word.length) :
    (events T (rightCell path continuation) event).val = rawPosition path event.val := by
  induction path with
  | nil =>
      rw [rightCell, events_id]
      rfl
  | cons path edge ih =>
      rw [rightCell, events_comp]
      exact (rightEdge_events edge (tailThrough path continuation)
        (events T (rightCell path continuation) event)).trans (congrArg (Oriented.position edge) ih)

theorem rightCell_trace {start : State} {first second : Object T start} (path : RawCell T first second)
    (continuation : P.Run first.last) :
    T.TraceEquiv start (first.append continuation) (second.append (tailThrough path continuation)) :=
  cell_trace (rightCell path continuation)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.rightCell_events
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.RunRearrangement.rightCell_trace
