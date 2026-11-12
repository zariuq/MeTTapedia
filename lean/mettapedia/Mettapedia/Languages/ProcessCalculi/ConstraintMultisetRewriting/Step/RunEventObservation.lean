import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunInterchangeWitness

/-!
# Local observation laws for native event provenance

A label is preserved through run comparisons when it is unchanged by moving
a firing, replacing it by an alike firing, and taking its residual. These
are separate local conditions. The labels along an interchange follow its
actual event-position map. Selection sizes give a nonconstant instance over
every transport, without declaring raw occurrence identifiers invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI uL

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

structure EventObservation (Label : Type uL) where
  label : {state : State} → Firing state → Label
  moving : ∀ {s t : State} (comparison : T.Iso s t) (firing : Firing s),
    label (T.move comparison firing) = label firing
  alikeness : ∀ {state : State} {first second : Firing state},
    T.Alike first second → label first = label second
  residual : ∀ {state : State} (first : Firing state) (accepted : P.Admits first)
    (second : Firing state), label (T.residual first accepted second) = label second

namespace EventObservation

variable {T} {Label : Type uL} (observation : T.EventObservation Label)

def labels {start : State} (run : P.Run start) : List Label :=
  run.word.map (fun event => observation.label event.2)

theorem labels_similarity : {s t : State} → {first : P.Run s} → {second : P.Run t} →
    T.SimilarityWitness first second → observation.labels first = observation.labels second
  | _, _, .nil _, .nil _, .nil _ => rfl
  | _, _, .cons first accepted rest, .cons second accepted' rest', .cons comparison alike tail => by
      change observation.label first :: observation.labels rest =
        observation.label second :: observation.labels rest'
      rw [← observation.moving comparison first, observation.alikeness alike,
        labels_similarity tail]

theorem labels_moveRun {s t : State} (comparison : T.Iso s t) (run : P.Run s) :
    observation.labels (T.moveRun comparison run) = observation.labels run :=
  (observation.labels_similarity (SimilarityWitness.moveRun comparison run)).symm

private theorem shifted_swap (depth index : Nat) :
    ProofRelevantRuns.swapAt (depth + 1) (index + 1) = ProofRelevantRuns.swapAt depth index + 1 := by
  unfold ProofRelevantRuns.swapAt
  split_ifs <;> omega

theorem labels_interchange {start : State} {first second : P.Run start}
    (witness : T.InterchangeWitness first second) (index : Nat) :
    (observation.labels second)[witness.position index]? = (observation.labels first)[index]? := by
  induction witness generalizing index with
  | @here state first second accepted accepted' afterFirst afterSecond close rest =>
      change (observation.label second :: observation.label (T.residual second accepted' first) ::
        observation.labels (T.moveRun close rest))[ProofRelevantRuns.swapAt 0 index]? =
        (observation.label first :: observation.label (T.residual first accepted second) ::
          observation.labels rest)[index]?
      rw [observation.residual, observation.residual, observation.labels_moveRun]
      exact ProofRelevantRuns.getElem?_swapAt [] (observation.labels rest)
        (observation.label first) (observation.label second) index
  | @later state firing accepted first second tail ih =>
      cases index with
      | zero =>
          change (observation.label firing :: observation.labels second)[ProofRelevantRuns.swapAt (tail.depth + 1) 0]? =
            some (observation.label firing)
          simp [ProofRelevantRuns.swapAt]
      | succ index =>
          change (observation.label firing :: observation.labels second)[ProofRelevantRuns.swapAt (tail.depth + 1) (index + 1)]? =
              (observation.label firing :: observation.labels first)[index + 1]?
          rw [shifted_swap]
          exact ih index

end EventObservation

def selectionSizes : T.EventObservation (Nat × Nat × Nat) where
  label firing := ((P.selection firing).taken.length, (P.selection firing).read.length,
    (P.selection firing).made.length)
  moving comparison firing := by simp [T.selection_move, AnnotatedRuns.renameSelection]
  alikeness alike := by simp [T.selection_alike alike]
  residual first accepted second := by simp [T.selection_residual]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.EventObservation.labels_interchange
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.selectionSizes
