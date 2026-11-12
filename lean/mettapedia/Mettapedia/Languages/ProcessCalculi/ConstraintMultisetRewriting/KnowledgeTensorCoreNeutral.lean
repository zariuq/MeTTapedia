import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreFirstOrder

/-!
# The empty context is in every grade

A graded proof of the two-zone calculus always admits the empty extra context. On the step this
is a property of a state: a state is neutral when every admitted firing is framed and admitted
beside it.

* `Neutral`: the property.
* `checks_of_neutral`: beside a neutral state every run is in its own grade.
* `placed_run_of_neutral`: so every run has a placed run there.
* `FirstOrder.unit_neutral`: the empty first-order configuration is neutral.

* `FirstOrder.contextChecks_pair`: in first order, where two configurations have a tensor,
  framing one firing by a pair of contexts is framing it twice.

The interface of placements has no pairing of two contexts, so the law that framing a run twice
is framing it by the pair is not stated for an arbitrary step.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore

universe uO uT uH uOcc uS uF uI uP

section Generic

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {P : Step X O State Firing}
  {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}
  (I : ContextualRunInterpretation.{uO,uT,uH,uOcc,uS,uF,uI,uP} T)

/-- A state is neutral when every admitted firing is framed and admitted beside it. -/
def Neutral (beside : State) : Prop :=
  ∀ {left : State} (place : I.Place left beside) (f : Firing left), P.Admits f →
    I.domain place f ∧ I.check place f

variable {I}

/-- **Beside a neutral state every run is in its own grade.** -/
theorem checks_of_neutral {beside : State} (neutral : Neutral I beside) :
    ∀ {left : State} (place : I.Place left beside) (run : P.Run left), I.Checks place run
  | _, _, .nil _ => trivial
  | _, place, .cons f allowed rest => by
      show (I.domain place f ∧ I.check place f) ∧ I.Checks (I.advance place f allowed) rest
      exact ⟨neutral place f allowed, checks_of_neutral neutral (I.advance place f allowed) rest⟩

/-- Beside a neutral state every run has a placed run. -/
theorem placed_run_of_neutral {beside : State} (neutral : Neutral I beside) {left : State}
    (place : I.Place left beside) (run : P.Run left) :
    ∃ native : P.Run (I.pair place).state, Places I place run native :=
  (exists_places_iff_checks I place run).mpr (checks_of_neutral neutral place run)

end Generic

section FirstOrder

open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open FirstOrderNativeRuns

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- **The empty first-order configuration is neutral.** -/
theorem FirstOrder.unit_neutral (A : SubstitutionAction T S) (label : O → T) :
    Neutral (contextualRunInterpretation A label)
      (AnnotatedRuns.unitConfiguration : Configuration T O) := by
  intro left _ f allowed
  have native : f.Valid A label (AnnotatedRuns.tensor left AnnotatedRuns.unitConfiguration) := by
    rw [AnnotatedRuns.tensor_unit_right]
    exact allowed
  exact ⟨Finset.disjoint_empty_right _, (valid_tensor_iff A label f allowed).mp native⟩

/-- **Framing a firing by a pair of contexts is framing it twice.** A firing passes its checks
beside the pair exactly when its outputs are fresh for the first context and it passes its
checks, at the pairing with the first, beside the second. -/
theorem FirstOrder.contextChecks_pair (A : SubstitutionAction T S) (label : O → T)
    (left first second : Configuration T O) (f : Firing T S O) :
    ContextChecks A label left (AnnotatedRuns.tensor first second) f ↔
      Disjoint f.selection.made.toFinset first.present ∧
        ContextChecks A label (AnnotatedRuns.tensor left first) second f := by
  have presentPair : (AnnotatedRuns.tensor first second).present =
      first.present ∪ second.present := rfl
  have presentLeft : (AnnotatedRuns.tensor left first).present ∪ second.present =
      left.present ∪ (first.present ∪ second.present) := Finset.union_assoc _ _ _
  unfold ContextChecks
  rw [AnnotatedRuns.tensor_assoc, presentLeft, presentPair, Finset.disjoint_union_right,
    and_assoc]

end FirstOrder

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore
