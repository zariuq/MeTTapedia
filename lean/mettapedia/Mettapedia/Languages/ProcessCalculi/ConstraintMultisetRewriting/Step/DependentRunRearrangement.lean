import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementPrefix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRaceHelpers

/-!
# Witnessed rearrangements on the actual dependent helper step

The existing natural-query helper step has the same admission and results as
its dependent full firings. This module embeds its complete runs into the
full step and constructs a witnessed interchange from the existing telescope
diamond. The closing map is the actual block exchange, with its knowledge,
present occurrences and typed rows, rather than an arbitrary endpoint match.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]


def toFull : {state : State rules O} → (helperStep levels O).toStep.Run state → (step levels O).toStep.Run state
  | _, .nil state => .nil state
  | _, .cons firing accepted rest => .cons firing.toFiring accepted (toFull rest)

theorem toFull_last : {state : State rules O} → (run : (helperStep levels O).toStep.Run state) →
    (toFull run).last = run.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => toFull_last rest

theorem toFull_word : {state : State rules O} → (run : (helperStep levels O).toStep.Run state) →
    (toFull run).word = run.word.map (fun event => ⟨event.1, event.2.toFiring⟩)
  | _, .nil _ => rfl
  | _, .cons _ _ rest => congrArg (List.cons _) (toFull_word rest)

structure Diamond {state : State rules O} (first second : HelperFiring levels O state)
    (accepted : (helperStep levels O).Admits first) (accepted' : (helperStep levels O).Admits second) where
  afterFirst : (helperStep levels O).Admits (helperResidual first accepted second)
  afterSecond : (helperStep levels O).Admits (helperResidual second accepted' first)
  agreement : Local.AgreeAlong (levels := levels) (exchange first.helpers second.helpers)
    ((helperStep levels O).result (helperResidual first accepted second) afterFirst).toLocal
    ((helperStep levels O).result (helperResidual second accepted' first) afterSecond).toLocal

theorem diamond_exists {state : State rules O} (first second : HelperFiring levels O state)
    (accepted : (helperStep levels O).Admits first) (accepted' : (helperStep levels O).Admits second)
    (independent : Independent (jointState first.helpers second.helpers)
      (atJointTelescopes first.data second.data).1 (atJointTelescopes first.data second.data).2) :
    Nonempty (Diamond first second accepted accepted') := by
  obtain ⟨afterFirst, afterSecond, agreement⟩ := telescope_diamond accepted accepted' independent
  exact ⟨⟨afterFirst, afterSecond, agreement⟩⟩

namespace Diamond

variable {state : State rules O} {first second : HelperFiring levels O state}
  {accepted : (helperStep levels O).Admits first} {accepted' : (helperStep levels O).Admits second}
  (diamond : Diamond first second accepted accepted')

def forward : (helperStep levels O).toStep.Run state :=
  .cons first accepted (.cons (helperResidual first accepted second) diamond.afterFirst (.nil _))

def backward : (helperStep levels O).toStep.Run state :=
  .cons second accepted' (.cons (helperResidual second accepted' first) diamond.afterSecond (.nil _))

def close : PlainIso levels diamond.forward.last diamond.backward.last :=
  (PlainIso.ofAgree (exchangeIso first.helpers second.helpers) diamond.agreement).symm

theorem close_frame : diamond.close.frame.hom = exchange second.helpers first.helpers := rfl

noncomputable def witness : (helperTransport levels O).InterchangeWitness diamond.forward diamond.backward :=
  Transport.InterchangeWitness.here (T := helperTransport levels O) accepted accepted'
    diamond.afterFirst diamond.afterSecond diamond.close (.nil _)

noncomputable def cell : Transport.RunRearrangement.Cell (helperTransport levels O) diamond.forward diamond.backward :=
  Transport.RunRearrangement.generator (helperTransport levels O) (.inr diamond.witness)

theorem event_count : diamond.forward.word.length = 2 ∧ diamond.backward.word.length = 2 := ⟨rfl, rfl⟩

theorem knowledge_kept :
    (frames levels).Equivalent ((frames levels).applyStore diamond.close.frame.hom
      diamond.forward.last.knowledge) diamond.backward.last.knowledge := diamond.close.knowledge

theorem occurrences_kept : diamond.forward.last.present = diamond.backward.last.present :=
  diamond.close.present

theorem typed_rows_kept (occurrence : O) :
    diamond.backward.last.label occurrence =
      (diamond.forward.last.label occurrence).reindex diamond.close.frame.hom :=
  diamond.close.label occurrence

theorem existing_trace : (helperTransport levels O).TraceEquiv state diamond.forward diamond.backward :=
  Transport.RunRearrangement.cell_trace diamond.cell

end Diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.diamond_exists
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.typed_rows_kept
