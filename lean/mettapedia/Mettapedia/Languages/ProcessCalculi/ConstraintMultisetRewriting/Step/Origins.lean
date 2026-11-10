import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventCategory

/-!
# Origin-indexed candidates and explicit authority

The origin profile retains a key alongside the complete candidate. Preparing
effects is unchanged. Admission additionally requires the key to resolve to
the candidate's actual description and the caller to have permission for that
key and complete firing. The base step's admission is always retained. Neither a successful lookup
nor equality of descriptions grants permission by itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Origins

universe uO uT uH uOcc uS uF uK uD

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing) (Key : Type uK)

structure Candidate (s : State) where
  origin : Key
  firing : Firing s

variable {Key} {Description : State → Type uD}
  (describe : ∀ {s}, Firing s → Description s)
  (resolve : (s : State) → Key → Option (Description s))
  (authorized : (s : State) → Key → Firing s → Prop)

def base : Step X O State (Candidate (Firing := Firing) Key) :=
  P.reindex (fun candidate => candidate.firing)

def profile : Step X O State (Candidate (Firing := Firing) Key) :=
  { base P (Key := Key) with
    Admits {s} candidate := P.Admits candidate.firing ∧
      resolve s candidate.origin = some (describe candidate.firing) ∧ authorized s candidate.origin candidate.firing
    admitted_prepares _ admitted := P.prepares admitted.1 }

theorem prepares_iff {s : State} (candidate : Candidate (Firing := Firing) Key s) :
    (profile P describe resolve authorized).Prepares candidate ↔ P.Prepares candidate.firing := Iff.rfl

theorem admits_iff {s : State} (candidate : Candidate (Firing := Firing) Key s) :
    (profile P describe resolve authorized).Admits candidate ↔
      P.Admits candidate.firing ∧ resolve s candidate.origin = some (describe candidate.firing) ∧
        authorized s candidate.origin candidate.firing := Iff.rfl

theorem result_eq {s : State} (candidate : Candidate (Firing := Firing) Key s)
    (permitted : (profile P describe resolve authorized).Admits candidate) :
    (profile P describe resolve authorized).result candidate permitted = P.result candidate.firing permitted.1 := rfl

instance profile_literalInformation [P.LiteralInformation] :
    (profile P describe resolve authorized).LiteralInformation :=
  ⟨fun candidate => P.transported candidate.firing⟩

instance profile_literalKnowledge [P.LiteralKnowledge] :
    (profile P describe resolve authorized).LiteralKnowledge :=
  ⟨fun candidate => P.knowledge_preparedResult candidate.firing⟩

instance profile_exact [P.Exact] : (profile P describe resolve authorized).Exact :=
  ⟨fun candidate => Exact.exactness (P := P) candidate.firing⟩

theorem wrong_origin_refused {s : State} (candidate : Candidate (Firing := Firing) Key s)
    (wrong : resolve s candidate.origin ≠ some (describe candidate.firing)) :
    ¬ (profile P describe resolve authorized).Admits candidate := fun admitted => wrong admitted.2.1

theorem unauthorized_refused {s : State} (candidate : Candidate (Firing := Firing) Key s)
    (denied : ¬ authorized s candidate.origin candidate.firing) :
    ¬ (profile P describe resolve authorized).Admits candidate := fun admitted => denied admitted.2.2

theorem base_refusal_retained {s : State} (candidate : Candidate (Firing := Firing) Key s)
    (denied : ¬ P.Admits candidate.firing) :
    ¬ (profile P describe resolve authorized).Admits candidate := fun admitted => denied admitted.1

def forgetEvent {s t : State}
    (event : (profile P describe resolve authorized).effectCore.Event
      (profile P describe resolve authorized).eventAdmission s t) :
    P.effectCore.Event P.eventAdmission s t :=
  ⟨event.firing.firing, event.prepared, event.permitted.1, event.target_eq⟩

def liftEvent {s t : State} (origin : Key) (event : P.effectCore.Event P.eventAdmission s t)
    (resolved : resolve s origin = some (describe event.firing)) (permitted : authorized s origin event.firing) :
    (profile P describe resolve authorized).effectCore.Event
      (profile P describe resolve authorized).eventAdmission s t :=
  ⟨⟨origin, event.firing⟩, event.prepared, ⟨event.permitted, resolved, permitted⟩, event.target_eq⟩

theorem forget_lift {s t : State} (origin : Key) (event : P.effectCore.Event P.eventAdmission s t)
    (resolved : resolve s origin = some (describe event.firing)) (permitted : authorized s origin event.firing) :
    forgetEvent P describe resolve authorized (liftEvent P describe resolve authorized origin event resolved permitted) =
      event := by cases event; rfl

theorem retained_origin {s t : State}
    (event : (profile P describe resolve authorized).effectCore.Event
      (profile P describe resolve authorized).eventAdmission s t) :
    resolve s event.firing.origin = some (describe event.firing.firing) ∧ authorized s event.firing.origin event.firing.firing :=
  event.permitted.2

def erase : EffectCore.EventObject (profile P describe resolve authorized).effectCore
    (profile P describe resolve authorized).eventAdmission ⥤q
      EffectCore.EventObject P.effectCore P.eventAdmission where
  obj state := state
  map := forgetEvent P describe resolve authorized

theorem different_origins_distinct {s t : State} {first second : Key} (different : first ≠ second)
    (event : P.effectCore.Event P.eventAdmission s t)
    (resolvedFirst : resolve s first = some (describe event.firing))
    (resolvedSecond : resolve s second = some (describe event.firing))
    (allowedFirst : authorized s first event.firing) (allowedSecond : authorized s second event.firing) :
    liftEvent P describe resolve authorized first event resolvedFirst allowedFirst ≠
      liftEvent P describe resolve authorized second event resolvedSecond allowedSecond := by
  intro same
  exact different (congrArg (fun edge => edge.firing.origin) same)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Step.Origins
