import Mettapedia.Ethics.MetaEthicsOntology

/-!
# Target-Centered Virtue Ethics

This module gives a typed account of the four aspects used by target-centered
virtue ethics:

* **field** — the situations in which a virtue is relevant;
* **basis** — the value or values to which it responds;
* **mode** — the kind of response made by an agent; and
* **target** — the condition that counts as responding well enough.

The four aspects are data of every `VirtueSpec`; completeness is therefore
structural rather than a post-hoc tag.  Action-level target satisfaction and
agent-level dispositions are kept distinct.  This matters for learning: one
successful act is not definitionally the same thing as possessing a stable
virtue.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.TargetCenteredVirtue

open Mettapedia.Ethics

universe uAgent uSituation uAction uValue uVirtue

/-- Whether an aspect is a virtue, vice, or ethically neutral trait. -/
inductive CharacterValence : Type
  | virtue
  | vice
  | neutral
  deriving DecidableEq, Repr

def CharacterValence.toMoralValue :
    CharacterValence → MoralValueAttribute
  | .virtue => .MorallyGood
  | .vice => .MorallyBad
  | .neutral => .MorallyPermissible

def CharacterValence.ofMoralValue :
    MoralValueAttribute → CharacterValence
  | .MorallyGood => .virtue
  | .MorallyBad => .vice
  | .MorallyPermissible => .neutral

@[simp] theorem CharacterValence.toMoralValue_ofMoralValue
    (verdict : MoralValueAttribute) :
    (CharacterValence.ofMoralValue verdict).toMoralValue = verdict := by
  cases verdict <;> rfl

@[simp] theorem CharacterValence.ofMoralValue_toMoralValue
    (valence : CharacterValence) :
    CharacterValence.ofMoralValue valence.toMoralValue = valence := by
  cases valence <;> rfl

/-- The four typed aspects of one virtue, vice, or neutral trait.

`mode` is agent-indexed so intentions and other internal modes of response can
be represented rather than reconstructed from the visible action alone. -/
structure VirtueSpec
    (Agent : Type uAgent) (Situation : Type uSituation)
    (Action : Type uAction) (Value : Type uValue) where
  valence : CharacterValence
  field : Situation → Prop
  basis : Set Value
  basis_nonempty : basis.Nonempty
  mode : Agent → Situation → Action → Prop
  target : Agent → Situation → Action → Prop

namespace VirtueSpec

variable {Agent : Type uAgent} {Situation : Type uSituation}
  {Action : Type uAction} {Value : Type uValue}

/-- An action hits a virtue's target only inside its field and through its
declared mode of response. -/
def ActionHitsTarget
    (virtue : VirtueSpec Agent Situation Action Value)
    (agent : Agent) (situation : Situation) (action : Action) : Prop :=
  virtue.field situation ∧
    virtue.mode agent situation action ∧
    virtue.target agent situation action

theorem actionHitsTarget_in_field
    {virtue : VirtueSpec Agent Situation Action Value}
    {agent : Agent} {situation : Situation} {action : Action}
    (hits : virtue.ActionHitsTarget agent situation action) :
    virtue.field situation :=
  hits.1

theorem actionHitsTarget_has_mode
    {virtue : VirtueSpec Agent Situation Action Value}
    {agent : Agent} {situation : Situation} {action : Action}
    (hits : virtue.ActionHitsTarget agent situation action) :
    virtue.mode agent situation action :=
  hits.2.1

theorem actionHitsTarget_satisfies_target
    {virtue : VirtueSpec Agent Situation Action Value}
    {agent : Agent} {situation : Situation} {action : Action}
    (hits : virtue.ActionHitsTarget agent situation action) :
    virtue.target agent situation action :=
  hits.2.2

end VirtueSpec

/-- A target-centered virtue theory is a family of included, fully specified
virtues.  Identity of virtues is retained independently of their four aspects.
-/
structure Theory
    (Virtue : Type uVirtue)
    (Agent : Type uAgent) (Situation : Type uSituation)
    (Action : Type uAction) (Value : Type uValue) where
  included : Set Virtue
  spec : Virtue → VirtueSpec Agent Situation Action Value

namespace Theory

variable {Virtue : Type uVirtue}
  {Agent : Type uAgent} {Situation : Type uSituation}
  {Action : Type uAction} {Value : Type uValue}

/-- A theory supports a verdict when an included virtue/vice/neutral aspect of
that valence has its target hit by the action.  Conflicting support remains
visible instead of being silently resolved. -/
def SupportsVerdict
    (theory : Theory Virtue Agent Situation Action Value)
    (agent : Agent) (situation : Situation) (action : Action)
    (verdict : MoralValueAttribute) : Prop :=
  ∃ virtue, virtue ∈ theory.included ∧
    (theory.spec virtue).ActionHitsTarget agent situation action ∧
    (theory.spec virtue).valence.toMoralValue = verdict

/-- Every virtue relevant in the situation is hit by the action.  This is the
ungraded core of the source ontology's “hits the targets of relevant virtues
to a sufficient extent” clause; graded sufficiency is deliberately separate.
-/
def HitsEveryRelevantTarget
    (theory : Theory Virtue Agent Situation Action Value)
    (relevant : Virtue → Agent → Situation → Prop)
    (agent : Agent) (situation : Situation) (action : Action) : Prop :=
  ∀ virtue, virtue ∈ theory.included → relevant virtue agent situation →
    (theory.spec virtue).ActionHitsTarget agent situation action

/-- An agent possesses a virtue disposition at a situation when it is likely
to choose a target-hitting action whenever the situation lies in the virtue's
field.  `Likely` is supplied by the surrounding probability/evidence theory.
-/
def PossessesDisposition
    (theory : Theory Virtue Agent Situation Action Value)
    (Likely : Prop → Prop)
    (chooses : Agent → Situation → Action → Prop)
    (agent : Agent) (virtue : Virtue) : Prop :=
  virtue ∈ theory.included ∧
    ∀ situation, (theory.spec virtue).field situation →
      Likely (∃ action, chooses agent situation action ∧
        (theory.spec virtue).ActionHitsTarget agent situation action)

theorem supportsVerdict_has_target_witness
    {theory : Theory Virtue Agent Situation Action Value}
    {agent : Agent} {situation : Situation} {action : Action}
    {verdict : MoralValueAttribute}
    (supports : theory.SupportsVerdict agent situation action verdict) :
    ∃ virtue, virtue ∈ theory.included ∧
      (theory.spec virtue).target agent situation action := by
  rcases supports with ⟨virtue, included, hits, _⟩
  exact ⟨virtue, included, hits.2.2⟩

end Theory

/-! ## Rescue canaries -/

inductive RescueAgent : Type
  | helper
  deriving DecidableEq, Repr

inductive RescueSituation : Type
  | ordinary
  | emergency
  deriving DecidableEq, Repr

inductive RescueAction : Type
  | wait
  | cross
  deriving DecidableEq, Repr

inductive RescueValue : Type
  | preservationOfLife
  deriving DecidableEq, Repr

inductive RescueVirtue : Type
  | courage
  deriving DecidableEq, Repr

/-- Courage responds to the value of preserving life, in emergencies, through
crossing, with the target of crossing to help. -/
def courageSpec :
    VirtueSpec RescueAgent RescueSituation RescueAction RescueValue where
  valence := .virtue
  field situation := situation = .emergency
  basis := { .preservationOfLife }
  basis_nonempty := ⟨.preservationOfLife, by simp⟩
  mode _ _ action := action = .cross
  target _ _ action := action = .cross

def rescueTheory :
    Theory RescueVirtue RescueAgent RescueSituation RescueAction RescueValue where
  included := { .courage }
  spec _ := courageSpec

theorem emergencyCross_hits_courage_target :
    courageSpec.ActionHitsTarget .helper .emergency .cross := by
  simp [VirtueSpec.ActionHitsTarget, courageSpec]

theorem ordinaryCross_does_not_hit_courage_target :
    ¬ courageSpec.ActionHitsTarget .helper .ordinary .cross := by
  simp [VirtueSpec.ActionHitsTarget, courageSpec]

theorem emergencyWait_does_not_hit_courage_target :
    ¬ courageSpec.ActionHitsTarget .helper .emergency .wait := by
  simp [VirtueSpec.ActionHitsTarget, courageSpec]

theorem rescueTheory_supports_good_emergencyCross :
    rescueTheory.SupportsVerdict .helper .emergency .cross .MorallyGood := by
  exact ⟨.courage, by simp [rescueTheory],
    emergencyCross_hits_courage_target, rfl⟩

theorem rescueTheory_does_not_support_good_ordinaryCross :
    ¬ rescueTheory.SupportsVerdict .helper .ordinary .cross .MorallyGood := by
  rintro ⟨virtue, included, hits, _⟩
  have : virtue = .courage := by
    simp [rescueTheory] at included ⊢
  subst virtue
  exact ordinaryCross_does_not_hit_courage_target hits

theorem rescueTheory_hits_every_relevant_target :
    rescueTheory.HitsEveryRelevantTarget
      (fun virtue _ situation =>
        virtue = .courage ∧ situation = .emergency)
      .helper .emergency .cross := by
  intro virtue included relevant
  have virtueEq : virtue = .courage := by
    simp [rescueTheory] at included ⊢
  subst virtue
  exact emergencyCross_hits_courage_target

/-! ## Axiom audit -/

#print axioms CharacterValence.toMoralValue_ofMoralValue
#print axioms VirtueSpec.actionHitsTarget_in_field
#print axioms Theory.supportsVerdict_has_target_witness
#print axioms emergencyCross_hits_courage_target
#print axioms rescueTheory_does_not_support_good_ordinaryCross
#print axioms rescueTheory_hits_every_relevant_target

end Mettapedia.Ethics.TargetCenteredVirtue
