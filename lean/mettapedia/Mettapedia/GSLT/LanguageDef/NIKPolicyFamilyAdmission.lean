import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

/-!
# Revision-indexed admission of executable policy families

A policy readout is a displayed capability over retained semantic state, not a
semantic execution authority.  This module gives the generic policy-only
admission layer its proper home in GSLT:

* admission retains the executable realization of a dependent policy family;
* dependency currentness guards activation;
* the hot path runs only the retained keyed function;
* preparation retains the complete semantic state independently of a possibly
  lossy readout;
* staleness prevents activation without destroying that fallback state.

Exact replay, semantic execution admission, and profitability are independent
additional capabilities.  They may be displayed over this layer but are not
silently inferred from policy sufficiency.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission

universe uRevision uDependency uDependencyValue uState uPolicy uResult uKey

/-- An executable policy-family realization retained at one exact dependency
revision.  The retained runner is data; admission does not replay a proof at
each use. -/
structure PolicyFamilyAdmittedAt
    (dependencies :
      DependencySystem.{uRevision, uDependency, uDependencyValue})
    (revision : dependencies.Revision)
    {State : Type uState}
    (family : PolicyFamily.{uState, uPolicy, uResult} State)
    {Key : Type uKey} (readout : State -> Key) where
  realization : family.ReadoutRealization readout

namespace PolicyFamilyAdmittedAt

variable
  {dependencies :
    DependencySystem.{uRevision, uDependency, uDependencyValue}}
variable {revision currentRevision : dependencies.Revision}
variable {State : Type uState}
variable {family : PolicyFamily.{uState, uPolicy, uResult} State}
variable {Key : Type uKey} {readout : State -> Key}

/-- The support witness retained by an admission record. -/
def supports
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout) :
    family.SupportsReadout readout :=
  ⟨admission.realization⟩

/-- Every admitted policy runner is compatible with every collision of its
key.  This is the extensional safety readout of the constructive admission
record. -/
theorem compatibleReadout
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout) :
    family.CompatibleReadout readout :=
  family.supportsReadout_implies_compatible readout admission.supports

/-- Construct admission directly from a total representative for the key and
a proof that key collisions preserve every requested policy.  No certificate
is replayed by the resulting runner. -/
def ofSection
    (representative : Key -> State)
    (represents : Function.RightInverse representative readout)
    (compatible : family.CompatibleReadout readout) :
    PolicyFamilyAdmittedAt dependencies revision family readout where
  realization := family.readoutRealizationOfSection readout representative
    represents compatible

/-- A single policy-visible key collision excludes every admission record for
that key and family. -/
theorem noAdmission_of_policy_collision
    {first second : State} (sameReadout : readout first = readout second)
    (policy : family.Policy)
    (differentDecision :
      family.decide policy first ≠ family.decide policy second) :
    ¬ Nonempty
      (PolicyFamilyAdmittedAt dependencies revision family readout) := by
  rintro ⟨admission⟩
  exact differentDecision
    (admission.compatibleReadout first second sameReadout policy)

/-- Currentness is construction evidence for an active retained realization;
it is not an argument to the keyed policy function. -/
structure Active
    (_admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (currentRevision : dependencies.Revision) : Prop where
  current : dependencies.SameDependencies revision currentRevision

def activate
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (current : dependencies.SameDependencies revision currentRevision) :
    admission.Active currentRevision :=
  ⟨current⟩

/-- Hot evaluation is exactly the function retained at admission. -/
def Active.runKey
    {admission : PolicyFamilyAdmittedAt dependencies revision family readout}
    (_active : admission.Active currentRevision)
    (policy : family.Policy) : Key -> family.Result policy :=
  admission.realization.run policy

/-- The retained keyed function agrees with the declared semantic policy. -/
@[simp] theorem Active.runKey_readout
    {admission : PolicyFamilyAdmittedAt dependencies revision family readout}
    (active : admission.Active currentRevision)
    (policy : family.Policy) (state : State) :
    active.runKey policy (readout state) = family.decide policy state :=
  admission.realization.agrees policy state

/-- Preparation retains both the semantic state and its chosen readout.  The
state is the independent fallback; the readout may be deliberately lossy. -/
structure PreparedState
    (_admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    where
  state : State
  encoded : Key
  encoded_adequate : encoded = readout state

def prepare
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (state : State) : admission.PreparedState where
  state := state
  encoded := readout state
  encoded_adequate := rfl

/-- Fallback returns the retained semantic state without consulting admission
or attempting to invert the readout. -/
def PreparedState.fallback
    {admission : PolicyFamilyAdmittedAt dependencies revision family readout}
    (prepared : admission.PreparedState) : State :=
  prepared.state

@[simp] theorem PreparedState.fallback_eq
    {admission : PolicyFamilyAdmittedAt dependencies revision family readout}
    (prepared : admission.PreparedState) :
    prepared.fallback = prepared.state :=
  rfl

def Active.runPrepared
    {admission : PolicyFamilyAdmittedAt dependencies revision family readout}
    (active : admission.Active currentRevision)
    (prepared : admission.PreparedState) (policy : family.Policy) :
    family.Result policy :=
  active.runKey policy prepared.encoded

@[simp] theorem Active.runPrepared_eq
    {admission : PolicyFamilyAdmittedAt dependencies revision family readout}
    (active : admission.Active currentRevision)
    (prepared : admission.PreparedState) (policy : family.Policy) :
    active.runPrepared prepared policy = family.decide policy prepared.state := by
  unfold Active.runPrepared Active.runKey
  rw [prepared.encoded_adequate]
  exact admission.realization.agrees policy prepared.state

/-- A candidate revision is stale exactly when the selected dependency view
cannot be transported to it. -/
def StaleAt
    (_admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (candidateRevision : dependencies.Revision) : Prop :=
  ¬ dependencies.SameDependencies revision candidateRevision

/-- Staleness disables only the admitted readout.  The retained semantic state
remains an exact fallback without requiring readout inversion. -/
theorem stale_prevents_activation_and_preserves_fallback
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    {candidateRevision : dependencies.Revision}
    (stale : admission.StaleAt candidateRevision)
    (prepared : admission.PreparedState) :
    (¬ admission.Active candidateRevision) ∧
      prepared.fallback = prepared.state := by
  constructor
  · rintro ⟨current⟩
    exact stale current
  · rfl

end PolicyFamilyAdmittedAt

/-! ## Positive and stale controls -/

namespace Canary

def family : PolicyFamily Bool where
  Policy := Unit
  Result := fun _ => Bool
  decide := fun _ state => state

def readout : Bool -> Bool := id

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read := fun revision _ => revision

def admission :
    PolicyFamilyAdmittedAt dependencies false family readout :=
  PolicyFamilyAdmittedAt.ofSection
    (dependencies := dependencies) (revision := false)
    (family := family) (readout := readout)
    id (fun _ => rfl) (by
      intro first second sameReadout policy
      exact sameReadout)

def active : admission.Active false :=
  admission.activate (dependencies.sameDependencies_refl false)

def prepared : admission.PreparedState :=
  admission.prepare true

/-- Current evaluation uses the retained runner and returns the semantic
policy answer. -/
theorem current_run_agrees :
    active.runPrepared prepared () = true :=
  rfl

theorem changed_revision_is_stale : admission.StaleAt true := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- A relevant revision change prevents activation while the complete state
survives as fallback. -/
theorem changed_revision_refuses_runner_and_preserves_state :
    (¬ admission.Active true) ∧ prepared.fallback = true :=
  admission.stale_prevents_activation_and_preserves_fallback
    changed_revision_is_stale prepared

def collapsedReadout : Bool -> Unit := fun _ => ()

/-- A key collision visible to the requested policy prevents construction of
any admission record for that key. -/
theorem collapsed_key_has_no_admission :
    ¬ Nonempty
      (PolicyFamilyAdmittedAt dependencies false family collapsedReadout) := by
  apply PolicyFamilyAdmittedAt.noAdmission_of_policy_collision
    (first := false) (second := true) rfl ()
  change false ≠ true
  decide

end Canary

#print axioms PolicyFamilyAdmittedAt.Active.runPrepared_eq
#print axioms PolicyFamilyAdmittedAt.supports
#print axioms PolicyFamilyAdmittedAt.compatibleReadout
#print axioms PolicyFamilyAdmittedAt.ofSection
#print axioms PolicyFamilyAdmittedAt.noAdmission_of_policy_collision
#print axioms PolicyFamilyAdmittedAt.stale_prevents_activation_and_preserves_fallback
#print axioms Canary.current_run_agrees
#print axioms Canary.changed_revision_refuses_runner_and_preserves_state
#print axioms Canary.collapsed_key_has_no_admission

end Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
