import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee

/-!
# Request-local NIK selection for gradual dependent transport

Forward transport and blame-reflecting transport implement one common
gradual-state contract, but they earn different capabilities.  This module
connects that strict distinction to the maximal-native calculus:

* every exact map registers a forward-safe operation;
* a blame-reflecting operation may be registered only with explicit exact
  reflection and its derived transport laws;
* when reflection is registered, it is the unique strongest operation for
  both exact-state and stable-blame requests;
* without reflection, exact-state transport still has a unique strongest
  safe operation, while a stable-blame request is uninhabited; and
* revision-current NIK activation executes the retained operation directly.

The admission objects retain the raw index together with its live gradual
state.  Their semantic invariant is the actual precision theorem saying that
the state refines suspension; no unrestricted semantic placeholder is used.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeGradualCapabilityNIKSelection

open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee

universe uRaw uExact uRaw' uExact' uRevision uDependency uValue

/-! ## One common semantic contract -/

/-- A raw value paired with its dependent gradual capability state. -/
abbrev PackedState (fibre : Fibre.{uRaw, uExact}) :=
  Sigma fun raw => State fibre raw

/-- The source state is raised into the common universe of a transport pair.
Its invariant is the generic gradual precision theorem. -/
def sourceStateObject (source : Fibre.{uRaw, uExact})
    (_target : Fibre.{uRaw', uExact'}) :
    AdmissionObject.{max (max uRaw uExact) (max uRaw' uExact')} where
  Carrier := ULift.{max uRaw' uExact'} (PackedState source)
  Meaning := fun packed =>
    Refines packed.down.2 (.suspended : State source packed.down.1)

/-- The target state is raised into the same common universe. -/
def targetStateObject (_source : Fibre.{uRaw, uExact})
    (target : Fibre.{uRaw', uExact'}) :
    AdmissionObject.{max (max uRaw uExact) (max uRaw' uExact')} where
  Carrier := ULift.{max uRaw uExact} (PackedState target)
  Meaning := fun packed =>
    Refines packed.down.2 (.suspended : State target packed.down.1)

/-- Every exact map supplies the forward-safe admitted operation. -/
def safeOperation
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    sourceStateObject source target ⟶ targetStateObject source target where
  run := fun packed =>
    ULift.up ⟨map.mapRaw packed.down.1, mapSafe map packed.down.2⟩
  preserves := by
    rintro ⟨⟨raw, state⟩⟩ precision
    change Refines (mapSafe map state)
      (.suspended : State target (map.mapRaw raw))
    simpa only [mapSafe] using
      precision.mapSafe (map := map)

/-- Exact reflection supplies the stronger operation that retains stable
blame rather than invalidating it. -/
def reflectingOperation
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (reflects : map.ReflectsExact) :
    sourceStateObject source target ⟶ targetStateObject source target where
  run := fun packed =>
    ULift.up ⟨map.mapRaw packed.down.1, mapFull map reflects packed.down.2⟩
  preserves := by
    rintro ⟨⟨raw, state⟩⟩ precision
    change Refines (mapFull map reflects state)
      (.suspended : State target (map.mapRaw raw))
    simpa only [mapFull] using
      precision.mapFull reflects

@[simp] theorem safeOperation_run
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (packed : PackedState source) :
    (safeOperation map).run (ULift.up packed) =
      ULift.up ⟨map.mapRaw packed.1, mapSafe map packed.2⟩ :=
  rfl

@[simp] theorem reflectingOperation_run
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (reflects : map.ReflectsExact)
    (packed : PackedState source) :
    (reflectingOperation map reflects).run (ULift.up packed) =
      ULift.up ⟨map.mapRaw packed.1, mapFull map reflects packed.2⟩ :=
  rfl

/-! ## Capability registrations -/

inductive TransportCapability where
  | exactStateTransport
  | stableBlameTransport
  deriving DecidableEq, Repr

/-- Every forward map has one canonical safe face. -/
inductive SafeFace where
  | forwardSafe
  deriving DecidableEq, Repr

instance : PartialOrder SafeFace where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ first second => first.trans second
  le_antisymm := fun _ _ forward _ => forward

def safeSupports (_face : SafeFace)
    (capability : TransportCapability) : Prop :=
  capability = .exactStateTransport

/-- The safe-only recognized family exists for every exact map. -/
def safeFamily
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    RecognizedFamily SafeFace (sourceStateObject source target)
      (targetStateObject source target) where
  package
    | .forwardSafe => safeOperation map
  Capability := TransportCapability
  supports := safeSupports
  supports_mono := by
    intro weaker stronger related capability supported
    cases related
    exact supported
  strict_support_gain := by
    intro weaker stronger strict
    have same : weaker = stronger := strict.1
    exact False.elim (strict.2 same.symm)
  recognized := {.forwardSafe}
  licensed := {.forwardSafe}
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := by simp

/-- Exact-state transport is the feasible request for a safe-only family. -/
def safeRequest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    (safeFamily map).CapabilityRequest where
  required := {.exactStateTransport}
  candidates := {.forwardSafe}
  candidates_exact := by
    intro candidate
    cases candidate
    constructor
    · intro _member
      constructor
      · simp [safeFamily]
      · intro capability capabilityRequired
        change capability = TransportCapability.exactStateTransport
        exact capabilityRequired
    · intro _eligible
      simp
  candidates_nonempty := by simp

def safeSelection
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    (safeRequest map).StrongestNativeCalculusPrinciple where
  val := .forwardSafe
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily, safeRequest]
    · intro candidate _member
      cases candidate
      exact le_rfl

/-- A safe-only registry cannot fabricate a feasible stable-blame request.
The request's exact candidate equation and nonemptiness expose the
contradiction. -/
theorem safeFamily_has_no_stableBlame_request
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    ¬ ∃ request : (safeFamily map).CapabilityRequest,
      TransportCapability.stableBlameTransport ∈ request.required := by
  rintro ⟨request, required⟩
  obtain ⟨candidate, candidateMember⟩ := request.candidates_nonempty
  have supportsStable :=
    ((request.candidates_exact candidate).mp candidateMember).2
      .stableBlameTransport required
  cases candidate
  change TransportCapability.stableBlameTransport =
    TransportCapability.exactStateTransport at supportsStable
  cases supportsStable

/-- Reflection is registered with the laws it earns, so the stronger family
cannot be constructed from a flag or an operational assertion alone. -/
structure ReflectingRegistration
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) where
  reflects : map.ReflectsExact
  laws : ReflectingTransportLaws map reflects

def reflectingRegistration
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (reflects : map.ReflectsExact) :
    ReflectingRegistration map where
  reflects := reflects
  laws := reflectingTransportLaws map reflects

inductive ReflectingFace where
  | forwardSafe
  | blameReflecting
  deriving DecidableEq, Fintype, Repr

namespace ReflectingFace

def rank : ReflectingFace → Nat
  | .forwardSafe => 0
  | .blameReflecting => 1

instance : PartialOrder ReflectingFace where
  le := fun first second => rank first ≤ rank second
  le_refl := fun face => Nat.le_refl (rank face)
  le_trans := fun _ _ _ first second => Nat.le_trans first second
  le_antisymm := by
    intro first second forward backward
    cases first <;> cases second <;> simp [rank] at forward backward ⊢

end ReflectingFace

def reflectingSupports (face : ReflectingFace)
    (capability : TransportCapability) : Prop :=
  capability = .exactStateTransport ∨ face = .blameReflecting

/-- Adding one checked reflection registration extends the safe family by one
strictly stronger, blame-retaining face. -/
def reflectingFamily
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    RecognizedFamily ReflectingFace (sourceStateObject source target)
      (targetStateObject source target)
    where
  package
    | .forwardSafe => safeOperation map
    | .blameReflecting => reflectingOperation map registration.reflects
  Capability := TransportCapability
  supports := reflectingSupports
  supports_mono := by
    intro weaker stronger related capability supported
    rcases supported with exactCapability | weakerReflecting
    · exact Or.inl exactCapability
    · subst weaker
      cases stronger with
      | forwardSafe =>
          change (1 : Nat) ≤ 0 at related
          omega
      | blameReflecting =>
          exact Or.inr rfl
  strict_support_gain := by
    intro weaker stronger strict
    cases weaker <;> cases stronger
    · exact False.elim (strict.2 le_rfl)
    · exact ⟨.stableBlameTransport,
        by simp [reflectingSupports], by simp [reflectingSupports]⟩
    · have impossible :
          ¬ (ReflectingFace.blameReflecting ≤ ReflectingFace.forwardSafe) := by
          change ¬ ((1 : Nat) ≤ 0)
          omega
      exact False.elim (impossible strict.1)
    · exact False.elim (strict.2 le_rfl)
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := ⟨.forwardSafe, by simp⟩

/-- An exact-state request sees both registered faces; maximal-native
selection must therefore choose the reflecting common upgrade. -/
def exactRequest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    (reflectingFamily map registration).CapabilityRequest where
  required := {.exactStateTransport}
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      constructor
      · simp [reflectingFamily]
      · intro capability capabilityRequired
        apply Or.inl
        change capability = TransportCapability.exactStateTransport
        exact capabilityRequired
    · intro _eligible
      simp
  candidates_nonempty := ⟨.forwardSafe, by simp⟩

/-- A blame-sensitive request cuts out exactly the reflecting face. -/
def stableBlameRequest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    (reflectingFamily map registration).CapabilityRequest where
  required := {.stableBlameTransport}
  candidates := {.blameReflecting}
  candidates_exact := by
    intro candidate
    cases candidate with
    | forwardSafe =>
        constructor
        · intro impossible
          simp at impossible
        · rintro ⟨_licensed, supportsRequired⟩
          have impossible := supportsRequired .stableBlameTransport (by simp)
          simp [reflectingFamily, reflectingSupports] at impossible
    | blameReflecting =>
        constructor
        · intro _member
          constructor
          · simp [reflectingFamily]
          · intro capability _required
            exact Or.inr rfl
        · intro _eligible
          simp
  candidates_nonempty := by simp

def exactSelection
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    (exactRequest map registration).StrongestNativeCalculusPrinciple where
  val := .blameReflecting
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily, exactRequest]
    · intro candidate _member
      cases candidate with
      | forwardSafe =>
          change (0 : Nat) ≤ 1
          omega
      | blameReflecting => exact le_rfl

def stableBlameSelection
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    (stableBlameRequest map registration).StrongestNativeCalculusPrinciple
    where
  val := .blameReflecting
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        stableBlameRequest]
    · intro candidate candidateMember
      have candidateEqual : candidate = .blameReflecting := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          stableBlameRequest] using candidateMember
      subst candidate
      exact le_rfl

/-- The safe request has exactly one strongest registered operation. -/
theorem safeRequest_uniqueStrongest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) :
    ∃! chosen,
      (safeRequest map).restrictedFamily.IsGreatestLicensed chosen := by
  refine ⟨.forwardSafe, (safeSelection map).property, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    (safeRequest map).restrictedFamily candidateGreatest
      (safeSelection map).property

/-- Once reflection is registered, its face is the unique strongest member
of the exact-state request as well. -/
theorem exactRequest_uniqueStrongest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    ∃! chosen,
      (exactRequest map registration).restrictedFamily.IsGreatestLicensed
        chosen := by
  refine ⟨.blameReflecting, (exactSelection map registration).property, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    (exactRequest map registration).restrictedFamily candidateGreatest
      (exactSelection map registration).property

/-- The blame-sensitive request has the same unique strongest member. -/
theorem stableBlameRequest_uniqueStrongest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    ∃! chosen,
      (stableBlameRequest map registration).restrictedFamily
        |>.IsGreatestLicensed chosen := by
  refine ⟨.blameReflecting,
    (stableBlameSelection map registration).property, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    (stableBlameRequest map registration).restrictedFamily candidateGreatest
      (stableBlameSelection map registration).property

/-- Reflection registration is a real strict capability upgrade, and its
forward-safe member is definitionally the canonical safe operation. -/
theorem reflection_registration_strictly_upgrades_safe
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    ReflectingFace.forwardSafe < ReflectingFace.blameReflecting ∧
      (reflectingFamily map registration).supports
        .blameReflecting .stableBlameTransport ∧
      ¬ (reflectingFamily map registration).supports
        .forwardSafe .stableBlameTransport := by
  constructor
  · constructor
    · change (0 : Nat) ≤ 1
      omega
    · change ¬ ((1 : Nat) ≤ 0)
      omega
  · simp [reflectingFamily, reflectingSupports]

@[simp] theorem reflection_registration_retains_safe_operation
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    (reflectingFamily map registration).package .forwardSafe =
      (safeFamily map).package .forwardSafe :=
  rfl

/-- Exact-state and stable-blame requests agree on the unique strongest face
when reflection has actually been registered. -/
theorem reflecting_requests_choose_same_strongest
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map) :
    (exactSelection map registration).1 = .blameReflecting ∧
      (stableBlameSelection map registration).1 = .blameReflecting :=
  ⟨rfl, rfl⟩

@[simp] theorem safeStrongestOperation_run
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (packed : PackedState source) :
    ((safeRequest map).strongestOperation (safeSelection map)).run
        (ULift.up packed) =
      (safeOperation map).run (ULift.up packed) :=
  rfl

@[simp] theorem exactStrongestOperation_run
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map)
    (packed : PackedState source) :
    ((exactRequest map registration).strongestOperation
      (exactSelection map registration)).run (ULift.up packed) =
        (reflectingOperation map registration.reflects).run
          (ULift.up packed) :=
  rfl

@[simp] theorem stableBlameStrongestOperation_run
    {source : Fibre.{uRaw, uExact}}
    {target : Fibre.{uRaw', uExact'}}
    (map : ExactMap source target) (registration : ReflectingRegistration map)
    (packed : PackedState source) :
    ((stableBlameRequest map registration).strongestOperation
      (stableBlameSelection map registration)).run (ULift.up packed) =
        (reflectingOperation map registration.reflects).run
          (ULift.up packed) :=
  rfl

/-! ## Positive, negative, and revision-current controls -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State.Canary

def collapseSafeSelection := safeSelection collapse

/-- The many-to-one collapse still earns exact-state transport. -/
theorem collapse_selects_safe_transport :
    (collapseSafeSelection).1 = .forwardSafe :=
  rfl

/-- The same collapse cannot be enrolled in the stronger registry. -/
theorem collapse_has_no_reflecting_registration :
    ¬ Nonempty (ReflectingRegistration collapse) := by
  rintro ⟨registration⟩
  exact collapse_not_reflects ⟨registration.reflects⟩

def identityMap := ExactMap.id source

def identityRegistration : ReflectingRegistration identityMap :=
  reflectingRegistration identityMap (ExactMap.reflects_id source)

def unsupportedPacked : PackedState source :=
  ⟨false, .refuted unsupportedBlame⟩

def unsupportedInput : ULift.{0} (PackedState source) :=
  ULift.up unsupportedPacked

/-- Safe selection invalidates blame at the non-reflecting boundary. -/
theorem selected_collapse_invalidates_blame :
    ((safeRequest collapse).strongestOperation collapseSafeSelection).run
        unsupportedInput =
      ULift.up ⟨PUnit.unit, .suspended⟩ :=
  rfl

/-- The strongest reflecting identity retains blame as a blame state. -/
theorem selected_identity_retains_blame_shape :
    ∃ blame : Refutation source false,
      ((stableBlameRequest identityMap identityRegistration).strongestOperation
        (stableBlameSelection identityMap identityRegistration)).run
          unsupportedInput =
        ULift.up ⟨false, .refuted blame⟩ := by
  exact ⟨mapRefutation identityMap identityRegistration.reflects
    unsupportedBlame, rfl⟩

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read := fun revision _ => revision

def admittedCollapse :=
  admitStrongestAt (safeFamily collapse) (safeRequest collapse)
    collapseSafeSelection dependencies false

def activeCollapse : admittedCollapse.Active false :=
  admittedCollapse.activate (dependencies.sameDependencies_refl false)

/-- Current NIK activation executes the selected safe operation directly. -/
theorem current_activation_runs_selected_safe_operation :
    activeCollapse.run unsupportedInput =
      ULift.up ⟨PUnit.unit, .suspended⟩ :=
  rfl

/-- A relevant dependency change prevents hot activation.  The unchanged raw
state remains the input of the ordinary safe semantics, whose own revision law
returns only the optional capability to suspension. -/
theorem changed_revision_prevents_activation :
    ¬ Nonempty (admittedCollapse.Active true) := by
  rintro ⟨active⟩
  have changed := active.current ()
  simp [dependencies] at changed

theorem stale_input_remains_raw_and_suspended :
    (unsupportedPacked.2.activateAt false true =
        (State.suspended : State source false)) ∧
      unsupportedPacked.1 = false := by
  exact ⟨activateAt_stale (by decide) unsupportedPacked.2, rfl⟩

end Canary

/-! ## Axiom audit -/

#print axioms safeOperation
#print axioms reflectingOperation
#print axioms safeFamily_has_no_stableBlame_request
#print axioms safeRequest_uniqueStrongest
#print axioms exactRequest_uniqueStrongest
#print axioms stableBlameRequest_uniqueStrongest
#print axioms reflection_registration_strictly_upgrades_safe
#print axioms reflection_registration_retains_safe_operation
#print axioms reflecting_requests_choose_same_strongest
#print axioms safeStrongestOperation_run
#print axioms exactStrongestOperation_run
#print axioms stableBlameStrongestOperation_run
#print axioms Canary.collapse_has_no_reflecting_registration
#print axioms Canary.selected_collapse_invalidates_blame
#print axioms Canary.selected_identity_retains_blame_shape
#print axioms Canary.current_activation_runs_selected_safe_operation
#print axioms Canary.changed_revision_prevents_activation
#print axioms Canary.stale_input_remains_raw_and_suspended

end Mettapedia.Languages.MeTTa.Prime.NativeGradualCapabilityNIKSelection
