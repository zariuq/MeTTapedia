import Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission

/-!
# Request-local NIK selection of native composition

A hosted calculus may realize two admitted stages successively or provide one
direct construction.  The direct construction is not automatically a stronger
kernel: it must agree with the successive construction under the observation
declared by the request.

`CompositionSpec` retains the fallback, both admitted stages, the direct
operation, and that observation square.  It generates one finite
maximal-native family with three constructional faces.  The direct request has
a unique strongest member, but only because the specification already carries
the semantic agreement.  Exact proof-object preservation is the special case
whose observation is the identity; lossy observations remain explicitly
weaker and cannot be advertised as exact.

Revision-indexed admission stores the selected direct operation.  Current
activation runs it without checking or certificate replay, while failure of
dependency currentness prevents activation.  Profitability is absent from the
construction and remains an orthogonal policy decision.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKCompositionCapabilitySelection

open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission

universe uArtifact uObservation uRevision uDependency uValue

/-! ## A declared observation square for direct composition -/

/-- Two admitted stages and one direct realization, compared under one
explicitly declared observation of the target carrier.  The fallback belongs
to the same semantic fibre but need not construct the requested target view. -/
structure CompositionSpec
    (source middle target : AdmissionObject.{uArtifact}) where
  Observation : Type uObservation
  observe : target.Carrier → Observation
  fallback : source ⟶ target
  earlier : source ⟶ middle
  later : middle ⟶ target
  direct : source ⟶ target
  direct_agrees : ∀ input,
    observe (direct.run input) =
      observe ((AdmissionHom.comp earlier later).run input)

namespace CompositionSpec

variable {source middle target : AdmissionObject.{uArtifact}}

/-- The retained ordinary composition of the two admitted stages. -/
def sequential
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target) :
    source ⟶ target :=
  AdmissionHom.comp spec.earlier spec.later

@[simp] theorem sequential_run
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target)
    (input : source.Carrier) :
    spec.sequential.run input = spec.later.run (spec.earlier.run input) :=
  rfl

/-- Exact composition is the strongest observation: the complete target value
itself is retained. -/
def ofExact
    (fallback : source ⟶ target)
    (earlier : source ⟶ middle)
    (later : middle ⟶ target)
    (direct : source ⟶ target)
    (agreement : ∀ input,
      direct.run input = (AdmissionHom.comp earlier later).run input) :
    CompositionSpec.{uArtifact, uArtifact} source middle target where
  Observation := target.Carrier
  observe := id
  fallback := fallback
  earlier := earlier
  later := later
  direct := direct
  direct_agrees := agreement

/-- An exact specification exposes function equality, not only pointwise
agreement under a lossy readout. -/
theorem ofExact_direct_run_eq_sequential
    (fallback : source ⟶ target)
    (earlier : source ⟶ middle)
    (later : middle ⟶ target)
    (direct : source ⟶ target)
    (agreement : ∀ input,
      direct.run input = (AdmissionHom.comp earlier later).run input) :
    (ofExact fallback earlier later direct agreement).direct.run =
      (ofExact fallback earlier later direct agreement).sequential.run := by
  funext input
  exact agreement input

/-! ## The finite constructional family -/

/-- Ranks represent retained fallback, ordinary sequential composition, and
direct construction.  The specification's observation square is the license
for placing the direct face above the sequential face. -/
def family
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target) :
    RecognizedFamily (Fin 3) source target where
  package
    | ⟨0, _⟩ => spec.fallback
    | ⟨1, _⟩ => spec.sequential
    | ⟨2, _⟩ => spec.direct
  Capability := Fin 3
  supports := fun realization requested => requested ≤ realization
  supports_mono := by
    intro weaker stronger related requested supported
    exact supported.trans related
  strict_support_gain := by
    intro weaker stronger strict
    exact ⟨stronger, le_rfl, not_le_of_gt strict⟩
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := Finset.univ_nonempty

/-- The direct-composition request names the constructional capability it
needs; exact candidate enumeration prevents silent filtering. -/
def directRequest
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target) :
    spec.family.CapabilityRequest where
  required := fun requested => requested = (2 : Fin 3)
  candidates := {(2 : Fin 3)}
  candidates_exact := by
    intro candidate
    constructor
    · intro member
      have equal : candidate = (2 : Fin 3) := by simpa using member
      subst candidate
      constructor
      · simp [family]
      · intro requested required
        rcases required with rfl
        exact le_rfl
    · rintro ⟨licensed, supportsRequired⟩
      have supportsDirect := supportsRequired (2 : Fin 3) rfl
      change (2 : Fin 3) ≤ candidate at supportsDirect
      fin_cases candidate
      · simp at supportsDirect
      · simp at supportsDirect
      · simp
  candidates_nonempty := by simp

/-- The direct face is greatest in its exact one-member request fibre. -/
def directSelection
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target) :
    spec.directRequest.StrongestNativeCalculusPrinciple where
  val := (2 : Fin 3)
  property := by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        directRequest]
    · intro candidate candidateMember
      have equal : candidate = (2 : Fin 3) := by
        simpa [RecognizedFamily.CapabilityRequest.restrictedFamily,
          directRequest] using candidateMember
      subst candidate
      exact le_rfl

theorem directRequest_uniqueStrongest
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target) :
    ∃! chosen,
      spec.directRequest.restrictedFamily.IsGreatestLicensed chosen := by
  refine ⟨(2 : Fin 3), spec.directSelection.2, ?_⟩
  intro candidate candidateGreatest
  exact RecognizedFamily.greatestLicensed_unique
    spec.directRequest.restrictedFamily candidateGreatest
    spec.directSelection.2

/-- Selection returns the stored direct operation exactly. -/
@[simp] theorem directSelection_run
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target)
    (input : source.Carrier) :
    (spec.directRequest.strongestOperation spec.directSelection).run input =
      spec.direct.run input :=
  rfl

/-- The selected direct face retains the specification's declared observation
agreement with ordinary sequential composition. -/
theorem directSelection_observation_agrees
    (spec : CompositionSpec.{uArtifact, uObservation} source middle target)
    (input : source.Carrier) :
    spec.observe
        ((spec.directRequest.strongestOperation spec.directSelection).run
          input) =
      spec.observe (spec.sequential.run input) :=
  spec.direct_agrees input

/-! ## Revision-current direct admission -/

/-- Store the uniquely strongest direct face at one dependency revision.  The
current operational admission waist is intentionally runtime-sized. -/
def admitDirectAt
    {source middle target : AdmissionObject}
    (spec : CompositionSpec source middle target)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (revision : dependencies.Revision) :=
  admitStrongestAt spec.family spec.directRequest spec.directSelection
    dependencies revision

/-- Activate the retained direct face at a dependency-equivalent revision. -/
def activateDirectAt
    {source middle target : AdmissionObject}
    (spec : CompositionSpec source middle target)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (admittedRevision currentRevision : dependencies.Revision)
    (current : dependencies.SameDependencies admittedRevision
      currentRevision) :=
  (spec.admitDirectAt dependencies admittedRevision).activate current

/-- Hot execution is the direct map; selection, checking, and the observation
proof are absent from its argument list. -/
@[simp] theorem activateDirectAt_run
    {source middle target : AdmissionObject}
    (spec : CompositionSpec source middle target)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (admittedRevision currentRevision : dependencies.Revision)
    (current : dependencies.SameDependencies admittedRevision currentRevision)
    (input : source.Carrier) :
    (spec.activateDirectAt dependencies admittedRevision currentRevision
      current).run input = spec.direct.run input :=
  rfl

/-- Current direct execution agrees with ordinary sequential composition under
the exact observation declared by the hosted calculus. -/
theorem activateDirectAt_observation_agrees
    {source middle target : AdmissionObject}
    (spec : CompositionSpec source middle target)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (admittedRevision currentRevision : dependencies.Revision)
    (current : dependencies.SameDependencies admittedRevision currentRevision)
    (input : source.Carrier) :
    spec.observe
        ((spec.activateDirectAt dependencies admittedRevision currentRevision
          current).run input) =
      spec.observe (spec.sequential.run input) := by
  change spec.observe (spec.direct.run input) =
    spec.observe (spec.sequential.run input)
  exact spec.direct_agrees input

/-- Failure of dependency currentness makes the retained direct face
unavailable.  It does not alter the fallback operation stored in the
specification. -/
theorem no_active_of_not_current
    {source middle target : AdmissionObject}
    (spec : CompositionSpec source middle target)
    (dependencies : DependencySystem.{uRevision, uDependency, uValue})
    (admittedRevision currentRevision : dependencies.Revision)
    (stale : ¬ dependencies.SameDependencies admittedRevision
      currentRevision) :
    ¬ Nonempty
      ((spec.admitDirectAt dependencies admittedRevision).Active
        currentRevision) := by
  rintro ⟨active⟩
  exact stale active.current

end CompositionSpec

/-! ## Exact and observation-relative controls -/

namespace Canary

@[reducible] def naturals : AdmissionObject where
  Carrier := Nat
  Meaning := fun _ => True

def identity : naturals ⟶ naturals := AdmissionHom.id naturals

def addOne : naturals ⟶ naturals where
  run := fun value => value + 1
  preserves := fun _ _ => trivial

def addTwo : naturals ⟶ naturals where
  run := fun value => value + 2
  preserves := fun _ _ => trivial

def addThree : naturals ⟶ naturals where
  run := fun value => value + 3
  preserves := fun _ _ => trivial

def addFour : naturals ⟶ naturals where
  run := fun value => value + 4
  preserves := fun _ _ => trivial

def exact : CompositionSpec naturals naturals naturals :=
  CompositionSpec.ofExact identity addOne addOne addTwo (by
    intro input
    rfl)

theorem exact_direct_is_uniqueStrongest :
    ∃! chosen, exact.directRequest.restrictedFamily.IsGreatestLicensed chosen :=
  exact.directRequest_uniqueStrongest

theorem exact_direct_preserves_complete_result (input : Nat) :
    exact.direct.run input = exact.sequential.run input :=
  rfl

/-- Adding three is not exact fusion of two successor stages. -/
theorem addThree_has_no_exact_composition :
    ¬ (∀ input,
      addThree.run input = (AdmissionHom.comp addOne addOne).run input) := by
  intro agreement
  have impossible := agreement 0
  norm_num [addThree, addOne, AdmissionHom.comp] at impossible

/-- A lossy parity observation permits a different direct construction.  This
does not make it exact, and the next theorem keeps that distinction visible. -/
def parity : CompositionSpec naturals naturals naturals where
  Observation := Nat
  observe := fun value => value % 2
  fallback := identity
  earlier := addOne
  later := addOne
  direct := addFour
  direct_agrees := by
    intro input
    simp [addFour, addOne, AdmissionHom.comp, Nat.add_mod]

theorem parity_direct_agrees (input : Nat) :
    parity.observe (parity.direct.run input) =
      parity.observe (parity.sequential.run input) :=
  parity.direct_agrees input

theorem parity_direct_is_not_exact :
    ¬ (∀ input, parity.direct.run input = parity.sequential.run input) := by
  intro exactAgreement
  have impossible := exactAgreement 0
  norm_num [parity, addFour, addOne, AdmissionHom.comp] at impossible

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read := fun revision _ => revision

def currentExact :=
  exact.activateDirectAt dependencies false false
    (dependencies.sameDependencies_refl false)

def oneInput : (discreteOperationalObject naturals).theory.Term := by
  change Nat
  exact 1

def threeOutput : (discreteOperationalObject naturals).theory.Term := by
  change Nat
  exact 3

theorem current_exact_runs_direct :
    currentExact.run oneInput = threeOutput :=
  rfl

theorem changed_revision_refuses_exact_activation :
    ¬ Nonempty ((exact.admitDirectAt dependencies false).Active true) := by
  apply exact.no_active_of_not_current dependencies false true
  intro same
  have impossible := same ()
  exact Bool.noConfusion impossible

end Canary

/-! ## Axiom audit -/

#print axioms CompositionSpec.ofExact_direct_run_eq_sequential
#print axioms CompositionSpec.directRequest_uniqueStrongest
#print axioms CompositionSpec.directSelection_observation_agrees
#print axioms CompositionSpec.activateDirectAt_run
#print axioms CompositionSpec.activateDirectAt_observation_agrees
#print axioms CompositionSpec.no_active_of_not_current
#print axioms Canary.exact_direct_preserves_complete_result
#print axioms Canary.addThree_has_no_exact_composition
#print axioms Canary.parity_direct_agrees
#print axioms Canary.parity_direct_is_not_exact
#print axioms Canary.current_exact_runs_direct
#print axioms Canary.changed_revision_refuses_exact_activation

end Mettapedia.GSLT.LanguageDef.NIKCompositionCapabilitySelection
