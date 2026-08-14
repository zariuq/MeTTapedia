import Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
import Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionEffectAnalysis

/-!
# The gradual-typing seam for native interaction

A typed interaction fast path needs two independent witnesses:

* an `OptLicense`, showing that runtime type and cardinality evidence is exact;
* an occurrence-preserving Prime interaction computation, showing that the
  selected endpoint path is authorized by the interaction presentation.

The indexed `LicensedInteraction` below makes both fields mandatory.  The
generic branch of `InteractionPlan` carries neither.  It remains available for
unknown, unchecked, and conflicting type evidence and delegates to the raw
interaction semantics.

This module does not equate typechecking with execution.  Exact evidence may
select an already-authorized path; it cannot create one.  Conversely, an
authenticated path does not become a typed fast path until an exact license is
attached.  Conflict and exactness inherit the gradual seam's persistence and
rigidity laws.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeInteractionSeam

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Core
open Mettapedia.Languages.MeTTa.PeTTa.TypecheckV3Seam
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction

universe uOutput

/-! ## Licensed interaction fast paths -/

/-- A typed fast path contains both exact type/cardinality authority and an
exact interaction computation at the requested endpoints.  The type evidence
indices are explicit so gradual unknown cannot hide inside a licensed value. -/
structure LicensedInteraction {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (actual expected : Ty) (card : Card) (demand : ArrowMode)
    (source target : theory.Term) : Type where
  license : OptLicense
  license_actual : license.actual = actual
  license_expected : license.expected = expected
  license_card : license.card = card
  license_demand : license.demand = demand
  computation : familiesCwF.Tm PrimeContext
    (interactionComputationTy presentation source target)

namespace LicensedInteraction

variable {theory : GSLT}
variable {presentation : InteractionPresentation theory}
variable {actual expected : Ty} {card : Card} {demand : ArrowMode}
variable {source target : theory.Term}

/-- The accelerated path erases to an ordinary authorized GSLT rewrite path. -/
def erase (fast : LicensedInteraction presentation actual expected card demand
    source target) :
    familiesCwF.Tm PrimeContext (fun _ => theory.RewritePath source target) :=
  eraseInternalPath fast.computation

/-- A licensed path is in particular reachable in the raw interaction
semantics. -/
theorem raw_reachable
    (fast : LicensedInteraction presentation actual expected card demand
      source target) :
    Nonempty (theory.RewritePath source target) :=
  ⟨fast.erase PUnit.unit⟩

/-- Exact cache entries are rigid under later precision refinement. -/
theorem indices_rigid
    (fast : LicensedInteraction presentation actual expected card demand
      source target)
    {actual' expected' : Ty}
    (actualRefines : Refines actual' actual)
    (expectedRefines : Refines expected' expected) :
    actual' = actual ∧ expected' = expected := by
  have actualRefinesLicense : Refines actual' fast.license.actual := by
    rw [fast.license_actual]
    exact actualRefines
  have expectedRefinesLicense : Refines expected' fast.license.expected := by
    rw [fast.license_expected]
    exact expectedRefines
  obtain ⟨actualEq, expectedEq⟩ :=
    license_rigid fast.license actualRefinesLicense expectedRefinesLicense
  exact ⟨actualEq.trans fast.license_actual,
    expectedEq.trans fast.license_expected⟩

end LicensedInteraction

/-! ## Generic or licensed execution -/

/-- The interaction execution choice.  Generic execution is a first-class
constructor, not a failed attempt to build a licensed path. -/
inductive InteractionPlan {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (actual expected : Ty) (card : Card) (demand : ArrowMode)
    (source target : theory.Term) : Type where
  | generic
  | licensed
      (fast : LicensedInteraction presentation actual expected card demand
        source target)

namespace InteractionPlan

variable {theory : GSLT}
variable {presentation : InteractionPresentation theory}
variable {actual expected : Ty} {card : Card} {demand : ArrowMode}
variable {source target : theory.Term}

/-- Raw execution ignores optional acceleration evidence and receives exactly
the original endpoints. -/
def runRaw (run : theory.Term → theory.Term → Output)
    (_plan : InteractionPlan presentation actual expected card demand source
      target) : Output :=
  run source target

/-- Inspect the optional accelerated computation.  The generic branch has no
synthetic empty path or fallback certificate. -/
def fastComputation? (plan : InteractionPlan presentation actual expected card
    demand source target) :
    Option (familiesCwF.Tm PrimeContext
      (interactionComputationTy presentation source target)) :=
  match plan with
  | .generic => none
  | .licensed fast => some fast.computation

@[simp] theorem runRaw_generic (run : theory.Term → theory.Term → Output) :
    (InteractionPlan.generic (presentation := presentation)
      (actual := actual) (expected := expected) (card := card)
      (demand := demand) (source := source) (target := target)).runRaw run =
        run source target :=
  rfl

@[simp] theorem runRaw_licensed (run : theory.Term → theory.Term → Output)
    (fast : LicensedInteraction presentation actual expected card demand
      source target) :
    (InteractionPlan.licensed fast).runRaw run = run source target :=
  rfl

@[simp] theorem fastComputation?_generic :
    (InteractionPlan.generic (presentation := presentation)
      (actual := actual) (expected := expected) (card := card)
      (demand := demand) (source := source)
      (target := target)).fastComputation? = none :=
  rfl

@[simp] theorem fastComputation?_licensed
    (fast : LicensedInteraction presentation actual expected card demand
      source target) :
    (InteractionPlan.licensed fast).fastComputation? = some fast.computation :=
  rfl

end InteractionPlan

/-! ## Authority boundaries -/

/-- Gradual unknown cannot index a licensed interaction fast path. -/
theorem no_unknown_licensed_interaction {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (expected : Ty) (card : Card) (demand : ArrowMode)
    (source target : theory.Term) :
    ¬ Nonempty (LicensedInteraction presentation .unknown expected card demand
      source target) := by
  rintro ⟨fast⟩
  exact no_unknown_license ⟨fast.license, fast.license_actual⟩

/-- A definite shape conflict cannot index a licensed interaction fast path. -/
theorem no_shape_conflict_licensed_interaction {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (actual expected : Ty) (card : Card) (demand : ArrowMode)
    (source target : theory.Term)
    (conflict : consistent? actual expected = false) :
    ¬ Nonempty (LicensedInteraction presentation actual expected card demand
      source target) := by
  rintro ⟨fast⟩
  have flows := fast.license.flows
  rw [fast.license_actual, fast.license_expected, conflict] at flows
  cases flows

/-- A definite cardinality conflict cannot index a licensed interaction fast
path. -/
theorem no_cardinality_conflict_licensed_interaction {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (actual expected : Ty) (card : Card) (demand : ArrowMode)
    (source target : theory.Term)
    (conflict : modeFits (.grade card) demand = false) :
    ¬ Nonempty (LicensedInteraction presentation actual expected card demand
      source target) := by
  rintro ⟨fast⟩
  have fits := fast.license.fits
  rw [fast.license_card, fast.license_demand, conflict] at fits
  cases fits

/-- The conflict-cache law used at the interaction boundary is exactly the
gradual seam's refinement-persistence theorem. -/
theorem interaction_conflict_persists {actual actual' expected expected' : Ty}
    (actualRefines : Refines actual' actual)
    (expectedRefines : Refines expected' expected)
    (conflict : consistent? actual expected = false) :
    consistent? actual' expected' = false :=
  conflict_persists actualRefines expectedRefines conflict

/-! ## A concrete COMM canary -/

/-- Exact symbol evidence with deterministic cardinality. -/
def symbolDetLicense : OptLicense where
  actual := .prim .sym
  expected := .prim .sym
  card := .det
  demand := .grade .det
  actual_exact := by simp [exactTy]
  expected_exact := by simp [exactTy]
  flows := by simp
  fits := by simp [modeFits, Card.le, Card.toNat]

/-- The concrete Prime-internal COMM path carries both the seam license and
the occurrence-preserving interaction computation. -/
def licensedComm : LicensedInteraction rhoOccurrencePresentation
    (.prim .sym) (.prim .sym) .det (.grade .det) commSource commTarget where
  license := symbolDetLicense
  license_actual := rfl
  license_expected := rfl
  license_card := rfl
  license_demand := rfl
  computation := internalComm

theorem licensedComm_raw_reachable :
    Nonempty (rhoOccurrenceTheory.RewritePath commSource commTarget) :=
  licensedComm.raw_reachable

/-- Unknown evidence uses the generic plan at the same rho endpoints. -/
def unknownCommPlan : InteractionPlan rhoOccurrencePresentation
    .unknown (.prim .sym) .det (.grade .det) commSource commTarget :=
  .generic

@[simp] theorem unknownCommPlan_has_no_fastComputation :
    unknownCommPlan.fastComputation? = none :=
  rfl

/-- Unknown type evidence does not remove the ordinary rho execution. -/
theorem unknownCommPlan_raw_reachable :
    Nonempty (rhoOccurrenceTheory.RewritePath commSource commTarget) :=
  ⟨eraseInternalPath internalComm PUnit.unit⟩

/-- A conflicting exact expectation cannot reuse the COMM fast path under a
different type index. -/
theorem string_number_conflict_has_no_fastPath :
    ¬ Nonempty (LicensedInteraction rhoOccurrencePresentation
      (.prim .str) (.prim .num) .det (.grade .det) commSource commTarget) := by
  apply no_shape_conflict_licensed_interaction
  simp [consistent?]

#print axioms LicensedInteraction.raw_reachable
#print axioms LicensedInteraction.indices_rigid
#print axioms no_unknown_licensed_interaction
#print axioms no_shape_conflict_licensed_interaction
#print axioms interaction_conflict_persists
#print axioms licensedComm_raw_reachable
#print axioms unknownCommPlan_raw_reachable
#print axioms string_number_conflict_has_no_fastPath

end Mettapedia.Languages.MeTTa.Prime.NativeInteractionSeam
