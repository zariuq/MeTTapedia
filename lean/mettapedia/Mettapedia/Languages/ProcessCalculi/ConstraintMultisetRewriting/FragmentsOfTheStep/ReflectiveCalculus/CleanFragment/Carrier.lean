import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.Encodings.FirstHalf

/-!
# The closed-row domain of the existing rho transform program

Cleanliness is stated on actual target knowledge and row observations. It
does not assume a source process, a source run, or an operational simulation.
A certificate provides a closed value for each present occurrence, consistent
knowledge, and determination of that value at every ground solution. Absent
identities and unused declarations are unrestricted.

The finite inventory constructs its source readback. This independently
described domain is exactly the domain of the existing closed-row rho
representation. Maximality is relative to this representation discipline and
the fixed four-rule program; it is not maximality among all transform variants
or all possible notions of behavioural equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag
open ByInstantiation (sig G Grounding GroundSolves Closed Similar)

abbrev RawState := ByInstantiation.State

/-- Concrete row evidence at the actual target state. The value function is
inspected only at finitely many present occurrences by the readback. -/
structure Certificate (state : RawState) where
  value : Nat → G [] .pr
  consistent : ∃ point : Grounding state.frame, GroundSolves point state.knowledge
  determined : ∀ point : Grounding state.frame, GroundSolves point state.knowledge →
    ∀ occurrence ∈ state.present, ∃ term : G [] .pr,
      instantiateObservation point (state.label occurrence) = observe term ∧ Similar term (value occurrence)
  closed : ∀ occurrence ∈ state.present, Closed (value occurrence)

/-- The domain is a predicate on the original state type. -/
def Clean (state : RawState) : Prop := Nonempty (Certificate state)

variable {state : RawState}

/-- Multiplicities are preserved when complete row meanings are assembled. -/
def Certificate.inventory (certificate : Certificate state) : Bag :=
  ⟨ByInstantiation.inventoryOf state.present certificate.value, by
    intro pattern member
    obtain ⟨occurrence, present, inside⟩ := Multiset.mem_sum.mp member
    exact (fromProcess (ByInstantiation.rowProcess (certificate.value occurrence)
      (certificate.closed occurrence present))).2 pattern inside⟩

/-- Executable finite readback when a row certificate is supplied. General
membership in `Clean` is not asserted decidable. -/
def Certificate.readback (certificate : Certificate state) : RhoProcess := toProcess certificate.inventory

/-- The actual readback meets the complete existing representation relation. -/
theorem Certificate.represents (certificate : Certificate state) :
    ByInstantiation.RepresentsBy state certificate.readback certificate.value := by
  refine ⟨certificate.consistent, certificate.determined, certificate.closed, ?_⟩
  rw [Certificate.readback, fromProcess_toProcess]
  rfl

/-- Existing represented rows supply the local certificate fields directly. -/
def Certificate.ofRepresentation {process : RhoProcess} {value : Nat → G [] .pr}
    (represented : ByInstantiation.RepresentsBy state process value) : Certificate state :=
  ⟨value, represented.solvable, represented.determined, represented.closed⟩

theorem clean_of_represents {process : RhoProcess} (represented : ByInstantiation.Represents state process) :
    Clean state := by
  obtain ⟨value, represented⟩ := represented
  exact ⟨Certificate.ofRepresentation represented⟩

/-- Exact domain characterization: the local target criterion constructs a
source process, and every state with the declared source representation has
that criterion. It is not just the literal image of the compiler. -/
theorem clean_iff_representable : Clean state ↔ ∃ process : RhoProcess, ByInstantiation.Represents state process := by
  constructor
  · rintro ⟨certificate⟩
    exact ⟨certificate.readback, certificate.value, certificate.represents⟩
  · rintro ⟨process, represented⟩
    exact clean_of_represents represented

/-- A represented state has exactly one equational source meaning. -/
theorem Certificate.readback_equations (certificate : Certificate state) {process : RhoProcess}
    (represented : ByInstantiation.Represents state process) :
    rhoProcessEquations.r certificate.readback process :=
  ByInstantiation.represents_functional ⟨certificate.value, certificate.represents⟩ represented

theorem Certificate.inventory_independent (first second : Certificate state) : first.inventory = second.inventory := by
  have equal := first.readback_equations ⟨second.value, second.represents⟩
  have bags := (fromProcess_eq_iff first.readback second.readback).mpr equal
  simpa only [Certificate.readback, fromProcess_toProcess] using bags

/-- This is the greatest domain under the specified closed-row
representation criterion. Other observations may justify different domains. -/
theorem represented_domain_is_greatest (domain : Set RawState)
    (supported : ∀ state ∈ domain, ∃ process : RhoProcess, ByInstantiation.Represents state process) :
    domain ⊆ {state | Clean state} := by
  intro state member
  exact clean_iff_representable.mpr (supported state member)

/-- The greatest domain is itself supported, rather than merely an upper
bound on other candidates. The criterion is the existing row representation;
its equivalence to the independent local fields is proved above. -/
theorem clean_domain_isGreatest :
    IsGreatest {domain : Set RawState | ∀ state ∈ domain,
      ∃ process : RhoProcess, ByInstantiation.Represents state process} {state | Clean state} := by
  constructor
  · intro state clean
    exact clean_iff_representable.mp clean
  · intro domain supported
    exact represented_domain_is_greatest domain supported

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.ReflectiveCalculus.CleanFragment
