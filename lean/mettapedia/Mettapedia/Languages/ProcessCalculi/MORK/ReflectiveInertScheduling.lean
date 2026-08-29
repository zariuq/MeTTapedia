import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveInertFiring
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Scheduling after an inert reflective probe

This interface composes remove-before-interpret semantics without expanding
the concrete space produced by the probe.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Conformance.Computable
open ReflectiveComputable
open WQComputable

/-- If a directive has no input match, the next scheduled step is determined
by erasing exactly that decoded candidate from the previous support list. -/
theorem cReflectiveSourceWorkQueueStep_after_inert
    (space : List Atom) (inert next : SourceExecFact)
    (candidates : List SourceExecFact)
    (decoded : extractSupportedSourceExecFact inert.atom = some inert)
    (noMatches :
      cmatchInputSpec [] (inert.atom :: space.erase inert.atom)
        inert.rule.input = [])
    (supported : cSupportedSourceExecFacts space = candidates)
    (nextSelected : selectNextScheduled (candidates.erase inert) = some next) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (cFireReflectiveSourceExecFact space inert) =
      some
        (cFireReflectiveSourceExecFact
          (cFireReflectiveSourceExecFact space inert) next) := by
  have inertEq :=
    cFireReflectiveSourceExecFact_eq_erase_of_no_matches
      space inert noMatches
  rw [inertEq]
  simp only [cReflectiveSourceWorkQueueStep,
    cSupportedSourceExecFacts_erase space inert decoded, supported,
    nextSelected]

/-- Candidate support after an inert probe is computed algebraically from the
previous exact interface; the concrete post-state need not be normalized. -/
theorem cSupportedSourceExecFacts_after_inert
    (space : List Atom) (inert : SourceExecFact)
    (candidates : List SourceExecFact)
    (decoded : extractSupportedSourceExecFact inert.atom = some inert)
    (noMatches :
      cmatchInputSpec [] (inert.atom :: space.erase inert.atom)
        inert.rule.input = [])
    (supported : cSupportedSourceExecFacts space = candidates) :
    cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFact space inert) =
      candidates.erase inert := by
  rw [cFireReflectiveSourceExecFact_eq_erase_of_no_matches
      space inert noMatches,
    cSupportedSourceExecFacts_erase space inert decoded, supported]

/-- Two successive unsuccessful probes form two genuine scheduler steps and
thread the candidate interface by exact erasure before the fallback step. -/
theorem cReflectiveSourceWorkQueueStep_after_two_inert
    (space : List Atom) (first second next : SourceExecFact)
    (candidates : List SourceExecFact)
    (firstDecoded : extractSupportedSourceExecFact first.atom = some first)
    (firstNoMatches :
      cmatchInputSpec [] (first.atom :: space.erase first.atom)
        first.rule.input = [])
    (supported : cSupportedSourceExecFacts space = candidates)
    (secondSelected :
      selectNextScheduled (candidates.erase first) = some second)
    (secondDecoded : extractSupportedSourceExecFact second.atom = some second)
    (secondNoMatches :
      cmatchInputSpec []
          (second.atom ::
            (cFireReflectiveSourceExecFact space first).erase second.atom)
          second.rule.input = [])
    (nextSelected :
      selectNextScheduled ((candidates.erase first).erase second) =
        some next) :
    cReflectiveSourceWorkQueueStep .leaveInert
        (cFireReflectiveSourceExecFact space first) =
        some
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact space first) second) ∧
      cReflectiveSourceWorkQueueStep .leaveInert
        (cFireReflectiveSourceExecFact
          (cFireReflectiveSourceExecFact space first) second) =
        some
          (cFireReflectiveSourceExecFact
            (cFireReflectiveSourceExecFact
              (cFireReflectiveSourceExecFact space first) second) next) := by
  constructor
  · exact cReflectiveSourceWorkQueueStep_after_inert
      space first second candidates firstDecoded firstNoMatches supported
      secondSelected
  · exact cReflectiveSourceWorkQueueStep_after_inert
      (cFireReflectiveSourceExecFact space first) second next
      (candidates.erase first) secondDecoded secondNoMatches
      (cSupportedSourceExecFacts_after_inert space first candidates
        firstDecoded firstNoMatches supported)
      nextSelected

/-- Execute a finite list of already-selected reflective directives. -/
def cFireReflectiveSourceExecFacts :
    List Atom → List SourceExecFact → List Atom
  | space, [] => space
  | space, directive :: rest =>
      cFireReflectiveSourceExecFacts
        (cFireReflectiveSourceExecFact space directive) rest

/-- Erase the same scheduled occurrences from an exact candidate inventory. -/
def eraseSourceExecFacts :
    List SourceExecFact → List SourceExecFact → List SourceExecFact
  | candidates, [] => candidates
  | candidates, directive :: rest =>
      eraseSourceExecFacts (candidates.erase directive) rest

/-- Proof-relevant certificate for a finite chain of unsuccessful probes.
Each probe must be the physical scheduler minimum of the current inventory,
decode exactly, and have no input match in the actual threaded state. -/
inductive CReflectiveInertProbePlan :
    (space : List Atom) →
    (candidates probes : List SourceExecFact) → Prop where
  | nil (space candidates) :
      CReflectiveInertProbePlan space candidates []
  | cons (space candidates probe rest)
      (decoded : extractSupportedSourceExecFact probe.atom = some probe)
      (noMatches :
        cmatchInputSpec [] (probe.atom :: space.erase probe.atom)
          probe.rule.input = [])
      (selected : selectNextScheduled candidates = some probe)
      (tail :
        CReflectiveInertProbePlan
          (cFireReflectiveSourceExecFact space probe)
          (candidates.erase probe) rest) :
      CReflectiveInertProbePlan space candidates (probe :: rest)

/-- Package one unsuccessful scheduled probe without exposing the dependent
constructor bookkeeping to each concrete language instance. -/
theorem CReflectiveInertProbePlan.singleton
    (space : List Atom) (candidates : List SourceExecFact)
    (probe : SourceExecFact)
    (decoded : extractSupportedSourceExecFact probe.atom = some probe)
    (noMatches :
      cmatchInputSpec [] (probe.atom :: space.erase probe.atom)
        probe.rule.input = [])
    (selected : selectNextScheduled candidates = some probe) :
    CReflectiveInertProbePlan space candidates [probe] :=
  .cons space candidates probe [] decoded noMatches selected
    (.nil (cFireReflectiveSourceExecFact space probe)
      (candidates.erase probe))

/-- Prefix one unsuccessful scheduled probe to an already established plan. -/
theorem CReflectiveInertProbePlan.prepend
    (space : List Atom) (candidates : List SourceExecFact)
    (probe : SourceExecFact) (rest : List SourceExecFact)
    (decoded : extractSupportedSourceExecFact probe.atom = some probe)
    (noMatches :
      cmatchInputSpec [] (probe.atom :: space.erase probe.atom)
        probe.rule.input = [])
    (selected : selectNextScheduled candidates = some probe)
    (tail : CReflectiveInertProbePlan
      (cFireReflectiveSourceExecFact space probe)
      (candidates.erase probe) rest) :
    CReflectiveInertProbePlan space candidates (probe :: rest) :=
  .cons space candidates probe rest decoded noMatches selected tail

/-- An inert-probe plan is one genuine state-threaded execution path. -/
theorem CReflectiveInertProbePlan.reachable
    {space : List Atom} {candidates probes : List SourceExecFact}
    (plan : CReflectiveInertProbePlan space candidates probes)
    (supported : cSupportedSourceExecFacts space = candidates) :
    CReflectiveReachable .leaveInert probes.length space
      (cFireReflectiveSourceExecFacts space probes) := by
  induction plan with
  | nil => exact .refl
  | cons space candidates probe rest decoded noMatches selected tail induction =>
      exact CReflectiveReachable.step
        (middle := cFireReflectiveSourceExecFact space probe)
        (by simp only [cReflectiveSourceWorkQueueStep, supported, selected])
        (induction
          (cSupportedSourceExecFacts_after_inert space probe candidates
            decoded noMatches supported))

/-- The same plan computes its final scheduler inventory by occurrence
erasure; no concrete execution state is normalized. -/
theorem CReflectiveInertProbePlan.supported_final
    {space : List Atom} {candidates probes : List SourceExecFact}
    (plan : CReflectiveInertProbePlan space candidates probes)
    (supported : cSupportedSourceExecFacts space = candidates) :
    cSupportedSourceExecFacts
        (cFireReflectiveSourceExecFacts space probes) =
      eraseSourceExecFacts candidates probes := by
  induction plan with
  | nil => exact supported
  | cons space candidates probe rest decoded noMatches selected tail induction =>
      exact induction
        (cSupportedSourceExecFacts_after_inert space probe candidates
          decoded noMatches supported)

/-- Append one concrete scheduler transition to an existing finite path.
The fuel index records an upper bound, so the reflexive case retains its
available fuel before accounting for the appended transition. -/
theorem CReflectiveReachable.then_step
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source middle target : List Atom}
    (reachable : CReflectiveReachable policy fuel source middle)
    (moved : cReflectiveSourceWorkQueueStep policy middle = some target) :
    CReflectiveReachable policy (fuel + 1) source target := by
  induction reachable with
  | refl => exact .step moved .refl
  | step first _ induction => exact .step first (induction moved)

#print axioms cReflectiveSourceWorkQueueStep_after_inert
#print axioms cSupportedSourceExecFacts_after_inert
#print axioms cReflectiveSourceWorkQueueStep_after_two_inert
#print axioms CReflectiveInertProbePlan.singleton
#print axioms CReflectiveInertProbePlan.prepend
#print axioms CReflectiveInertProbePlan.reachable
#print axioms CReflectiveInertProbePlan.supported_final
#print axioms CReflectiveReachable.then_step

end Mettapedia.Languages.ProcessCalculi.MORK
