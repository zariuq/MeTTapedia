import Mettapedia.GSLT.Logic.ProgrammableSpaceEvidenceControls

/-!
# Two proof paths can carry one random observation

In the reachability source, the edges are fixed data and the selected far query
is one Boolean observation. Both derived answers require that same query input.
Across the two equiprobable Boolean trials their event indicators are equal and
nonconstant. Independence would require twice the joint event count to equal
the product of the marginal counts; the actual counts refute that equation.

This is a concrete dependence witness, not a claim that shared provenance alone
decides independence in every probability model. Conversely, disjoint origin
names alone do not supply a probabilistic independence theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceEvidence.Controls

attribute [local instance] Finite.membership

/-- The query observation varies; the authored edge data remain available. -/
def queryTrial (outcome : Bool) : Origin → Bool
  | .farQuery => outcome
  | _ => true

def acceptedInTrial {n : Nat} (receipt : Receipt (source n)) (outcome : Bool) : Bool :=
  receipt.origins.all (queryTrial outcome)

@[simp] theorem direct_trial (n : Nat) (outcome : Bool) :
    acceptedInTrial (direct n) outcome = outcome := by
  cases outcome <;> rfl

@[simp] theorem indirect_trial (n : Nat) (outcome : Bool) :
    acceptedInTrial (indirect n) outcome = outcome := by
  cases outcome <;> rfl

def trialCount (event : Bool → Bool) : Nat := ([false, true].filter event).length

theorem shared_query_event_counts (n : Nat) :
    trialCount (acceptedInTrial (direct n)) = 1 ∧
      trialCount (acceptedInTrial (indirect n)) = 1 ∧
      trialCount (fun outcome => acceptedInTrial (direct n) outcome &&
        acceptedInTrial (indirect n) outcome) = 1 := by
  simp [trialCount]

/-- The independence equation for the uniform two-trial experiment is false. -/
theorem shared_query_is_not_independent (n : Nat) :
    2 * trialCount (fun outcome => acceptedInTrial (direct n) outcome &&
      acceptedInTrial (indirect n) outcome) ≠
    trialCount (acceptedInTrial (direct n)) * trialCount (acceptedInTrial (indirect n)) := by
  obtain ⟨directCount, indirectCount, jointCount⟩ := shared_query_event_counts n
  rw [directCount, indirectCount, jointCount]
  decide

theorem shared_query_remains_observable (n : Nat) :
    acceptedInTrial (direct n) false ≠ acceptedInTrial (direct n) true := by
  exact Bool.false_ne_true

end Mettapedia.GSLT.ProgrammableSpaceEvidence.Controls
