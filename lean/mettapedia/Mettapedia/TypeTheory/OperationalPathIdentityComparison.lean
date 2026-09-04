import Mettapedia.TypeTheory.IdentityObservationComparison
import Mettapedia.TypeTheory.ResponseIndexedResultFamily
import Mettapedia.GSLT.Core.SemanticInvariant

/-!
# Operational paths and identity observations

Finite execution paths form a reflexive, proof-relevant route layer, but they
are not automatically identity proofs.  A semantic invariant supplies a sound
map from every execution path to equality of denotations because its selected
meaning is conserved along each step.

The dependent reflective protocol separates the notions concretely.  It has a
path from the initial state to a completed state, so execution paths do not
reflect equality of protocol states and support no sound comparison to exact
state equality.  Its constant denotation is a valid equality observation,
whereas the visible completion bit is not invariant because computation
changes it.

Thus extensional equality can read operational paths only through an explicitly
conserved denotation.  It is not obtained by reclassifying state transition as
identity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.OperationalPathIdentityComparison

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol
open Mettapedia.GSLT.Dynamics.IndexedPolynomialProtocol.VaryingCanary
open Mettapedia.GSLT.Dynamics.DependentReflectiveProtocolComparison
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.IdentityRouteCapabilities
open Mettapedia.TypeTheory.IdentityObservationComparison

universe uTerm uMeaning

/-! ## Generic comparison through a conserved denotation -/

/-- Finite execution paths, with proposition-valued support obtained by
forgetting which path occurred. -/
def executionLayer (system : GSLT.{uTerm}) : Layer system.Term where
  Route := ExecutionPath system
  refl := fun term => .refl term
  Support := fun source target => Nonempty (ExecutionPath system source target)
  forget := fun path => ⟨path⟩

/-- Every semantic invariant is a sound equality observation of the execution
route layer. -/
def invariantComparison {system : GSLT.{uTerm}} {Meaning : Type uMeaning}
    (invariant : SemanticInvariant system Meaning) :
    Comparison (executionLayer system) invariant.denote where
  toObservedEquality path := invariant.executionPath_eq path

/-- The comparison really reads a primitive singleton path by the invariant's
step-conservation law. -/
theorem invariantComparison_singleton
    {system : GSLT.{uTerm}} {Meaning : Type uMeaning}
    (invariant : SemanticInvariant system Meaning)
    {source target : system.Term} (step : system.Step source target) :
    (invariantComparison invariant).toObservedEquality
        (.cons ⟨step⟩ (.refl target)) = invariant.rewrite step := by
  apply Subsingleton.elim

/-! ## Dependent reflective protocol controls -/

/-- One real state-changing execution path. -/
def unitExecutionPath :
    ExecutionPath (lts codedQuery) Phase.start Phase.unitDone :=
  .cons ⟨unitEvent.step⟩ (.refl Phase.unitDone)

/-- State-changing execution does not reflect equality of exact endpoints. -/
theorem protocolExecution_not_endpoint_reflecting :
    ¬ EndpointReflection (executionLayer (lts codedQuery)) := by
  intro reflects
  have impossible : Phase.start = Phase.unitDone :=
    reflects unitExecutionPath
  cases impossible

/-- Consequently there is no sound route-to-equality comparison using exact
protocol state as the observation. -/
theorem no_exact_state_equality_comparison :
    ¬ Nonempty
      (Comparison (executionLayer (lts codedQuery)) (id : Phase → Phase)) := by
  rintro ⟨comparison⟩
  have impossible : Phase.start = Phase.unitDone :=
    comparison.toObservedEquality unitExecutionPath
  cases impossible

/-- The independently selected constant denotation is conserved and therefore
does yield a sound, deliberately coarse equality observation. -/
def constantDenotationComparison :
    Comparison (executionLayer (lts codedQuery))
      codedDenotation.denote :=
  invariantComparison codedDenotation

theorem constantDenotation_reads_unit_path :
    constantDenotationComparison.toObservedEquality unitExecutionPath = rfl :=
  Subsingleton.elim _ _

/-- The visible completion bit changes along the unit response step, so no
semantic invariant can have exactly that denotation map. -/
theorem completion_is_not_invariant :
    ¬ ∃ invariant : SemanticInvariant (lts codedQuery) Bool,
      invariant.denote = completion := by
  rintro ⟨invariant, denotationEquality⟩
  have conserved := invariant.rewrite unitEvent.step
  rw [denotationEquality] at conserved
  exact Bool.false_ne_true conserved

/-- Equivalently, completion cannot be a sound equality observation of all
execution paths. -/
theorem no_completion_equality_comparison :
    ¬ Nonempty
      (Comparison (executionLayer (lts codedQuery)) completion) := by
  rintro ⟨comparison⟩
  have impossible : false = true :=
    comparison.toObservedEquality unitExecutionPath
  exact Bool.false_ne_true impossible

/-- The complete boundary: operational paths are real routes but not identity
proofs; only independently conserved denotations give sound extensional
equality readouts. -/
theorem operational_path_identity_boundary :
    Nonempty (ExecutionPath (lts codedQuery) Phase.start Phase.unitDone) /\
      (¬ EndpointReflection (executionLayer (lts codedQuery))) /\
      (¬ Nonempty
        (Comparison (executionLayer (lts codedQuery)) (id : Phase → Phase))) /\
      Nonempty
        (Comparison (executionLayer (lts codedQuery))
          codedDenotation.denote) /\
      (¬ ∃ invariant : SemanticInvariant (lts codedQuery) Bool,
        invariant.denote = completion) /\
      ¬ Nonempty
        (Comparison (executionLayer (lts codedQuery)) completion) :=
  ⟨⟨unitExecutionPath⟩,
    protocolExecution_not_endpoint_reflecting,
    no_exact_state_equality_comparison,
    ⟨constantDenotationComparison⟩,
    completion_is_not_invariant,
    no_completion_equality_comparison⟩

#print axioms invariantComparison_singleton
#print axioms protocolExecution_not_endpoint_reflecting
#print axioms no_exact_state_equality_comparison
#print axioms constantDenotationComparison
#print axioms completion_is_not_invariant
#print axioms no_completion_equality_comparison
#print axioms operational_path_identity_boundary

end Mettapedia.TypeTheory.OperationalPathIdentityComparison
