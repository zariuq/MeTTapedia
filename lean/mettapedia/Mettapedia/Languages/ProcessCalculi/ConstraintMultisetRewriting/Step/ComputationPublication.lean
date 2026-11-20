import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationRealization

/-!
# Qualified computation begins at actual typed publications

Principal and residual source applications supply real result states. Exact
answer coverage makes their published knowledge solvable. A selected present
output then starts the computation profile without assuming that an arbitrary
already-typed implementation realizes the source definition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull TypedPublication
open AlgebraicParallel NativeTypesOnTheStep.Computing ConversionCoherence

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

theorem publication_consistent {state : State S.R Nat}
    (application : Application S.levels Nat state)
    (accepted : (realizationStep S.levels Nat).Admits application) :
    (frames S.levels).Solvable ((realizationStep S.levels Nat).result application accepted).knowledge := by
  obtain ⟨observer, solution, solved⟩ := (realizationStep S.levels Nat).solvable_information accepted
  obtain ⟨further, models, _⟩ := application.basis.covers solution solved
  exact ⟨observer, further, models⟩

def Configuration.fromPublication {state : State S.R Nat}
    (application : Application S.levels Nat state)
    (accepted : (realizationStep S.levels Nat).Admits application) (active : Nat)
    (present : active ∈ ((realizationStep S.levels Nat).result application accepted).present) :
    Configuration (S := S) :=
  ⟨(realizationStep S.levels Nat).result application accepted, active, present,
    publication_consistent application accepted⟩

theorem publication_computes (qualified : Qualified S) (presentation : SchemaPresentation S.R)
    {state : State S.R Nat} (application : Application S.levels Nat state)
    (accepted : (realizationStep S.levels Nat).Admits application) (active : Nat)
    (present : active ∈ ((realizationStep S.levels Nat).result application accepted).present)
    {value : Tm Head application.target.arity} :
    Answer S.R (Configuration.fromPublication application accepted active present).code value ↔
      ∃ run : (step S.levels Nat).toStep.Run ((realizationStep S.levels Nat).result application accepted),
        ∃ profile : RunProfile qualified presentation
          (Configuration.fromPublication application accepted active present) run,
          profile.execution.term = value ∧ ConstructorSystem.Normal S.R profile.execution.term :=
  full_answers_iff qualified presentation

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProfile.publication_computes
