import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullJoinSolvers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullNonVacuity

/-!
# The later solvers in the point package: controls

Every run below executes an actual solver of R86 or R90 in the point package, evaluated by the
kernel, and feeds its decision to the join through the solver's own theorem from
`DependentFullJoinSolvers`.

* **The pattern store** `m(x) ≐ n(x)` is solved by R86's normalizing solver and by R90's Π solver
  (whose fallbacks are the identity and fragment rounds); the store `F(x) ≐ y` is refuted by both.
* **Rotation on a translated telescope.** Over three unary metavariables `a, b, c` (newest first), the
  store `c(x) ≐ x` asks for the deepest one. R77's full solver is stuck on it (`deep_full_suspended`):
  its rules read only the two newest declarations. R86's permuting solver rotates `c` to the newest
  position and solves it (`deep_permuting_commit`); the rotated telescope is again translated, so the
  decision is a decision in the fibre (`deep_in_fibre`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.SolverControls

open _root_.CategoryTheory
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open ContextualDependentFibre ContextualDependentFibre.Controls Translation
open PointPackage NonVacuity

/-- The evaluator without root steps covers every root step of the package. -/
theorem rootComplete {n : Nat} (term : Tower.Tm n) :
    (fun _ => none : ExecutableReduction.RootEvaluator setting.R) term = none →
      ∀ target, ¬ setting.R.computation.step term target :=
  fun _ _ impossible => False.elim impossible

/-- R86's normalizing solver in the point package. -/
def normalizing : ContextualDependentWorklist.Solver setting.levels :=
  ContextualDependentNormalizing.normalizingSolver (S := setting) rigid complete facts roots heads algebra declared
    choices reducer (fun _ => none) rootComplete point_normalizes certifyNormal headTypingUnique 16

/-- R86's permuting solver in the point package. -/
def permuting : ContextualDependentWorklist.Solver setting.levels :=
  ContextualDependentPermutation.permutingSolver (S := setting) rigid complete facts roots heads algebra declared
    choices reducer (fun _ => none) point_normalizes certifyNormal headTypingUnique 16

/-- R90's Π solver in the point package. -/
def piSolver : ContextualDependentWorklist.Solver setting.levels :=
  ContextualDependentFragment.piSolver (S := setting) facts roots heads algebra declared choices reducer rigid complete
    (fun _ => none) point_normalizes certifyNormal headTypingUnique rootComplete 16

theorem decided_of_commit {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {outcome : ContextualDependentWorklist.Outcome setting.levels original} (committed : outcome.readout = .commit) :
    outcome.Decided := by
  cases outcome with
  | solved _ _ => trivial
  | refuted _ => trivial
  | stuck _ => cases committed
  | cutoff _ => cases committed

theorem decided_of_refuted {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {outcome : ContextualDependentWorklist.Outcome setting.levels original} (refuted : outcome.readout = .refuted) :
    outcome.Decided := by
  cases outcome with
  | solved _ _ => trivial
  | refuted _ => trivial
  | stuck _ => cases refuted
  | cutoff _ => cases refuted

/-! ## The pattern store and the refuted store -/

theorem pattern_normalizing_commit :
    (ContextualDependentWorklist.run normalizing (Ψ.store (patternStore star)) 2).readout = .commit := by
  decide +kernel

theorem pattern_pi_commit :
    (ContextualDependentWorklist.run piSolver (Ψ.store (patternStore star)) 2).readout = .commit := by
  decide +kernel

theorem outside_normalizing_refuted :
    (ContextualDependentWorklist.run normalizing (Ψ.store outsideStore) 2).readout = .refuted := by
  decide +kernel

theorem outside_pi_refuted :
    (ContextualDependentWorklist.run piSolver (Ψ.store outsideStore) 2).readout = .refuted := by
  decide +kernel

/-- **R90's Π solver decides the pattern store in the fibre.** -/
theorem pattern_pi_in_fibre :
    DecidedInFibre (S := setting) facts roots heads church names realization (patternStore star) :=
  decidedInFibre_of_pi (S := setting) facts roots heads church names realization rigid complete algebra declared
    choices reducer (fun _ => none) rootComplete point_normalizes certifyNormal headTypingUnique _ 16 2
    chainsSilent_none (decided_of_commit pattern_pi_commit)

/-- **R86's normalizing solver decides the refuted store in the fibre.** -/
theorem outside_normalizing_in_fibre :
    DecidedInFibre (S := setting) facts roots heads church names realization outsideStore :=
  decidedInFibre_of_normalizing (S := setting) facts roots heads church names realization rigid complete algebra
    declared choices reducer (fun _ => none) rootComplete point_normalizes certifyNormal headTypingUnique _ 16 2
    chainsSilent_none (decided_of_refuted outside_normalizing_refuted)

/-! ## Rotation on a translated telescope -/

/-- Three unary metavariables `a, b, c`, newest first. -/
abbrev triple : List (Binding.MetaArity pointSig) := [([star], star), ([star], star), ([star], star)]

/-- `c(x)`, the deepest metavariable applied to its parameter. -/
def deepLeft : Obs triple := occurrence triple ⟨2, by simp⟩

/-- `x`. -/
def deepRight : Obs triple := ⟨[star], star, .var .zero⟩

/-- `c(x) ≐ x`. -/
def deepStore : EquationStore (Obs triple) := [(deepLeft, deepRight)]

/-- **R77's full solver is stuck**: its rules read only the two newest declarations. -/
theorem deep_full_suspended :
    (ContextualDependentWorklist.run full (Ψ.store deepStore) 4).readout = .suspended := by
  decide +kernel

/-- **R86's permuting solver rotates `c` to the newest position and solves it.** -/
theorem deep_permuting_commit :
    (ContextualDependentWorklist.run permuting (Ψ.store deepStore) 2).readout = .commit := by
  decide +kernel

/-- **The rotation's decision is a decision in the fibre.** -/
theorem deep_in_fibre : DecidedInFibre (S := setting) facts roots heads church names realization deepStore :=
  decidedInFibre_of_permuting (S := setting) facts roots heads church names realization rigid complete algebra
    declared choices reducer (fun _ => none) point_normalizes certifyNormal headTypingUnique _ 16 2
    (decided_of_commit deep_permuting_commit)

end DependentFull.SolverControls

#print axioms DependentFull.SolverControls.pattern_normalizing_commit
#print axioms DependentFull.SolverControls.pattern_pi_commit
#print axioms DependentFull.SolverControls.outside_normalizing_refuted
#print axioms DependentFull.SolverControls.outside_pi_refuted
#print axioms DependentFull.SolverControls.pattern_pi_in_fibre
#print axioms DependentFull.SolverControls.outside_normalizing_in_fibre
#print axioms DependentFull.SolverControls.deep_full_suspended
#print axioms DependentFull.SolverControls.deep_permuting_commit
#print axioms DependentFull.SolverControls.deep_in_fibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
