import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.LevelConstraints
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CumulativeCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CrossStoreLevels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PatternSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PatternSolverControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.OccursNull
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.StepConnection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.SymbolicLevels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.DependentFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.LevelLowering
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PrincipalAlignment
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.FixedPointAnswers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CodomainNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CodomainNarrowingControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerTransitions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerDecision
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MillerControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PostponingFragments
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PostponingFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MeetNarrowing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.MeetSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.Overview

/-!
# Unification with level variables: exact runs with three outcomes

**The theorem.** A solver changes a store of equations by transitions along morphisms of frames.
Each transition is exact: the solutions of the store before are exactly the composites of the
solutions after. So every run is exact, and a run that stops is one of three things:

* **solved**: the residual is empty and the composite morphism is a principal answer; a principal
  answer is exactly an exact transition to the empty store; with an epimorphic answer it is the
  initial solution (`ExactTransitions`);
* **refuted**: the store has no solution, and the refutation carries its reason as data (clash,
  levels, or no well-founded solution);
* **postponed**: equations remain; they are the knowledge, and the solution set is unchanged.

Nothing claims that a run ends solved or refuted. Where a store is solvable and has no principal
answer, every run that stops, stops postponed, in every frames instance, including the dependent
fibre of the tree (`DependentFibre.cross_postponed`).

In the core's own terms (`PrincipalAlignment`): solved is `Frames.Principal` and `FactorsOn` over all
terms; the answer of any exact run, postponed or not, `FactorsOn` every set of terms; initial is
`Principal` with a unique factor. For the solver of cumulative codes a solved answer is idempotent
and the solutions are exactly the assignments it fixes, an equalizer with a canonical factor
(`FixedPointAnswers`).

**Levels.** Levels are variables, successor and maximum over ℕ; cumulativity is the constraint
`u ≤ v`; satisfiability of a store of level constraints is decided, soundly and completely, through a
small-model bound (`LevelConstraints`), and by lowering to the greatest bounded solution, the solver
to run, with polynomially many lowering steps in the unary size (`LevelLowering`, `lowerSat_cost`). Level constraints are equations of the store
(`CumulativeCodes.levelEquation`), refuted at every valuation when unsatisfiable, dropped when
entailed, postponed otherwise (`SymbolicLevels`).

**A model with cumulative universes** (`CumulativeCodes`): second-order type codes typed in
cumulative universes with level variables. Its solver's transitions are exact, they terminate on
every store, and on the uniform pattern fragment every store is decided: principal answer or no
solution (`PatternSolver`). The cross store `X par ≐ Y par`, with `X` at `a` and `Y` at `b`, has a
principal answer exactly when `b ≤ a`; with the cumulativity constraint `a ≤ b` alone that is a
postponed level constraint, and the answer `U : Sort b ⟶ Sort a` is principal under it
(`CrossStoreLevels`).

**Occurs.** `X ≐ arr X gnd` has no well-founded solution and exactly one rational one
(`OccursNull.rational_solution_unique`); every clash has no solution in either model
(`OccursNull.clash_in_trees`).

**The step.** Postponed equations are the knowledge after a settlement along the run, on every
`Step.Standard` whose settlement is a literal solver run (`standard_knowledge_residual`), such as the
settled step of any solver (`Settled.knowledge_is_residual`); preparation's `solvable` is the
residual's solvability; a run's verdict is solved, refused, or undecided, and undecided is neither of
the others (`StepConnection`).
-/

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

#print axioms Exact.trans
#print axioms exact_nil_iff_principal
#print axioms Principal.initial
#print axioms Exact.solvable_iff
#print axioms Exact.entails_iff
#print axioms Solver.Reaches.exact
#print axioms solved_principal
#print axioms solved_initial
#print axioms refuted_none
#print axioms postponed_exact
#print axioms postponed_of_solvable_no_principal
#print axioms LevelStore.satisfiable_iff_bounded
#print axioms decideSat_iff
#print axioms LevelStore.entails_iff
#print axioms CumulativeCodes.Ty.act
#print axioms CumulativeCodes.solves_levelEquation
#print axioms CumulativeCodes.Cross.principal_iff
#print axioms CumulativeCodes.Cross.no_principal
#print axioms CumulativeCodes.Cross.answer_principal
#print axioms CumulativeCodes.Cross.postponed_level_constraint
#print axioms CumulativeCodes.Cross.plain_principality_fails
#print axioms CumulativeCodes.Rule.exact
#print axioms CumulativeCodes.Refutes.sound
#print axioms CumulativeCodes.rules_terminate
#print axioms CumulativeCodes.progress
#print axioms CumulativeCodes.decided
#print axioms CumulativeCodes.principal_or_unsolvable
#print axioms CumulativeCodes.Cross.cross_stopped
#print axioms CumulativeCodes.Cross.cross_solved_at_equal_levels
#print axioms OccursNull.loopTree_unique
#print axioms OccursNull.loopTree_rational
#print axioms OccursNull.loopTree_not_finite
#print axioms OccursNull.rational_solution
#print axioms OccursNull.well_founded_refutation
#print axioms knowledge_keeps_solutions
#print axioms standard_knowledge_residual
#print axioms Settled.knowledge_is_residual
#print axioms CumulativeCodes.SettledControls.solved_knowledge
#print axioms CumulativeCodes.SettledControls.cross_knowledge
#print axioms OccursNull.rational_solution_unique
#print axioms OccursNull.clash_in_trees
#print axioms lowerSat_cost
#print axioms prepares_iff_residual
#print axioms CumulativeCodes.solver_literal
#print axioms CumulativeCodes.Cross.undecided_solvable
#print axioms CumulativeCodes.Cross.undecided_unsolvable
#print axioms CumulativeCodes.refuted_everywhere
#print axioms CumulativeCodes.drop_entailed
#print axioms DependentFibre.exact_iff_update
#print axioms DependentFibre.cross_postponed
#print axioms DependentFibre.cross_driver_states
#print axioms lowerSat_iff
#print axioms lowerSat_eq_decideSat
#print axioms exact_nil_iff_factorsOn_univ
#print axioms Exact.factorsOn
#print axioms Exact.principal_iff_of_epi
#print axioms initialSolution_iff
#print axioms InitialSolution.retract
#print axioms CumulativeCodes.Cross.answer_initial
#print axioms CumulativeCodes.Cross.constrained_exact
#print axioms CumulativeCodes.Cross.constrained_principal
#print axioms CumulativeCodes.solved_equalizer
#print axioms CumulativeCodes.solved_idempotent
#print axioms CumulativeCodes.equalizer_or_unsolvable
#print axioms CumulativeCodes.narrow_exact
#print axioms CumulativeCodes.Narrowing.NarrowStep.exact
#print axioms CumulativeCodes.Narrowing.NarrowRefutes.sound
#print axioms CumulativeCodes.Narrowing.steps_terminate
#print axioms CumulativeCodes.Narrowing.progress
#print axioms CumulativeCodes.Narrowing.principal_or_unsolvable
#print axioms CumulativeCodes.NarrowingControls.uniform_solver_stopped
#print axioms CumulativeCodes.NarrowingControls.narrowed_principal
#print axioms CumulativeCodes.NarrowingControls.misfit_refuted
#print axioms CumulativeCodes.NarrowingControls.domain_needed
#print axioms CumulativeCodes.NarrowingControls.level_question
#print axioms MillerCodes.act_comp
#print axioms MillerCodes.invert_exact
#print axioms MillerCodes.restrict_exact
#print axioms MillerCodes.prune_forced
#print axioms MillerCodes.intersect_forced
#print axioms MillerCodes.MStep.exact
#print axioms MillerCodes.MRefutes.sound
#print axioms MillerCodes.steps_terminate
#print axioms MillerCodes.progress
#print axioms MillerCodes.principal_or_unsolvable
#print axioms MillerCodes.Controls.inversion_principal
#print axioms MillerCodes.Controls.pruning_principal
#print axioms MillerCodes.Controls.intersection_principal
#print axioms MillerCodes.Controls.scope_refuted
#print axioms MillerCodes.Controls.occurs_refuted
#print axioms MillerCodes.Controls.nonpattern_no_principal
#print axioms CumulativeCodes.NarrowingControls.domain_raising
#print axioms Exact.principal_of_residual
#print axioms DependentFibre.PostponingFragment.outcome
#print axioms DependentFibre.cross_run_postponed
#print axioms DependentFibre.PostponingSettled.outcome
#print axioms DependentFibre.tower_sort_const
#print axioms DependentFibre.cross_sortTower_postponed
#print axioms CumulativeCodes.Ty.meet
#print axioms CumulativeCodes.meet_exact
#print axioms CumulativeCodes.Meet.MeetStep.exact
#print axioms CumulativeCodes.Meet.steps_terminate
#print axioms CumulativeCodes.Meet.MeetStep.compatibleGroups
#print axioms CumulativeCodes.Meet.progress
#print axioms CumulativeCodes.Meet.principal_or_unsolvable
#print axioms CumulativeCodes.Meet.never_postponed
#print axioms CumulativeCodes.Meet.stopped_principal
#print axioms CumulativeCodes.Meet.compatibleGroups_of_uniform
#print axioms CumulativeCodes.Meet.compatibleGroups_of_oneDomain
#print axioms CumulativeCodes.Meet.raising_solved
#print axioms CumulativeCodes.Meet.fragment_needed
#print axioms CumulativeCodes.Meet.meet_needs_compatible
#print axioms CumulativeCodes.Meet.outside_solved

#print axioms TreeFibre.delete_exact
#print axioms TreeFibre.invert_exact
#print axioms TreeFibre.familyRound_ne_stuck
#print axioms TreeFibre.familyRound_stable
#print axioms TreeFibre.family_decided
#print axioms TreeFibre.principal_of_inFragment
#print axioms TreeFibre.stopped_empty
#print axioms TreeFibre.stopped_principal
#print axioms TreeFibre.forced_meet
#print axioms TreeFibre.meet_exact
#print axioms TreeFibre.meetRule_exact
#print axioms TreeFibre.intersectRule_exact
#print axioms TreeFibre.pruneFlexFlex_exact
#print axioms TreeFibre.Controls.fit_committed
#print axioms TreeFibre.Controls.cross_outside
#print axioms TreeFibre.Controls.cross_postponed_by_families
#print axioms TreeFibre.Controls.level_postponed
#print axioms TreeFibre.Controls.mixed_unsolvable
#print axioms TreeFibre.Controls.narrow_principal_by_meet
#print axioms TreeFibre.Controls.over_narrowing_loses
#print axioms TreeFibre.Controls.twice_principal
#print axioms TreeFibre.stepOf_stuck_iff
#print axioms TreeFibre.readFlexData_valuation_free
#print axioms TreeFibre.raise_forced
#print axioms TreeFibre.raise_exact
#print axioms TreeFibre.raiseContract_exact
#print axioms TreeFibre.fitRound_ne_stuck
#print axioms TreeFibre.fitRound_stable
#print axioms TreeFibre.fit_decided
#print axioms TreeFibre.principal_of_inFitFragment
#print axioms TreeFibre.Controls.raise_principal
#print axioms TreeFibre.Controls.three_committed
#print axioms TreeFibre.Controls.cross_not_fit_inside
#print axioms TreeFibre.Controls.cross_postponed_by_fit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
