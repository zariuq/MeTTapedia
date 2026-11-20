import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Probes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Characterization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramFreeBisimilarity.Programs

/-!
# What the bisimilarity of the program-free step is

The program-free step (`Semantic.ruleOffers`) offers every semantic firing under its rule.

* `Probes`: under rule labels the queries of a firing are invisible, so the step moves as the
  occurrence step of the rule and the raw step has the same moves; the guard, tell, none queries, count
  and take probes, the multiplicity of a class read by the take of `k` copies; what bisimilar
  configurations share.
* `Characterization`: for every substitution action, on configurations with consistent knowledge,
  bisimilarity is equivalence modulo the knowledge: with no hypothesis for the step of guards and
  takes, and with a fresh supply of identities for the program-free step and every restriction of it
  that keeps guards and takes; inconsistent configurations, which no move reaches, are all
  bisimilar. The congruence for a disjoint store is therefore the statement that equivalence modulo
  the knowledge is preserved by a disjoint store, which the tree proves on the static side
  (`Observation.ModuloEquivalent.tensor_disjoint`); the two theorems are shown to state one fact.
* `Controls`: the ground and first-order instances; a control for each hypothesis (consistency, a
  fresh supply) and for each probe (guards alone, takes alone, no checks); private equivalence too
  fine, pointwise equivalence and the run layer's static probes too coarse; knowledge about
  unmentioned unknowns and the history of a take are seen.
* `Programs`: for a fixed program, bisimilarity contains equivalence modulo the knowledge and is
  strictly coarser; for take-and-make programs over a ground action, two consistent configurations
  are bisimilar exactly when the same words of the program are affordable from their bags; such
  programs whose rules take at most one row each compose with a disjoint store (`oneTake_tensor`),
  and a rule that takes two rows breaks that (`takeTU_not_congruence`).
-/
