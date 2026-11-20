import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.FixpointTypes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.OneLetterChain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Ladder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Groundable
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.GroundableUpTo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Changes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.ThatsAll
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.TwoKinds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Map

/-!
# When types apply

A type is a class no admitted observer splits. These modules say when such a class can be asserted,
of which kind it is, what it survives, what destroys it, and how its membership is found.

* `FixpointTypes`: the tree's modal μ-calculus over the step's systems, atoms as free variables;
  a formula whose fixed points have positive bodies denotes a bisimulation-closed class, through
  zigzag maps and spans; without positivity bisimilar states are split. Every finitary formula is a
  fixed-point formula.
* `OneLetterChain`: on a one-letter chain every such formula is a finite automaton reading the chain
  from its end; the formulas denote exactly the ultimately periodic sets; the squares by none.
* `Ladder`: on the step under "take one `T`", finitary ⊊ fixed-point ⊊ infinitary, with the even
  reaches and the square reaches as witnesses; a class of reaches is fixed-point denoted exactly
  when its reaches are ultimately periodic; with the bag observed, the even counts are not denoted
  by any fixed-point formula.
* `Groundable`: budgeted fixed-point checks with three outcomes; least fixed points of plain bodies
  are found at a finite unfolding on image-finite systems, greatest ones refuted at one and never
  confirmed by one; without image-finiteness stage ω is not enough.
* `GroundableUpTo`: the same through the bisimulation quotient, on every system with finite covers
  up to bisimilarity, so on every finite program of the first-order step.
* `Changes`: what a type must survive: firings (invariant cores), growth by another party (exactly
  the positively generated types of a join-preserving lens), more observers, substitution.
* `ThatsAll`: a closure clause is a none statement, sound in an open world exactly on an owned
  region; the constructor reading needs only that other creation goes through the constructors.
* `TwoKinds`: constructor-defined types have finite witnesses that survive growth; observer-defined
  types are refuted by one observation, persist as predicates and lose their lists of members; a
  type asserted from examples collapses exactly when the examples cover every class.
* `Map`: the table, every cell citing a theorem or saying "open".
-/
