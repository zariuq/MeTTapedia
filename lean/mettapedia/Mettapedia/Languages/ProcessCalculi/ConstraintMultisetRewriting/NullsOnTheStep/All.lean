import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullKinds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.NullSeparations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.SchemaGuards
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.EvaluationNulls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.AbsenceNotCompositional

/-!
# Nulls on the step

Each emptiness is an absence claim with its own scope, placed on the step (`NullKinds`): the empty
store, the refusal of one candidate, the empty answer set, one answer that is empty, the empty type of
candidates, no solution of the information, and the refusal of permission. The pairs listed in
`NullSeparations` are separated on an actual step, including the occurs check, whose null is relative
to the frames. Not every pair of kinds has a separation theorem, and the empty type of candidates has
no positive example on the first-order step, whose candidates do not depend on the state. The
evaluator's refusal, unresolved work and exhausted budget are three more, each separated from the
empty answer set (`EvaluationNulls`).

A guard evaluated in three outcomes is an attempt of the step's evaluation interface: no verdict is
unresolved work, never an admission or a refusal. Absence over stored schemas has that semantics, with
two sound evaluations, one refining the other (`SchemaGuards`).

Absence is not compositional (`AbsenceNotCompositional`): admission guarded by absence is not
monotone under the union of stores, while take, read, make and tell admission is, whenever the
union's knowledge stays solvable; no reaction and no relation closed under parallel composition is an
absence step, and the absence step on rho processes is not the reduction of any rho rule set.
Encodings of absence are not addressed. Absence is meaningful on owned stores read as a whole.
-/
