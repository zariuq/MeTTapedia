import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Universality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Core
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Locality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.DependentEq
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleInstanceSets
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Contextual
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ContextualCoupling

/-!
# The step as rule syntax

**What the interface is** (`Universality`). `Interface.Step` is an interface: a relation is the
transition relation of an instance with given frames, knowledge and present occurrences exactly when
every transition starts from solvable knowledge, refines it along some morphism of frames, and changes
the present occurrences by an enabled commit (`realizable_iff`). The last law excludes nothing
(`commit_between`); at one frame the second follows from the first (`oneFrame_laws_iff`); every relation
is an instance with no knowledge (`ofLTS`).

**A one-match step** (`Core`). Over a frame action with its extensions, a rule has its own frame of
schematic unknowns and, there, take and read patterns, tells, checks (equation guards, absence and
count queries) and made rows (the tree's `RuleInstance`), and collect patterns. A program is a set of
rules. A firing of a program is a rule of the program, an extension, an opening of the rule's unknowns
into the extended frame, a selection of occurrences and the collect query's claimed rows. Information,
freshness of the opening, shapes, the guard predicate and admission are computed from these, and
`step X O E P` is an `Interface.Step.Standard` whose admission is that computation (`admits_iff`).

**The existing steps, restricted, are this step.**
* One frame (`FirstOrderEq`): the first-order step restricted to the fresh openings of a program is the
  label-keeping step of the program, read through one label function (`embed`), with admission, results
  and transition relations equal (`admits_toFirstOrder_iff`, `result_toFirstOrder`, `firstOrder_eq`).
  For ground programs without collect patterns this is the tree's step under a rule set
  (`RuleInstanceSets.instanceSet_eq`); with unknowns that form shares a rule's unknowns with the caller
  (`instanceSet_captures`, `opened_keeps_caller_free`).
* Typed frames (`DependentEq`): the dependent full step restricted to the fresh openings of a program is
  the step of the program at helper telescopes (`admits_toDependent_iff`, `result_toDependent`,
  `dependent_eq`). The dependent full step's predicate queries with arbitrary regions and answers, and
  its rule instances that mention the state's unknowns, are beyond rule syntax.
* Declaration frames of a binding signature (`Contextual`): the canonical opening is fresh at every
  state (`canonical_fresh`); a firing with a fresh opening that takes and reads no row adds no relation
  between its new unknowns and what the state mentions beyond the knowledge and the rule's tells
  (`information_amalgamates`); a firing of the helper step couples its fresh helper to old names by a
  tell over the state's own frame (`helper_coupled`; `HelperControl.nameHelper_coupled`, at a state
  that mentions nothing). Freshness speaks only of what the state mentions (`ContextualCoupling`): at
  a state that mentions nothing, a fresh program firing without rows couples a new unknown to an old
  name too (`CouplingControls.coupling_admitted`, `coupling_couples`); where the state mentions the
  old name that firing is refused (`coupling_refused_when_mentioned`) and the helper firing still
  couples (`mentionedHelper_coupled`).

**What the step of a program excludes** (`Locality`): admission is invariant under changes of the store
outside the firing's take, read, make and query regions (`admits_of_outsideRegions`), rights are local
(`permitted_admits_of_outsideRegions`), the result's knowledge is, by definition, the state's knowledge
carried along the extension with the opened take and read equations on the labels of the selected
rows and the opened tells (`result_knowledge`), and at a finite store the selections of one rule,
extension, opening and made identities are finitely many (`selections_finite`), each with its control.

**Every feature fires** (`Examples`, at the one-frame action over first-order atoms): a take and a
make, a read, a tell that binds a caller's unknown, a guard that holds and one that fails, an absence
that holds and one that fails, and a refused opening that captures the caller's unknown.
-/
