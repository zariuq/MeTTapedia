import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Congruence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.ProgramLaws
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Modulo
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Strong
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Standard
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.TellLaw
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.ReadLaw
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Commute
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Separations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.GuardTerms
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.TellReadControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.BarbComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.NameRenaming

/-!
# When two programs may replace each other: reduction-closed barbed congruence on the step of a program

**Systems, contexts, barbs** (`Systems`). A system is a program with a state; it reduces by
`RuleSyntax.step` of its program. Contexts add rows (at absent identities), add rules, tell
equations, or extend the frame; running beside another system is the composite of the three first
kinds. The barb is the may-barb of a pattern: whether some present row can be read against it at some
solution of the knowledge. It is the admission of the observer rule that reads the pattern
(`mayBarb_of_observed`, and `observed_of_mayBarb` given a fresh opening). It does not count rows
(`sevens_barbs`); the contexts that add rules do (`count_separates`). Must-barbs hold vacuously at
unsolvable knowledge.

**The congruence** (`Congruence`, `Strong`). Reduction-closed barbed congruence, the largest
symmetric relation that preserves the barbs, answers reductions and is closed under every context, is
an equivalence relation (`congruent_equivalence`), a congruence for every kind of context, with the same
identities for added rows (`Congruent.applyAll_same`), sound for contextual equivalence
(`congruent_contextual`) and contained in closed bisimilarity (`Congruent.bisimilar`). With infinitely
many identities it is the largest relation closed under contexts with the same identities
(`congruent_iff_congruentSame`, in `Standard`).

**Laws** (`Renaming`, `Modulo`, `ProgramLaws`, `TellLaw`, `ReadLaw`): renaming of identities;
states equivalent modulo the knowledge with the same support; union of rule sets idempotent,
commutative and associative; a rule that never fires may be dropped; an entailed guard may be
dropped (whatever its terms at one frame over first-order terms with the numbers as unknowns, with
function symbols or without; at the frame with one unknown only when its terms are terms of the rule,
for want of a fresh unknown: `GuardTerms`); an entailed tell with no new support is a no-op; one read
is a take followed by a make of the same pattern, with infinitely many identities.

**Separations** (`Separations`). A context separates two systems when they are closed bisimilar before
it and not after it (`SeparatedBy`); then they are not congruent (`not_congruent_of_separatedBy`). At
one frame a row context, a rule context and a tell context each separate a pair, and each statement
names its context (`row_kind`, `rule_kind`, `tell_kind`). An extend context separates nothing at one
frame (`not_separates_extend`); whether one separates a pair beyond one frame is open. Running beside
another system is the composite of a tell, a row context and a rule context; on its pair it adds no
separating power over rows (`beside_separates`, `row_kind`).

**Controls** (`Controls`, `GuardTerms`, `TellReadControls`): for each hypothesis of a law, a pair just
outside it, or the instance where it is not needed together with one where it is; pairs of different
systems that are congruent; the knowledge is not observed up to logical equivalence
(`tautology_observable`).

**Names** (`NameRenaming`): the step at one frame is equivariant under every renaming of the
substitution action that commutes with substitution and preserves and reflects the declared equality.
The renamed system's admission, results, firings, reachable states and outcomes are exactly the
renamed ones (`step_equivariant`). Over first-order terms, every permutation of constants together
with an arity-preserving permutation of function symbols is such a renaming (`names_equivariant`), and
so is every permutation of the unknowns (`unknownsAutomorphism`). A bijection that breaks a declared
equality, or that exchanges an unknown with a name, is not one, and the module's controls show the
firing that separates it.

**Contexts and steps** (`Commute`): adding rows at fresh identities commutes with a step whose firing
asks no query and stays fresh. **Barbs compared** (`BarbComparison`): a success row is blind where the
pattern barbs see, until a rule context converts the row.
-/
