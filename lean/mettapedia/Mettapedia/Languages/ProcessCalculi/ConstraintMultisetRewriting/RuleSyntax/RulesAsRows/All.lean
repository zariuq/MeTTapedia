import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Codes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.NoJunk
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Interpreter
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Simulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Bisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.RunTime
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Limits
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Queries
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Gating
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Untagged
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Mobility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Decoding
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Renaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Canonical

/-!
# Rules as rows: one fixed program that interprets the rules held in the store

The step of a program (`RuleSyntax.step`) takes its program as a parameter. Here the program is in the
store: a rule is a row holding its code, and one fixed program, the interpreter `U`, reads codes as
rows and does what they say by matching and making rows.

**The term theory** (`Codes`): terms with closed codes (symbols, cells, slots with quotation levels)
and `drop c e`, a code instantiated at an environment; the declared equality is equality of normal
forms, under which dropping the quotation of a term at an environment instantiates the term's
unknowns by the environment's entries (`nf_drop_quote`). It is a substitution action
(`Expr.action`), used at one frame with the identity extension. **It has no junk** (`NoJunk`): a store
of drop-free equations is solvable in it exactly when it is solvable over plain first-order terms, and
every property of the equality pattern of finitely many drop-free terms agrees between the two
(`consistent_iff_firstOrder`, `forall_iff_firstOrder`).

**Codes, the specification and the interpreter** (`Interpreter`): the code of a rule (`ruleCode`) is a
closed row listing the quotations of its takes, reads, made rows, tell sides, check terms, check kinds
and collect patterns. Every drop-free rule of the rule syntax has one: takes, reads, tells, equation
guards, absence and count queries, made rows, collect query. The stored-rule program `Stored F` gates every
rule of `F` by a read of its own code: a rule fires only while its code is present. The interpreter `U`
has one rule per shape (`interp`), independent of any object program: a shape fixes the numbers of
takes, reads, made rows, tells and collect patterns and the list of check kinds with their count
numbers, so one arity carries infinitely many rules, and `U` is the image of an injective computable map
from shapes (`mem_U_iff`). An interpreter rule reads a code by a pattern of unknowns, and opens
every term of the coded rule by dropping it at one environment unknown, which stands for all the rule's
own unknowns. After its code read it is the object rule with each unknown a projection of the
environment (`specialize_entry`): the declared equality instantiates, firing does the rest.

**The theorem** (`Simulation`, `Bisimulation`): for every fragment `F` closed under what its rules make,
the step of `U` and the step of `Stored F` are strongly bisimilar on stores tagged through their
knowledge (every row a data row, or made by the knowledge the code of a rule of `F`: `SemTagged`),
firing for firing, with the same selections (`forward`, `backward`, `bisimulation`, `runs_forward`,
`runs_backward`). Without closure, the same holds where the stored-rule program keeps the tags
(`step_bisimulation`), and along runs under an invariant that implies them (`runs_forward_of`,
`runs_backward_of`). Tagging is needed (`Untagged`): at a store whose row is an unknown, the interpreter
reads it as a code with undetermined entries, and no stored firing with the same selection matches the
result (`loose_unmatched`); such a store is not tagged through its knowledge (`loose_not_semTagged`).
The interpreter's stores after a make are tagged by no set of rules by syntax (`interp_result_untagged`)
and are tagged through their knowledge, so the bisimulation restarts from them
(`Represents.semTagged_interp`, `interp_result_restarts`).

**A fixed program** (`Gating`): the step of `U` from a store of data rows together with the code rows of
a fixed program `P` is strongly bisimilar to the step of `P` from the store
(`fixed_program_bisimulation`), for finite programs of rules that make data rows only and whose take,
read, query and collect patterns address data rows, from stores of data rows; a rule reading any row
would read the code rows (`readAny_reads_code`).

**Which rows are codes** (`Decoding`): reading a row back as a rule and coding it again decides whether
the row is the code of a rule of the fragment (`isCode_iff`); tagging by syntax is decided row by row
(`taggedCheck_iff`).

**Names of a rule's own unknowns** (`Renaming`): a program and its copy with each rule renamed by an
injective renaming have the same steps (`renamed_succ`), so the interpreter run from the codes of the
renamed rules is bisimilar to the original program (`renamed_codes_bisimulation`); a non-injective
renaming changes the steps (`collapsed_refused`), and code rows are syntax: a rule reading a code by its
text tells a renamed copy apart (`probe_refuses_renamed`). The canonical code (`Canonical`), the code of
the rule with its unknowns numbered by first occurrence, is the same row for a rule and every renamed
copy (`canonCode_rename`), and the interpreter runs a fixed program from its canonical codes
(`canonical_codes_bisimulation`).

**Existence and controls** (`Examples`, `Queries`): a two-rule program with a take, a read, a tell that
binds the store's unknown, guards and made rows, run for two steps through `U` (`interpreter_run`); a
absence query and a count query through `U`, each with its refusal; a guard that fails, no firing
without codes, and a wrong shape refused.

**Rules at run time** (`RunTime`): the coding is injective (`ruleCode_injective`); an installer makes a
code row and the installed rule then fires, through `U` (`interpreter_install_run`); a remover takes a
code row and the rule no longer fires (`interpreter_removal`). Adding or removing a rule at run time is
making or taking a row that gates a rule of a program fixed in advance: the install run is a run of the
fixed program `Stored InstallFragment` (`stored_program_installs`). The ungated program `{second}`
fires with no code in the store (`fixed_fires_without_code`), where the stored-rule program does not.

**Codes received in rows** (`Mobility`): a rule that makes a code from a message it took is in no
closed fragment (`relay_outside`); the store it reaches is tagged by no set of rules by syntax
(`relayed_untagged`) and is tagged through its knowledge (`relayed_semTagged`). For the relay and
`second`, under the invariant that every message carries the body of the code of `second`
(`RelayInv`, kept by every firing), the interpreter and the stored-rule program correspond from the
start, step for step (`relay_runs_forward`, `relay_runs_backward`, `interpreter_relay_run`); where a
message's payload is an unknown, the tags are lost (`openPayload_not_kept`).

**Limits** (`Limits`): for each bound `N` on the entries of each part and on the count numbers, a finite
part of `U` is bisimilar to the stored-rule program of every closed fragment bounded by `N`
(`upTo_finite`, `bisimulation_upTo`); bounding the entries alone leaves infinitely many rules
(`entriesAtMostOne_infinite`); no finite program at all interprets every rule firing for firing
(`no_finite_one_firing`, by take arity); `U`'s own rules are in the fragment only at the empty shape
(`interp_fragment_iff`), the construct outside being `drop`, and that rule is idle
(`interp_empty_idle`).
-/
