import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Rows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Language
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Firings
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Possibility
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Validation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Direct
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Spatial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Substitutability
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Controls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Transfer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Formers
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Boundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Oracle
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.StepBeside
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic.All

/-!
# The step of a program as a presented language

The positive ground fragment of the step of a program (rules that take, read and make rows, with equation
guards between their own ground terms; no none query, count or collect query) is presented as a language definition of
the tree's framework, and the framework's constructions applied to it are the step's.

* **The presentation** (`Rows`, `Language`): sorts `Nat`, `Row`, `Store`; one constructor per row former and
  the union of stores as a bag of rows; no authored equations, so the only equations are the derived bag
  permutations (`equationEquiv_storeCode_iff`); one premise-free rewrite per rule, what it consumes beside a
  rest becoming what it yields beside the rest (`present`). The parallel context rule holds as a theorem
  (`semanticStep_beside`). The framework's executable compiler runs it as predicted (`Validation.demo_reducts`).
* **Generated possibility is firing possibility** (`Possibility`): the framework's derived diamond at the store of
  a configuration with trivial knowledge holds of an equation-invariant property exactly when an admitted firing
  of the step of the program reaches a configuration whose store has it (`generated_possibility_iff`; in OSLF's
  form as derived diamonds, `pulled_back_diamond_iff`; for `RuleSyntax.step` through the one-frame instance,
  `generated_possibility_keeping`). No rewrite has a premise (`present_premises`).
* **Directly for `RuleSyntax.step`** (`Direct`): every admitted firing, at every state with trivial knowledge, when
  identities are infinitely many (`generated_possibility_direct`, `pulled_back_diamond_direct`).
* **Spatial types** (`Spatial`): the union of stores generates "A beside B" (`split_generated`), with the split
  law (`sat_split_iff`; for every language of rows and stores without authored equations, `sat_split_iff_in`) and
  the law that a firing of a part is a firing of the whole, in the generated types (`split_possibly`), on the
  instance-set step (`succ_beside`, by `positive_admission_monotone`) and on `RuleSyntax.step` itself
  (`StepBeside.admitted_beside`); a none-guarded rule breaks it (`spawn_fires_alone`, `spawn_refused_beside`,
  `spawn_presentation_control`).
* **Substitutability** (`Substitutability`, `Controls`): on finite programs of the fragment, the barbed types, which
  the presented language generates (`barbed_generated`), agree at two stores exactly when the configurations are
  bisimilar observing row barbs (`substitutability`). This is the tree's Hennessy–Milner theorem
  (`program_adequacy`) transported through a translation of its formulas (`translate_sat`, `back_sat`); what is
  new is that the barbs and the possibility are the generated logic's own (`sat_barb_iff`,
  `sat_possibly_storeOf_iff`). It is not closed under contexts, unlike the tree's token-net theorem
  `saturated_iff_nativeTypes`. Both sides occur (`nine_bisimilar`, `token_not_bisimilar`), and the whole generated
  logic is finer (`singleton_separates`). For `RuleSyntax.step`'s label-keeping firings through `instanceSet_eq`
  and `firstOrder_eq`: `Transfer` (`bisimilar_keeping_iff`, `substitutability_keeping`).
* **Row formers and the OSLF type system** (`Formers`): the constructor former at rows (`sat_built_rowCode_iff`),
  "some row of the store has the type" (`sat_someRow_iff`), and the diamond of the OSLF type system the framework
  generates at the sort `Store` (`oslf_diamond_iff`).
* **Where presentation without premises stops** (`Boundary`, `Oracle`): no presented program steps as the none query
  step (`presented_not_none`, the corollary of `parClosed_not_noneReduces`) or has the none program's
  possibility (`none_not_presented`). A rewrite whose premise asks the relation environment about the whole
  store presents none queries (`whole_presents_none`) and has no parallel context rule (`whole_not_parClosed`); the
  relation environment is an arbitrary function, so the same device presents every yes/no question of the store
  (`Oracle.oracle_step_iff`, `Oracle.count_presented`): such premises are oracles, and the boundary is a boundary
  of presentations whose premises ask nothing of the store beyond their matches. A guard over a caller's unknown is
  decided by the knowledge, which rows do not record (`knowledge_decides`).
* **Programs with unknowns** (`Schematic`): the rule's unknowns as the rewrite's metavariables, reads and guards as
  premises of the builtin equality; generated possibility is firing possibility for range-restricted positive
  programs at ground states (`Schematic.generated_possibility`), the ground presentation is its instance at ground
  rules (`Schematic.semanticStep_ground_iff`), and the boundary of the class (`Schematic.Boundary`,
  `Schematic.Knowledge`).
-/
