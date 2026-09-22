import Mettapedia.Languages.OpenTheory.Substitution
import Mettapedia.Languages.OpenTheory.CoreRules
import Mettapedia.Languages.OpenTheory.Binding
import Mettapedia.Languages.OpenTheory.BindingRules
import Mettapedia.Languages.OpenTheory.TheoremSubstitutionRule
import Mettapedia.Languages.OpenTheory.PrimitiveRules
import Mettapedia.Languages.OpenTheory.AxiomPolicy
import Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
import Mettapedia.Languages.OpenTheory.TheoryClosure
import Mettapedia.Languages.OpenTheory.TheoryClosureCanary
import Mettapedia.Languages.OpenTheory.TheoryReplay
import Mettapedia.Languages.OpenTheory.TheoryReplayCanary
import Mettapedia.Languages.OpenTheory.Definitions
import Mettapedia.Languages.OpenTheory.DefinitionsCanary
import Mettapedia.Languages.OpenTheory.PackageDefinitionOwnership
import Mettapedia.Languages.OpenTheory.PackageDefinitionOwnershipCanary
import Mettapedia.Languages.OpenTheory.NominalProvenanceBoundary
import Mettapedia.Languages.OpenTheory.NominalProvenanceBoundaryCanary
import Mettapedia.Languages.OpenTheory.CheckedSourceTheorem
import Mettapedia.Languages.OpenTheory.CheckedSourceTheoremCanary
import Mettapedia.Languages.OpenTheory.NIKAuthority
import Mettapedia.Languages.OpenTheory.NIKAuthorityCanary
import Mettapedia.Languages.OpenTheory.ExtensionalHOLInterpretation
import Mettapedia.Languages.OpenTheory.ExcludedMiddleNotDerivable
import Mettapedia.Languages.OpenTheory.EtaNotDerivable
import Mettapedia.Languages.OpenTheory.DefinedConnectives
import Mettapedia.Languages.OpenTheory.DerivedRulesEquality
import Mettapedia.Languages.OpenTheory.DerivedRulesConnectives
import Mettapedia.Languages.OpenTheory.DerivedRulesEta
import Mettapedia.Languages.OpenTheory.ReverseTranslation

/-!
# The OpenTheory kernel: syntax, primitive rules, theories, and semantics

This directory formalizes the logical kernel of OpenTheory at revision
`f555adbf6f3ca52ef6a9c5ca35d0316e53a289c1`.

Syntax and inference: provenance-sensitive typed syntax, the pinned
source-compatible substitution model, typed alpha-canonical sequents, and an
executable checker for all nine primitive theorem rules.  The rules have
Type-valued one-step certificates, independent declarative semantics, exact
success and failure correspondence, and deterministic combined dispatch.
Substitution uses the stricter `TermSubst.TypeCorrect` admission condition and
its type-preservation theorem.

Theories: axiom policies and least premise closure keep the primitive kernel
distinct from each selected object theory, with an exact replay interface and,
for every explicit decidable policy, a concrete NIK least-closure authority
whose semantic projection is axiom-provenance authorization, not truth.
Constant and type-operator definitions have exact executable admission gates
and provenance theorems.  Package-level printed-name ownership is separate from
provenance identity, and a proved alpha-collision shows why exact definition
provenance requires retained nominal source evidence.  A source-retaining
theorem carrier and constant-definition checker project exactly to the
canonical pinned checker.

Semantics: every theorem of the policy closure has a translated sequent
provable in extensional higher-order logic from background sentences that
prove its axiom tags, hence sound for Heyting-valued substitutional models and
for extensional Henkin models.  The axiom-free kernel derives none of `⊢ F`,
excluded middle `⊢ ∀ p. p ∨ ¬ p` (connectives by their definitions), and eta
`⊢ (λ x. f x) = f`; since extensional higher-order logic proves eta, the
translation of the axiom-free kernel is not complete.  With the eta axiom it
is: every natural-deduction rule of extensional higher-order logic is
admissible in the kernel over the HOL Light definitions of the connectives
(`DerivedRules*`, `ReverseTranslation`, `EtaCompletenessRules`), so a sequent
with Boolean hypotheses is derivable under the eta axiom policy iff its
translation is provable (`EtaCompleteness`), iff it is a consequence in every
Heyting-valued model (`EtaCompletenessHeyting`).  The theorem-list GSLT of the
kernel and the composition of reachability with these semantic statements live
in `OperationalGSLT`, `OperationalGSLTAdequacy`, and `ReachabilitySemantics`.

Remaining obligations:

* closure of the source-retaining carrier under type-operator definitions,
  the remaining named primitive operations, and every article command;
  recursive proof trails and reader execution;
* semantic conservativity of definitions, and an interpretation of
  definitional extensions in higher-order logic;
* completeness for OpenTheory theories with axioms beyond eta, and for the
  classical extension by choice;
* the standard theorem axioms (extensionality, choice, and infinity) as a
  selected axiom policy, which remain separate from the primitive inference
  layer;
* adequacy for OpenTheory, HOL Light, or HOL4 artifacts.
-/
