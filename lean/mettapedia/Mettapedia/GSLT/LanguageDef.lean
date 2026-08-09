import Mettapedia.GSLT.LanguageDef.Extension
import Mettapedia.GSLT.LanguageDef.InferenceExtension
import Mettapedia.GSLT.LanguageDef.ValidatedInferenceExtension
import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.ExtensionGluing
import Mettapedia.GSLT.LanguageDef.ExtendedLanguageDef
import Mettapedia.GSLT.LanguageDef.TotalGSLT
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef
import Mettapedia.GSLT.LanguageDef.CalculusAsLanguage
import Mettapedia.GSLT.LanguageDef.CalculusExtension
import Mettapedia.GSLT.LanguageDef.ProofGSLT
import Mettapedia.GSLT.LanguageDef.RuleMachineCompilation
import Mettapedia.GSLT.LanguageDef.LogicExtension
import Mettapedia.GSLT.LanguageDef.OracleExtension
import Mettapedia.GSLT.LanguageDef.ReflectionExtension
import Mettapedia.GSLT.LanguageDef.RuntimeProfileExtension

/-!
# Compositional language definitions

This is the canonical entry point for the five-field language-definition and
extension architecture.

An object language remains exactly `name`, `types`, `terms`, `equations`, and
`rewrites`.  Additional authored structures are dependent fibres over that
base.  Their authoring languages are GSLTs, their elaborators respect the
source equations and rewrites, and erasure recovers the exact base.

Primary human authoring has two direct forms.  `CalculusLanguageDef` is the
flat specialization with judgments and rules in the same record as the five
object-language fields.  `ExtendedLanguageDef layer`, together with
`extendedLanguageDef!`, handles any finite product of independently authored
layers without adding a universal optional field for every future extension.
The older nested `Presentation` remains a derived checker and transport type;
validators, generated projections, and focused checker fixtures may use it,
but it is not the primary authoring authority.

The reusable hierarchy is law-based:

1. `GSLT.Embedding` preserves and reflects `(E,R)`; `Embedding.Observed`
   additionally names the answer, trace, cost, or reflection observation that
   is preserved.
2. `CoGSLTLayer` is an exact dependent elaboration over an unchanged base.  It
   does not by itself claim that authored terms can be concatenated.
3. `GSLT.Compositional` supplies empty and concatenation inside `(T,E,R)`, and
   `GSLT.CompositionalElaboration` requires elaboration to preserve that
   concatenation.  The payload partial monoid is derived from this law rather
   than carried independently.
4. `GSLT.ContextualAdmission` separates total authored composition from an
   application-specific acceptance predicate and overlap law.  Compatible
   siblings glue; staged increments are admitted relative to an accumulated
   payload.
5. `GSLT.Realization` carries compilation together with an explicitly named
   conservation certificate.  Stages compose, independent realizations form
   products, and certified backends may be selected per source without changing
   their common observation.

`RuleMachineCompilation` supplies a nontrivial realization instance: it compiles
authored inference rules to register-machine blocks and proves that executing a
compiled block agrees with applying the authored rule.  Binary encoding and
search scheduling remain later realization stages rather than hidden parts of
that theorem.

`GSLT.Interaction` is the complementary construction for components that are
not independent: the component theories remain faithfully embedded while all
cross-rewrites are explicit authored data.  `GSLT.InteractionElaboration`
requires those crossings to preserve the common interpretation.  Together
they prevent a product construction from silently claiming that communicating
layers are disjoint.

Proof calculi use the complete path:

1. atomic judgment and rule declarations form a GSLT;
2. the free document construction supplies empty documents, concatenation,
   equations, and contextual rewrites;
3. elaboration produces a `ProofCalculus` in the fibre over one base;
4. admission validates that calculus against the unchanged base; and
5. proof search is a derived GSLT whose reachability agrees with derivability.

`ExtensionComposition` derives the payload partial monoid from authored
concatenation and its elaboration law, then combines independently authored
layers.  `ExtensionGluing` instantiates contextual admission for proof calculi.
Admission is deliberately separate: authored documents always compose, while
admitted payloads compose only when their overlap conditions hold.  Pairwise
gluing is not called descent: covers and coherent higher overlaps have not been
chosen here.

The strict `ProofGSLT` nucleus is included here.  Stronger proof-GSLT
interpretation, cyclic, and ultrainfinite modules have their own imports so
that this foundational entry point does not silently enlarge its authority.
-/
