import Mettapedia.GSLT.LanguageDef.TemplateScope.Term
import Mettapedia.GSLT.LanguageDef.TemplateScope.Elaboration
import Mettapedia.GSLT.LanguageDef.TemplateScope.Evaluation
import Mettapedia.GSLT.LanguageDef.TemplateScope.Corpus
import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum
import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumTheorems
import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
import Mettapedia.GSLT.LanguageDef.TemplateScope.Lists
import Mettapedia.GSLT.LanguageDef.TemplateScope.ListsCorpus

/-!
# Template scope and the environment action

Who owns a `$` name in a lambda body or template that runs more than once in
one form, and how the store reaches each consumer.

Core:
* `TemplateScope.Term` — scope-bearing terms (a lambda carries its own names
  as binders), ground values, one capture-avoiding substitution, the
  environment action: absorption, idempotence, occurrence locality.
* `TemplateScope.Elaboration` — rule M (Mercury's implicit quantification)
  and rule A; text inlining is safe under hygiene.
* `TemplateScope.Evaluation` — activation disciplines (static own-renaming
  for M and A, copy-at-call for B), the bag-valued answer semantics, lambda
  lifting, inlining at the query.
* `TemplateScope.Corpus` — kernel-checked programs: positive and negative
  examples of every theorem, and the desired outputs of the C task.

The scope-policy spectrum:
* `TemplateScope.Spectrum` — slots (owner, spelling); the ownership,
  lifetime and readout axes as elaborations and disciplines; adequacy of
  activation renaming for the slot frames of
  `ScopedAuthoritativeSlotCompilation`.
* `TemplateScope.SpectrumTheorems` — the cone law for the evaluator, the
  ownership-level 4-versus-5 tension, context independence of explicit
  capture and lexical fresh.
* `TemplateScope.SpectrumCorpus` — the corpus under six configurations and
  the criterion matrix.
* `TemplateScope.Lists` — every option as a default inference of stored
  lists; stored lists determine meaning; lexical inventory and its boundary
  rule.
* `TemplateScope.ListsCorpus` — lexical inventory on the corpus, criterion
  10, and the lifetime remark.

Agreement between these elaborators and the runtime's elaborator is a
separate obligation, not proved here.
-/
