# Evidence

This directory contains system-independent mathematics for evidence-bearing
reasoning. It is deliberately smaller than any particular logic.

- `SourceScope.lean` studies finite sets of source occurrences: independence,
  overlap, union, and pairwise independence.
- `SourceScoped.lean` gives heterogeneous evidence objects a common projection
  to that source geometry. It does not prescribe a truth value or merge rule.
- `TwoLanguage.lean` separates belief and evidence vocabularies, their
  meanings, relevance, evidence transport, open layers, and finite views.

NARS, PLN, and other reasoning systems may import these definitions. Their
truth-value semantics, inference rules, and conflict policies remain in their
own directories. Cross-system equivalences and non-equivalences belong in
explicit bridge modules.

