# Historical two-sort dependent-calculus presentations

This is the MeTTa-facing part of the historical MeTTa-Pure experiment.
It does not identify a selected MeTTa or Prime foundation, and it is not
MeTTa Zero.

`Pattern/` contains a locally nameless presentation in MeTTa-IL `Pattern`.
The independent de Bruijn-scoped calculus lives in
`TypeTheory/Calculi/TwoSortPiSigmaId`, with explicitly separate `Permissive`
and `Regular` typing developments.

## Mathematical scope

The fixed fragment has a distinguished ground type `U0`, an untyped
formation marker `U1`, dependent products and sums, identity formation and
reflexivity, and beta/projection reductions. It has no cumulative universe
hierarchy or identity eliminator. Calling these two heads a pair of
Russell universes obscures the actual typing rules.

`Pattern/Core.lean` supplies a concrete `LanguageDef`, not an initiality theorem.
`Pattern/Confluence.lean` and `Pattern/SubjectReduction.lean` prove properties of their
stated reduction and typing relations. Those statements neither choose a
Prime kernel nor prove the full Prime metatheory.

The separate regular intrinsic development proves normalization and
checking results for its own formed-context, declaration-free fragment.
Its hypotheses and boundary examples must accompany any reuse. See
the mathematical calculus's README for the judgment distinction.

## Separation of responsibilities

- Reusable binding, reduction, normalization and categorical mathematics
  belongs in subject-matter theory modules.
- A concrete calculus is an instance whose sorts, formation rules,
  conversion and supported eliminators are explicit.
- MeTTa syntax translation and candidate integration are downstream bridges.

`Adapters/` owns quotation, elaboration, presentation comparisons and guest
encodings. `Services/` owns the closed-certificate/checking experiments;
these use the permissive or declaration-aware judgments named in their
statements. Their one-pass complete-development service is not the exact
regular normalizer. `HEFragmentBridge.lean` is a scoped runtime comparison.

The regular typing authority was extracted into the mathematical calculus's
`Regular/Typing.lean`; `Adapters/PresentationBoundary.lean` imports it, not
the reverse. `Pattern.lean` and `Scoped.lean` are experiment import bundles,
not selections of a Prime kernel.

The generic `TypeTheory/CwfYoneda` constructions already take an arbitrary
source CwF and do not depend on this directory. Their application here is a
test instance, not a proof that this fragment satisfies Prime's requirements.

## Build scope

The library and experiment bundles do not import every standalone adapter.
In particular, `Adapters/LeaTTaDIndGEvaluator.lean` is outside those bundles;
its build is opt-in and needs LeaTTa (`-Kleatta` with the package override).
A green root build does not certify that adapter. Its relocation does not
change LeaTTa's semantics or make repairing that separate project part of
the two-sort calculus development.
