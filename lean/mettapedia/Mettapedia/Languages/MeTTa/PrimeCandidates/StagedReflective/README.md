# Staged scoped-reflective profiles and language operations

This family connects the named staged scoped-reflective calculus to the
selected query-first occurrence/Need/quotation presentation. Its typed route
encoding uses the declaration-aware two-sort calculus. Stage indices, binder
contexts and the selected language region remain explicit.

Start with [StagedReflectiveInstances](StagedReflectiveInstances.lean),
[LanguageDefAdequacy](LanguageDefAdequacy.lean) and
[LanguageOperationSyntax](LanguageOperationSyntax.lean). The parameterized
operational assembly itself is [Native/Language](../Native/Language.lean);
it is not defined by choosing this type-theory profile.

Principal results:

- `FiniteLanguageOperationSignature.Signature.operationQuotientEquiv` identifies the
  quotient of recognized route syntax with independently decoded programs.
  `Signature.InvariantInterpretation.existsUnique_factor` gives the corresponding universal factorization.
- `GSLTILLayeredCrown.dataExecutionRepresentation_map` identifies the direct
  action extracted from the path-generated relation with the existing Data
  execution. `dataExecutionCompEquiv` retains the intermediate value and both
  route witnesses under composition.
- `GSLTILLayeredCrown.represented_fragment_does_not_functionalize_raw_commands`
  and `returned_fibre_remains_strict` preserve the boundaries of that fragment.
- `GSLTILInteractionTransport` applies the common occurrence-path transport to
  actual typed programs. Injective-state history readback is proved in
  `GSLT.Core.OperationalPathFibration`.

The current finite operation package has its authored language codes and
primitive route; it does not represent every future language change. General
finite signatures, syntax-directed recognition and typed encoding live in
`GSLT.LanguageDef.FiniteLanguageOperationSignature`.

Further route families, conversion bubbles and full source-kernel adequacy
remain separately stated research obligations. Structural quotation,
conversion, proof transport and native execution have separate interfaces.
