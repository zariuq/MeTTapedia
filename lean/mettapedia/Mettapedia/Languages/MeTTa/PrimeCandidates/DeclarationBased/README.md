# Declaration-based Pi/Sigma/Id profiles

These constructions use the parameterized Pi/Sigma/Id calculus, its formed
contexts and the cumulative level-tower profiles. A signature supplies the
actual constants and computation rules. List, J, relator, Boolean and HOL
extensions state their own conversion and preservation conditions.

Start with [DeclarationBased.lean](../DeclarationBased.lean), then
[SharedJudgmentFragment](SharedJudgmentFragment.lean) for the actual assembly
of declarations, scoped execution, matching, intrinsic HOL production and
contextual observations. `Assembly.resume` uses that assembly's own primitive
worlds. Its seven requirements concern those same data.

Principal results:

- `SharedJudgmentFragment.common_qualified` constructs a qualified source
  assembly; componentwise existence is not substituted for compatibility.
- `SharedJudgmentQuotientRetainedSemantics.qualified_iff` states the remaining
  source, service and declaration requirements on the same quotient data.
  `Controls.common_qualified` supplies their common concrete witness.
- `SharedJudgmentNativeBooleanParallel.cofinal` and
  `HOLNativeMixedConversionParallel.cofinal` develop their respective native
  parallel relations. Their root computation rules differ.
- `SharedJudgmentQuotientRetainedSemantics.Controls.changed_payload_semantics_without_contract`
  separates valid component meanings from satisfaction of the caller's actual
  service contract.

The native J/iota development supports the recorded scoped-identity direction;
K/UIP and proof irrelevance remain conditional on their named profiles.
The set and universe interpretations expose their host assumptions. Formation
of a native representation, source-proof preservation and logical reflection
are separate theorems. General full-candidate reflection is not inferred from
one typed HOL encoding.

The HOL carrier reading is shared through `TypeTheory.HOLFiber`.
`GSLT.Dedukti.HOLHubFiber` studies the specified hub conversion, while
[SetProfile](SetProfile/Basic.lean) supplies a concrete declaration signature
and reading. These are different uses of the same infrastructure, not three
interchangeable definitions of constant dependent families.

The stable research obligations remain in the existing specification index:
TRACE-004 and ASM-005 for broader joint assembly; HOST and identity clauses for
interpretation and motive coverage. `CertifiedTransformProgram`,
`IdentityEquality` and `SetProfile` retain their internal dependency boundaries.
