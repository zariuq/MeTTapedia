# Ethics

Lean 4.28 port of the Fuenmayor & Benzmüller AFP formalization of Gewirth's
Principle of Generic Consistency (PGC).
**4 files. Zero sorry. Zero axioms beyond propext/choice/Quot.sound.**

## Origin and Attribution

This is a **direct port** into Lean 4 of the Isabelle/HOL formalization by
David Fuenmayor and Christoph Benzmüller:

> Fuenmayor, D. & Benzmüller, C. (2018).
> *Formalisation and Evaluation of Alan Gewirth's Proof for the Principle
> of Generic Consistency in Isabelle/HOL.*
> Archive of Formal Proofs, October 2018.
> https://isa-afp.org/entries/GewirthPGCProof.html

The original Isabelle development is at `GewirthPGCProof/` (project root).
Our Lean port follows the same proof structure, with one simplification:
the AFP formalization uses 8 frame axioms (`sem_3a`–`sem_5e`); our proof
needs only 3 (`sem_5a`, `sem_5b`, `sem_5e`), dropping 5 as unnecessary
(`sem_3a` av-seriality, `sem_4a` av⊆pv, `sem_4b` pv-reflexivity,
`sem_5c` ob-conjunction, `sem_5d` ob-transfer). `GewirthTheory.lean`
proves both the minimal route (`entails_PGC_strong`) and the full
AFP-aligned route (`entails_PGC_strong_from_AFPTheory`) to confirm the
stronger assumptions trivially subsume the weaker ones.

## Key Idea

The PGC is Gewirth's (1978) central theorem in moral philosophy: every
purposive agent, by virtue of acting for purposes, implicitly claims
that freedom and well-being are necessary for their action — and is
therefore rationally committed to acknowledging the same right for all
other purposive agents. In short: *Act in accord with the generic
rights of your recipients as well as yourself.*

This directory formalizes the PGC argument in Lean, proves the main
theorem (`PGC_strong`) from explicit assumptions, and bridges it to the
DDLPlus deontic logic layer and the governance norm framework.

## Modules

| File | Contents |
|------|----------|
| `Core.lean` | Semantic infrastructure: `Semantics`, `Entails`, `DeonticAttribute`, `MoralValueAttribute`, `ModalSentence`, `DeonticSemantics`, `ValueSemantics` |
| `GewirthPGC.lean` | The PGC argument: modal operators (□ᴰ, □ₐ, □ₚ, ◇ₐ, ◇ₚ), `Oi` (ideal obligation), `PPA` (purposeful purposive action), `RightTo`, `PGCInterpretation`, `PGCAssumptions`; main theorem `PGC_strong`; helper `CJ_14p`; bundled wrapper `PGC_strong_ofAssumptions` |
| `GewirthBridge.lean` | Connects PGC to the rest of Mettapedia: `PGCFullFrame` → `DDLPlusFrame` → `GovFrame`; `pgc_is_governance_norm` — the PGC conclusion is a governance norm in the DDLPlus framework |
| `GewirthTheory.lean` | Theory-level presentation: `PGCAssumptionTheory`, `pgcSemantics`, `entails_PGC_strong`; AFP-aligned route `entails_PGC_strong_from_AFPTheory` matching the Carmo-Jones DDL embedding |

## Key Results

- **`PGC_strong`**: from the PGC assumptions (`sem_5ab`, `CJ_14p`, `PPA`,
  `RightTo` instantiation, and the DDLPlus frame conditions), every
  purposive agent is ideally obligated to respect the generic rights of
  all other purposive agents. Zero sorry.
- **`pgc_is_governance_norm`**: the PGC conclusion holds as a
  governance norm in the DDLPlus/`GovFrame` framework — connecting
  moral philosophy directly to the OSLF governance layer.
- **`entails_PGC_strong`**: semantic entailment: any model satisfying
  the PGC assumption theory satisfies `PGC_strong`.
- **`entails_PGC_strong_from_AFPTheory`**: AFP-aligned route using the
  full CJDDLplus frame axioms, compatible with the Isabelle companion.

## References

- Gewirth, A. (1978). *Reason and Morality*. University of Chicago Press.
- Fuenmayor, D. & Benzmüller, C. (2018). *Formalisation and Evaluation of
  Alan Gewirth's Proof for the Principle of Generic Consistency in
  Isabelle/HOL.* Archive of Formal Proofs.
  https://isa-afp.org/entries/GewirthPGCProof.html
- Carmo, J. & Jones, A.J.I. (2002). "Deontic Logic and Contrary-to-Duties"
  (AFP formalization basis)
