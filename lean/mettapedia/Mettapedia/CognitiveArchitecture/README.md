# Cognitive Architecture — MetaMo, OpenPsi, MicroPsi & GödelClaw (Lean 4)

A *cognitive architecture* is a computational theory of how an agent's
motivations, emotions, and decisions fit together into one working mind: what it
wants, how a stimulus changes those wants, and how those wants pick an action.
This directory formalizes such architectures in Lean and asks what they have in
common — and what they leave out.

The organizing abstraction is **MetaMo**, a category-theoretic *motivational
Q-module*: motivational state lives in a module over a quantale of "intensities,"
an **appraisal** functor maps environmental stimuli to changes in that state, and
a **decision** functor maps state to actions. Two well-known psychological
architectures appear as concrete MetaMo instances — **OpenPsi** (the OpenCog
realization of Dörner's *Psi* theory, with six demands and four modulators) and
**MicroPsi** (Bach's architecture, with seven demands and a PAD emotion model) —
which lets the formalization compare them on a common footing and *prove* where
they coincide and where they fall short. The `Values/` strand then extends the
picture beyond the consequentialist core both architectures share (Schwartz
values, Haidt's moral foundations, deontological/relational/temporal/meta layers),
and the work-in-progress **GödelClaw** kernel (`GodelClaw/`) builds an
ethical-agent layer — policy kernel, tool broker, gate chain, "mindlock" — on top.

## Modules

### MetaMo

MetaMo is a six-file motivational Q-module framework.

- `MetaMo/Basic.lean`
  - MetaMo/Basic.lean defines Q-module structure with scalar multiplication

- `MetaMo/Appraisal.lean`
  - MetaMo/Appraisal.lean defines environmental stimulus appraisal functors

- `MetaMo/Decision.lean`
  - MetaMo/Decision.lean defines action selection functors

- `MetaMo/Commutativity.lean`
  - MetaMo/Commutativity.lean proves appraisal-decision commutativity

- `MetaMo/Dynamics.lean`
  - MetaMo/Dynamics.lean proves stability via Banach fixed-point arguments

- `MetaMo/Main.lean`
  - MetaMo/Main.lean aggregates the MetaMo module surface

### OpenPsi

OpenPsi is a five-file formalization of Dorner Psi with six demands and four modulators.

- `OpenPsi/Basic.lean`
  - OpenPsi/Basic.lean defines demands, modulators, and action-selection rules

- `OpenPsi/FuzzyLogic.lean`
  - OpenPsi/FuzzyLogic.lean defines fuzzy satisfaction computation

- `OpenPsi/ActionSelection.lean`
  - OpenPsi/ActionSelection.lean defines demand-driven action selection

- `OpenPsi/MetaMoInstance.lean`
  - OpenPsi/MetaMoInstance.lean defines OpenPsi as a QModule over ENNReal

### MicroPsi

MicroPsi is a three-file formalization with seven demands and PAD decomposition.

- `MicroPsi/Basic.lean`
  - MicroPsi/Basic.lean defines demands, PAD model, and utility action selection

- `MicroPsi/MetaMoInstance.lean`
  - MicroPsi/MetaMoInstance.lean defines MicroPsi as a QModule over ENNReal

### Bridges

Bridges is five files of cross-architecture comparison and limits.

- `Bridges/PLNMetaMoBridge.lean`
  - Bridges/PLNMetaMoBridge.lean connects PLN evidence quantales to MetaMo

- `Bridges/OpenPsiMicroPsiBridge.lean`
  - Bridges/OpenPsiMicroPsiBridge.lean compares OpenPsi and MicroPsi as MetaMo instances

- `Bridges/ModelExpressiveness.lean`
  - Bridges/ModelExpressiveness.lean analyzes expressiveness boundaries

- `Bridges/MissingValueSystems.lean`
  - Bridges/MissingValueSystems.lean proves value-system gaps outside consequentialism

### Values

Values is nine files extending beyond consequentialism.

- `Values/SchwartzValues.lean`
  - Values/SchwartzValues.lean defines Schwartz ten-value circumplex structure

- `Values/MoralFoundations.lean`
  - Values/MoralFoundations.lean defines Haidt six moral foundations

- `Values/DeontologicalLayer.lean`
  - Values/DeontologicalLayer.lean defines duty constraints above consequential utility

- `Values/RelationalValues.lean`
  - Values/RelationalValues.lean defines individual-dependent relational values

- `Values/TemporalValues.lean`
  - Values/TemporalValues.lean defines legacy and future-generation value structure

- `Values/MetaValues.lean`
  - Values/MetaValues.lean defines values about values including corrigibility

- `Values/FOETBridge.lean`
  - Values/FOETBridge.lean connects value formalization to FOET

### GödelClaw (work in progress)

`GodelClaw/` (32 files, including `GodelClaw/Ethics/`) is a work-in-progress
ethical-agent kernel — a policy kernel, tool broker, gate chain, and "mindlock"
with a MetaMo bridge, over a meaning/agency ethics layer. It introduces one
named primitive as a postulate (currently a `Prop` `axiom` — more a placeholder
definition than a proved theorem, to be refined):

```lean
-- GodelClaw/Core.lean
/-- "Realize the known desires of all beings when possible, while avoiding
    preventable harm." — from Formal-Ethics-Ontology (SUO-KIF). -/
axiom UniversalLovingCare : Prop
```

## Key results

- OpenPsi and MicroPsi are MetaMo QModule instances.
- Appraisal-decision commutativity is proven when the quantale is commutative.
- Contractivity is a sufficient condition for unique motivational equilibrium.
- Gap analysis shows that both base architectures are fundamentally consequentialist.

## Formalization status

All 64 `.lean` files in this directory are `sorry`- and `admit`-free.

**Trusted base.** The MetaMo / OpenPsi / MicroPsi / Bridges / Values strands have
no source-level `axiom` declarations (a source grep, *not* a per-theorem `#print
axioms` audit — a theorem can still inherit a Mathlib axiom transitively).
`GodelClaw/` introduces **exactly one** named postulate: `axiom
UniversalLovingCare : Prop` in `GodelClaw/Core.lean` (see GödelClaw above). This
is an honest stand-in for an ethical primitive — more a placeholder than a proved
theorem — and the rest of `GodelClaw/` is otherwise `sorry`-free. There is **no
`native_decide`** anywhere in this directory, so nothing here compile-evaluates in
place of kernel-checking.

Reproduce from this directory — the regexes below are raw scans (they would also
match the term in comments/strings):

```bash
# real sorry/admit tactics (prints nothing):
rg -n --glob '*.lean' '^\s*(sorry|admit)\b' .
# axiom declarations (prints only the one GödelClaw postulate):
rg -n --glob '*.lean' '^\s*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Zhenhua Cai, Ben Goertzel & Nil Geisweiller, [*OpenPsi: Realizing Dörner's "Psi" Cognitive Model in the OpenCog Integrative AGI Architecture*](https://doi.org/10.1007/978-3-642-22887-2_22) (AGI 2011, LNCS 6830, Springer) — the OpenPsi demands/modulators formalized in `OpenPsi/`.
- Dietrich Dörner, [*Bauplan für eine Seele*](https://www.spektrum.de/magazin/bauplan-fuer-eine-seele/825713) (Rowohlt, 1999) — the *Psi* theory underlying both OpenPsi and MicroPsi.
- Joscha Bach, [*Principles of Synthetic Intelligence: Psi — An Architecture of Motivated Cognition*](https://global.oup.com/academic/product/principles-of-synthetic-intelligence-9780195370676) (Oxford University Press, 2009) — the MicroPsi architecture (demands + PAD model) formalized in `MicroPsi/`.
- Shalom H. Schwartz, [*Universals in the Content and Structure of Values*](https://doi.org/10.1016/S0065-2601(08)60281-6), in *Advances in Experimental Social Psychology* 25 (1992), 1–65 — the ten-value circumplex in `Values/SchwartzValues.lean`.
- Jonathan Haidt, [*The Righteous Mind: Why Good People Are Divided by Politics and Religion*](https://righteousmind.com/) (Pantheon, 2012) — Moral Foundations Theory in `Values/MoralFoundations.lean`.
- Alan Gewirth, [*Reason and Morality*](https://press.uchicago.edu/ucp/books/book/chicago/R/bo25842059.html) (University of Chicago Press, 1978) — the Principle of Generic Consistency underlying the Gewirth/FOET ethics layer in `GodelClaw/Ethics/` and `Values/FOETBridge.lean`.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 64 .lean files, 0 with sorries.*
