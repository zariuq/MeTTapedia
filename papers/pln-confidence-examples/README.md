# PLN Confidence-Formula — Degrees-of-Freedom example pack

Runnable companion to the paper `../pln-credal-degrees-of-freedom.tex`.

The PLN truth value `<s,c>` (strength, confidence) is a **compression of a credal set**.
The paper characterizes *where it is determined* and *where it has degrees of freedom the two
numbers cannot see*. This pack turns each degree of freedom (Appendix A's "zoo") into a small,
intuitive, **runnable** demonstration — each one paired with the Lean theorem,
definition, or structure that is its real correctness reference.

## The honest contract (read this first)
- **Lean is the oracle.** Each degree of freedom has a Lean theorem/definition/structure reference;
  theorem-bearing oracle rows checked in this pass are axiom-clean up to the usual
  `{propext, Classical.choice, Quot.sound}` set. That Lean reference is the *claim*. See
  `DOF-INDEX.md` for the map.
- **`.metta` is intuition + reproducibility, NOT proof.** The `metta/*.metta` files run real PLN
  arithmetic so you can *see* a knob mattering, and reproduce the paper's numbers. Matching output is
  an illustration check, never a golden-test-as-proof.
- **Three tiers** (column in `DOF-INDEX.md`): *Runnable* (a real executable demo), *Structural*
  (a finite shadow of an infinite/joint fact — the Lean theorem is the real content), *Lean-ref*
  (the witness is a theorem; no standalone `.metta`).

## Run it
```sh
sh run_all.sh           # builds CeTTa (BUILD=core), runs every dof*.metta on it (+PeTTa if present)
```
Or one example, on either engine:
```sh
../../../hyperon/CeTTa/cetta            metta/dof01_kappa_calibration.metta   # CeTTa (HE mode)
cd ../../../hyperon/PeTTa && sh run.sh  <abs-path>/metta/dof01_kappa_calibration.metta   # PeTTa
```
Every `dof*.metta` example here is **portable across CeTTa(HE) and PeTTa** (float literals, standard
`import!`/`!`, no dialect-specific keywords). Where one source genuinely cannot serve both engines
we ship `*.he.metta` / `*.petta.metta` variants (none needed so far). See `docs/PORTABILITY.md`.

## Layout
```
metta/        one dofNN_<name>.metta per Runnable/Structural DoF (intuitive write-up inline)
lib/          pln_evidence.metta + lib_pln.metta (the portable PLN API; also copied into metta/ so imports resolve)
lean/         DOF-LEAN-MAP.md; the Lean canary source lives in ../../lean/mettapedia/Mettapedia/Logic/
docs/         PORTABILITY.md, EXPECTED.md (paper's numbers for spot-check)
DOF-INDEX.md  the 19-row master table: DoF -> metta file -> Lean oracle -> tier
run_all.sh    the reproducibility harness
```

## What you can verify in 30 seconds
`metta/dof01_kappa_calibration.metta` → `0.8333 / 0.3333 / 0.0909` = confidence of the *same* 5 units
of evidence at κ = 1 / 10 / 50. Same strength, three confidences: κ is a real calibration knob, and
the paper's κ table reproduces exactly. (See `docs/EXPECTED.md` for the full number set.)
