import Mettapedia.Languages.ProcessCalculi.MORK.MORKCommBridge
import Mettapedia.Languages.ProcessCalculi.MORK.PathMapBridge
import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.ProcessCalculi.MORK.MeTTaILBridge

/-!
# MORK: Minimal Model 2 (MM2) Formalization

MORK (MM2 Object-Relational Kernel) is the execution substrate for MeTTa-Compiler.
This module formalises MORK's execution semantics and proves its structural
correspondence with the MQ-calculus COMM rule.

## Structure

```
MORK/
  Syntax.lean          — MM2 atoms, exec rules, patterns, templates, sinks
  Space.lean           — Space = Finset Atom; firing semantics; matchAtom/applySubst
  ThreePhaseExec.lean  — Phase protocol: unfold (0–31), base (32–63), fold (64–95)
  MORKCommBridge.lean  — Bridge: MORK binary fold ↔ MQ-calculus CommReduction
  PathMapBridge.lean   — Bridge: MORK space transitions ↔ PathMap lattice ops
  MatchSpec.lean       — Relational spec of atom matching (sound/complete fragment)
  MeTTaILBridge.lean   — Bridge: DeclReduces ↔ MORK fireRule
```

## Key Results

- `phase_ranges_disjoint`: unfold/base/fold priority bands are mutually disjoint
- `phase_priority_monotone`: priorities are ordered unfold < base < fold
- `mork_fold_is_comm`: any binary MORK fold step corresponds to a MQ CommReduction
- `mork_fold_both_outcomes_exist`: MORK fold is non-deterministic (both sub-results possible)
- `mork_mq_nondeterminism_corresponds`: MORK non-determinism ↔ MQ comm_both_outcomes
- `applyBase_eq_lattice_ops`: MORK base step = PathMap psubtract + pjoin
- `applyFold_eq_lattice_ops`: MORK fold step = PathMap psubtract chain + pjoin
- `applySubst_commutes`: MORK applySubst commutes with morkPatternToAtom
- `declReduces_implies_mork_fire`: DeclReduces → MORK fireRule fires (topRule case)

## Spec status

This is a CORE MORK formalization capturing the stable 2026-02 semantics.
The spec intentionally covers:
- The three-phase protocol (stable)
- Binary non-determinism (the fundamental quantum-inspired structure)
- Connection to MQ-calculus COMM (the theoretical foundation)

Details likely to change in future MORK versions (NOT formalized here):
- Exact sub-query naming convention (`(sub-k qid)` format)
- MAX_DEPTH constant (32 by default)
- Sink priority refinements (streaming/partial-fold)
- MM2 bytecode instruction set extensions

**Canary theorems** in `MORKCommBridge.lean` and `ThreePhaseExec.lean` will
fail to compile if the stable invariants change.
-/
