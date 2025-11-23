# P ≠ NP Formalization in Megalodon

## Status: Streamlined Proof Outline

This directory contains a formalization of Ben Goertzel's P ≠ NP proof strategy
(arXiv:2510.08814v1) in the Megalodon theorem prover for Proofgold.

**Philosophy:** This formalization uses `admit` for unproven theorems (deep results
that require additional infrastructure). True foundational axioms (ZFC, excluded
middle, choice) remain as `Axiom` in `00_preamble.mg`.

## File Structure (7 files)

| File | Description | Status |
|------|-------------|--------|
| `00_preamble.mg` | Set theory foundations, bits, XOR, vectors | **Proven** |
| `01_foundations.mg` | Category theory, F₂ field, complexity classes | Partial admits |
| `02_weakness_quantale.mg` | ExtNat quantale structure | Partial admits |
| `03_cnf_sat.mg` | CNF/SAT formalization, Cook-Levin | Admits |
| `04_masking.mg` | Mask group H_m = S_m ⋉ (Z₂)^m | Admits |
| `05_vv_isolation.mg` | Valiant-Vazirani isolation | Admits |
| `13_main_theorem.mg` | Main P ≠ NP theorem | **Proven from admits** |

## Classification

### True Axioms (Foundational - in 00_preamble.mg and 02_weakness_quantale.mg)

These are standard set-theoretic and logical axioms that cannot be eliminated:

| Axiom | Source | File |
|-------|--------|------|
| UPair, Union, Power, Empty | ZFC (Zermelo 1908) | `00_preamble.mg` |
| ordsucc, nat_p, omega | von Neumann (1923) | `00_preamble.mg` |
| classic (excluded middle) | Classical logic | `00_preamble.mg` |
| Eps_i_ax (choice) | Hilbert-Bernays (1939) | `00_preamble.mg` |
| omega_not_in_omega | Foundation axiom | `02_weakness_quantale.mg` |

### Admits (Unproven Theorems)

These are theorems we assume without proof. They are well-known results that
require extensive infrastructure to formalize, or key lemmas in the proof:

**Deep Theorems (well-established results):**

| Theorem | Source | File |
|---------|--------|------|
| Cook-Levin (SAT is NP-complete) | Cook 1971, Levin 1973 | `03_cnf_sat.mg` |
| 3-SAT NP-completeness | Karp 1972 | `03_cnf_sat.mg` |
| VV Isolation Lemma | Valiant-Vazirani 1986 | `05_vv_isolation.mg` |
| Linear hash pairwise independence | Carter-Wegman 1979 | `05_vv_isolation.mg` |
| K^poly chain rule, subadditivity | Li-Vitányi 2008 | `02_weakness_quantale.mg` |

**Derivable Lemmas (could be proven with more infrastructure):**

| Theorem | Notes |
|---------|-------|
| Mask group axioms | Need permutation inverse properties |
| vv_witness_unique | Need equip infrastructure |
| mask_preserves_SAT | Need semantic analysis |

**Main Proof Admits:**

The main theorem uses 3 key admits:

1. **self_reduction_upper_bound**: P=NP implies polytime witness extraction
2. **tuple_incompressibility**: Lower bound on witness tuple complexity
3. **quantale_clash**: Upper and lower bounds contradict

## Proof Architecture

```
┌─────────────────────────────────────────────────────┐
│                    FOUNDATIONS                       │
│  00_preamble.mg ──► 01_foundations.mg               │
│         │                   │                        │
│         ▼                   ▼                        │
│  02_weakness_quantale.mg    │                        │
│         │                   │                        │
│         ▼                   ▼                        │
│  03_cnf_sat.mg ──────► 04_masking.mg                │
│         │                   │                        │
│         ▼                   ▼                        │
│         └───────────► 05_vv_isolation.mg            │
└─────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────┐
│                    MAIN THEOREM                      │
│  13_main_theorem.mg: P ≠ NP via quantale clash      │
│                                                      │
│  Upper bound (self-reduction) + Lower bound (K^poly)│
│  = Contradiction in ExtNat quantale                 │
└─────────────────────────────────────────────────────┘
```

## Key Mathematical Structures

### Weakness Quantale (Section 2.1)
- **Carrier**: ExtNat = ω ∪ {ω}
- **Operation**: quant_add (+ with ω absorbing)
- **Order**: quant_le (standard order, ω greatest)
- **Measure**: K^poly(z|y) = polytime-bounded Kolmogorov complexity

### Mask Group H_m (Section 3)
- **Structure**: S_m ⋉ (Z₂)^m (semidirect product)
- **Elements**: (π, σ) where π permutes variables, σ flips signs
- **Action**: h(x)_i = σ_i ⊕ x_{π(i)}

### VV Instance (Section 4)
- **Components**: (F, A, b) - formula, hash matrix, target
- **Promise**: exactly one x satisfies F and Ax + b = 0
- **Witness**: vv_witness m inst extracts the unique solution

## Build Instructions

```bash
cd megalodon
./bin/megalodon -mizar -I examples/mizar/PfgMizarNov2020Preamble.mgs \
    PNP_grassroots/00_preamble.mg \
    PNP_grassroots/01_foundations.mg \
    PNP_grassroots/02_weakness_quantale.mg \
    PNP_grassroots/03_cnf_sat.mg \
    PNP_grassroots/04_masking.mg \
    PNP_grassroots/05_vv_isolation.mg \
    PNP_grassroots/13_main_theorem.mg
```

## What Was Removed

The following placeholder files were removed as they contained only trivial
admits (conclusions of `True`):
- `06_sils.mg` - SILS sketches
- `07_block_ensemble.mg` - Block distribution
- `08_neutrality.mg` - AP-GCT neutrality
- `09_sparsification.mg` - Template sparsification
- `10_switching.mg` - Switching-by-Weakness
- `11_small_success.mg` - Per-program success bounds

The mathematical content of these files is captured by the admits in
`13_main_theorem.mg` (specifically `tuple_incompressibility` and
`quantale_clash`).

## References

- **[Goertzel]** Goertzel, B. (2025). "P ≠ NP: A Non-Relativizing Proof via
  Quantale Weakness and Geometric Complexity". arXiv:2510.08814v1.
- **[Cook]** Cook, S.A. (1971). "The complexity of theorem-proving procedures".
- **[VV86]** Valiant & Vazirani (1986). "NP is as easy as detecting unique solutions".
- **[LV08]** Li & Vitányi (2008). "An Introduction to Kolmogorov Complexity".
- **[Lang]** Lang, S. (2002). "Algebra", 3rd ed.
