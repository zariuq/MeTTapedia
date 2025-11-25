# Probability Theory Formalization for Megalodon

## Purpose

This directory contains a formalization of probability theory in Megalodon's Egal mode, building from Kolmogorov's axioms to support the Knuth-Skilling papers on quantum foundations.

## Structure

```
probability_theory/
├── README.md                          # This file
├── GEMINI_FORMALIZATION_PROMPT.md     # Main instructions for Gemini
├── PROGRESS.md                        # Progress tracking (update after each milestone)
├── 01_sigma_algebras.mg               # σ-algebras and fields
├── 02_probability_measures.mg         # Probability spaces and measures
├── 03_conditional_probability.mg      # Conditional probability, product rule, Bayes
├── 04_independence.mg                 # Independence and product measures
└── examples/                          # Concrete examples and tests
    ├── coin_flip.mg
    └── dice.mg
```

## Reference Materials

- **Textbook**: Billingsley "Probability and Measure" 3rd Edition
  - Location: `/home/zar/claude/literature/Probability_Theory/Probability_and_Measure_Third_Edition_Patrick_Billingsley.pdf`
  - Key sections: Chapter 1 §2-6

- **Target papers**: Knuth & Skilling
  - "The symmetrical foundation of Measure, Probability and Quantum theories"
  - "The Arithmetic of Uncertainty unifies Quantum Formalism and Relativistic Spacetime"

## Verification

To verify a file:
```bash
cd /home/zar/claude/megalodon/probability_theory
/home/zar/claude/megalodon/bin/megalodon -egal \
  -I /home/zar/claude/megalodon/Megalodon/examples/egal/PfgEAug2022Preamble.mgs \
  01_sigma_algebras.mg
```

Exit code 0 = Success!

## Development Workflow

1. Read `GEMINI_FORMALIZATION_PROMPT.md` for detailed instructions
2. Start with Phase 1 (`01_sigma_algebras.mg`)
3. After each definition/theorem:
   - Verify with megalodon
   - Update `PROGRESS.md`
   - Commit progress
4. Move to next phase only when current phase is stable
5. Add examples to test definitions

## Current Status

See `PROGRESS.md` for detailed progress tracking.

**Phase 1**: Not started
**Phase 2**: Not started
**Phase 3**: Not started
**Phase 4**: Not started

## Key Definitions

### Phase 1: σ-Algebras
- `is_field` - Finitely additive family of sets
- `is_sigma_field` - Countably additive family of sets
- Helper: `setminus`, `setunion`, `setinter`, `bigcup_nat`

### Phase 2: Probability Measures
- `is_probability_space` - (Ω, F, P) satisfying Kolmogorov axioms
- Properties: monotonicity, complement rule, inclusion-exclusion

### Phase 3: Conditional Probability
- `conditional_prob` - P(A|B) = P(A∩B)/P(B)
- Product rule: P(A∩B) = P(A)·P(B|A)
- Bayes' theorem

### Phase 4: Independence
- `independent_events` - P(A∩B) = P(A)·P(B)
- Mutual independence for families

## Philosophy

**Prove what you can, admit what you must, document everything.**

When a proof is too complex:
1. Admit as axiom with clear TODO comment
2. Mark priority (HIGH/MEDIUM/LOW)
3. Continue building on top
4. Return to prove it later if possible

The goal is a **working foundation**, not perfection on first pass.

## Contact

This formalization is part of the Knuth-Skilling quantum foundations project.
For questions or issues, see the main project documentation.
