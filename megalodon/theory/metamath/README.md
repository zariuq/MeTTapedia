# MetaMath set.mm Translation to Megalodon

**Source**: http://grid01.ciirc.cvut.cz/~chad/mmmg.tgz
**Date**: Mid-2022 snapshot of MetaMath set.mm
**Files**: 40,558 theorem files
**Size**: 655MB uncompressed

## Overview

This directory contains a complete translation of MetaMath's set.mm library to Megalodon format. Each theorem is in its own `.mg` file with the naming convention:

```
mmset<number>_<theorem_name>.mg
```

For example:
- `mmset00001_a1ii.mg` - Theorem a1ii
- `mmset30904_elprob.mg` - Theorem elprob (probability element)

## File Structure

Each file contains:
1. **Definitions** - Type definitions and parameters
2. **Hypotheses** - Previously proven theorems used as lemmas
3. **Theorem** - The main theorem statement
4. **Proof** - Megalodon proof term

## Probability & Measure Theory Content

### Probability Theory (mmset309xx series)

Located in files `mmset30904` through `mmset30974`:

**Basic probability**:
- `mmset30904_elprob.mg` - Element of probability space
- `mmset30905_domprobmeas.mg` - Domain of probability measure
- `mmset30906_domprobsiga.mg` - Domain of probability σ-algebra
- `mmset30907_probtot.mg` - Total probability
- `mmset30908_prob01.mg` - Probability bounds [0,1]
- `mmset30909_probnul.mg` - Probability of null set

**Probability operations**:
- `mmset30913_probcun.mg` - Probability of countable union
- `mmset30914_probun.mg` - Probability of union
- `mmset30915_probdif.mg` - Probability of difference
- `mmset30916_probinc.mg` - Probability inclusion
- `mmset30917_probdsb.mg` - Probability disjoint sets bound

**Probability measures**:
- `mmset30918_probmeasd.mg` - Probability measure definition
- `mmset30919_probvalrnd.mg` - Probability value random
- `mmset30920_probtotrnd.mg` - Total probability random
- `mmset30921_totprobd.mg` - Total probability definition
- `mmset30922_totprob.mg` - Total probability theorem
- `mmset30924_probfinmeasb.mg` - Probability finite measure bound
- `mmset30925_probmeasb.mg` - Probability measure bound

**Conditional probability** (mmset30928-30933):
- `mmset30928_cndprobval.mg` - Conditional probability value
- `mmset30929_cndprobin.mg` - Conditional probability element
- `mmset30930_cndprob01.mg` - Conditional probability [0,1]
- `mmset30931_cndprobtot.mg` - Conditional probability total
- `mmset30932_cndprobnul.mg` - Conditional probability null
- `mmset30933_cndprobprob.mg` - Conditional probability is probability

**Applications**:
- `mmset30966_dstrvprob.mg` - Distribution probability
- `mmset30974_coinflipprob.mg` - Coin flip probability

### Measure Theory (mmset413xx series)

- `mmset41362_psmeasurelem.mg` - Pre-measure lemma
- `mmset41363_psmeasure.mg` - Pre-measure theorem

### General Measure Theory

Search for files containing:
- `measure` - Measure theory
- `sigma` - σ-algebras
- `borel` - Borel sets
- `lebesgue` - Lebesgue measure

## Usage

### Verifying a theorem:

```bash
cd /home/zar/claude/megalodon/theory/metamath/mmmg
megalodon mmset30904_elprob.mg
```

### Searching for theorems:

```bash
# Find probability theorems
ls -1 | grep prob

# Find measure theorems
ls -1 | grep measure

# Find σ-algebra theorems
ls -1 | grep sigma

# Search theorem content
grep -l "keyword" *.mg
```

### Example: Finding conditional probability

```bash
cd mmmg
ls -1 mmset30928_cndprob*.mg
```

Output:
```
mmset30928_cndprobval.mg
mmset30929_cndprobin.mg
mmset30930_cndprob01.mg
mmset30931_cndprobtot.mg
mmset30932_cndprobnul.mg
mmset30933_cndprobprob.mg
```

## Integration with Our Probability Formalization

These files can be referenced when:

1. **Verifying our definitions** match standard probability theory
2. **Finding lemmas** for difficult proofs
3. **Understanding proof patterns** from MetaMath community
4. **Cross-checking theorems** we've formalized

### Example: Compare our conditional probability

Our definition in `probability_theory/03_conditional_probability.mg`:
```megalodon
Definition conditional_prob : set -> set -> (set -> set) -> set -> set -> set :=
  fun Omega F P A B =>
    if P B = R_zero then R_zero else (P (A :/\: B)) :/: (P B).
```

MetaMath equivalent in `mmset30928_cndprobval.mg`:
```
(P(A|B) = P(A∩B) / P(B) when P(B) ≠ 0)
```

## Notes

- **Translation format**: Uses Church-encoded HOL like our work
- **Proof style**: Functional proof terms (not tactic-based)
- **Dependencies**: Each file is self-contained with all hypotheses
- **Naming**: `mmset<number>` reflects original MetaMath set.mm ordering

## License

See `LICENSE` file in this directory (from original MetaMath project).

## References

- MetaMath set.mm: http://us.metamath.org/mpeuni/mmset.html
- Original translation: Chad Brown (CIIRC/CTU Prague)
- Megalodon: http://grid01.ciirc.cvut.cz/~chad/megalodon/
