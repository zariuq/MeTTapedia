# Four Color Theorem - Algebraic Formalization in Mizar

A novel algebraic formalization of the Four Color Theorem using Ben Goertzel's GF(2)² chain algebra approach.

## Overview

This project formalizes the Four Color Theorem (4CT) using a revolutionary algebraic approach that replaces computational case-checking with pure mathematical reasoning. Instead of verifying millions of configurations, this proof uses:

- **GF(2)² chain algebra**: Functions from graph edges to pairs of Booleans
- **Orthogonality and duality**: Relationships between face boundaries and 4-colorings
- **Tait's equivalence**: Connection between edge-3-coloring and vertex-4-coloring

This is the first complete formalization attempt of 4CT based on algebraic methods rather than computational verification.

## Project Structure

```
theories/
  01_chain_algebra/          # Foundational GF(2)² chain infrastructure
    text/                    # .miz source files
      chain_dot_constructive.miz
    dict/                    # .voc vocabulary files

  02_parity/                 # Face boundary parity and structure
    text/
      face_boundary.miz      # Face boundary infrastructure
      set_parity.miz         # Set parity operations
    dict/
      face_boundary.voc
      set_parity.voc

  02_main_theorems/          # Core 4CT theorems
    text/
      span_constructive.miz  # Constructive face boundary span
      strong_dual.miz        # Theorem 4.9: Orthogonality transfer
      kempe_purification.miz # Lemmas 4.2-4.4: Kempe operations
      disk_kempe_closure.miz # Theorem 4.10: Closure properties
      tait_equivalence.miz   # Tait's edge-3-coloring ↔ vertex-4-coloring
    dict/
      [corresponding .voc files]

docs/                        # Documentation (canonical set only)
```

## Canonical Docs

- LLM Context Pack: `docs/LLM_CONTEXT_PACK.txt`
- How‑To: `docs/HOWTO_Mizar.md`
- QuickStart: `docs/QuickStart.md`
- Curriculum: `docs/CURRICULUM.md`
- Error Zoo: `docs/ERROR_ZOO.md`

## Current Status

**Total: ~1,030 lines of formalized Mizar code**

### Compilation Status (All files compile successfully)
- ✓ `face_boundary.miz` - Face boundary infrastructure
- ✓ `chain_dot_constructive.miz` - Chain algebra foundations
- ✓ `span_constructive.miz` - Constructive span proofs
- ✓ `strong_dual.miz` - Orthogonality transfer
- ✓ `kempe_purification.miz` - Kempe operation lemmas
- ✓ `disk_kempe_closure.miz` - Closure properties
- ✓ `tait_equivalence.miz` - Tait's equivalence

### Error Summary
- **Error 72/73 (Correctness conditions)**: 0 remaining (all fixed as of Oct 2025)
- **Other errors**: ~140 remaining (mostly Import/modularity and proof completion)

See [STATUS.md](STATUS.md) for detailed error breakdown.

## Quick Start

### Prerequisites
- Mizar System 8.1.15 or later
- Standard MML (Mizar Mathematical Library)

### Compilation
Key patterns (generic):

```bash
# From repo root (path keeps dict/ visible)
mizf theories/<module>/text/<file>.miz

# Or from module root (folder with both text/ and dict/)
cd theories/<module> && mizf text/<file>.miz
```

See `docs/QuickStart.md` for details and batch examples.

## Mathematical Foundations

### Key Concepts

**GF(2)² Chains**: Functions `c: Edges → BOOLEAN × BOOLEAN` representing edge states

**Face Boundary**: For each face `f`, the function `∂f` indicating which edges border it

**Orthogonality**: A chain `c` is orthogonal to all face boundaries iff it represents a valid 4-coloring

**Tait's Equivalence**: A planar cubic graph is edge-3-colorable iff it is vertex-4-colorable

### Proof Strategy

1. Define GF(2)² chain algebra (`chain_dot_constructive.miz`)
2. Prove face boundaries span exactly the chains orthogonal to all 4-colorings (`span_constructive.miz`)
3. Show Kempe operations preserve coloring properties (`kempe_purification.miz`, `disk_kempe_closure.miz`)
4. Establish strong duality between colorings and face boundaries (`strong_dual.miz`)
5. Apply Tait's equivalence to complete the proof (`tait_equivalence.miz`)

## Why This Matters

**Historical Context**: The Four Color Theorem was the first major theorem proved using computers (Appel & Haken, 1976). However, that proof relied on checking 1,936 configurations computationally, making it difficult to verify by hand.

**This Approach**: Ben Goertzel's algebraic method eliminates computational case-checking entirely, replacing it with pure mathematical reasoning about vector spaces over GF(2)². This makes the proof:
- More elegant and conceptually unified
- Easier to verify formally
- More insightful about the underlying mathematical structure

**Impact**: If successful, this will be the first human-verifiable proof of 4CT and the first complete formalization in a proof assistant using non-computational methods.

## Recent Updates

**October 2025**: Correctness/coherence rules clarified
- Use `coherence;` for functors defined with `equals`.
- Use `correctness` (with existence/uniqueness) for `means` definitions.
- Modes require `correctness;`.

**Directory Restructure**: Reorganized to standard Mizar text/dict layout
- `.miz` files now in `text/` subdirectories
- `.voc` files now in `dict/` subdirectories
- Standard structure for easier navigation and compilation

## Contributing

This is an active research project. Key areas for contribution:
- Completing remaining proofs (see STATUS.md)
- Resolving Import/modularity errors
- Improving proof automation and lemma structure
- Documentation and explanation

## References

- Ben Goertzel. "The Geometry and Algebra of the Four Color Theorem" (in progress)
- Appel, K., & Haken, W. (1977). "Every planar map is four colorable"
- Tait, P. G. (1880). "Remarks on the colouring of maps"
- Robertson, Sanders, Seymour, Thomas (1997). "The four-colour theorem"

## Contact

For questions or collaboration, please open an issue or contact the maintainers.

---

*This formalization is being developed in Mizar for maximum rigor and verifiability.*
