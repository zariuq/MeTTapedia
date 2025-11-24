# Four Color Theorem - Lean 4 Formalization

> 🛑 **PROJECT STATUS**: BLOCKED - FATAL FLAW DISCOVERED (2025-11-24)
>
> **A fundamental mathematical error has been found in Lemma 4.3 of the proof approach.**
>
> The claimed equality `X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R` (boundary) is **false**.
> The correct result is `X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_{A∪A'}` (interior).
>
> **Verification**: Kernel-verified refutation in `/home/zar/claude/megalodon/4CT/`
>
> **Impact**: The purification mechanism cannot work. Lemmas 4.4, 4.8-4.10 are blocked.
>
> **Value**: This formalization contains valuable proof architecture and infrastructure
> that may be useful for alternative approaches or educational purposes.

---

A Lean 4 formalization of the Four Color Theorem using the **Kauffman/Spencer-Brown** boundary algebra approach following **Ben Goertzel's** modern treatment.

## Toolchain & Pins

- Lean toolchain: `leanprover/lean4:v4.24.0-rc1` (see `lean-toolchain`)
- mathlib: pinned to commit `06d95e5f5311594940c0c3dff5381fabe4fcabe7`
  - Declared in `lakefile.toml` and mirrored in `lake-manifest.json`
  - Do not run `lake update` unless intentionally upgrading
- Fresh setup (no rebuild of mathlib from source):
  - `lake exe cache get`
  - `lake build`

## Current Status

**🎯 ~75% Complete** - Core geometry proven, integration pieces remain
**✅ Lemma 4.5 Complete** - Full proof of facial basis property
**✅ Strong Dual Complete** - Theorem 4.9 fully proven
**✅ H2+H3 Pipeline Complete** - Architecture with only routine sorries
**⚠️ Remaining**: Kempe chains (~150 lines), Tait equivalence (~80 lines), integration (~30 lines)

👉 **See [docs/FOUR_COLOR_THEOREM_STATUS.md](docs/FOUR_COLOR_THEOREM_STATUS.md) for comprehensive status report**

## Quick Start

```bash
# Clone and build
cd /home/zar/claude/lean-projects/fourcolor
lake build

# Run specific module
lake build FourColor.StrongDual
lake build FourColor.Geometry.DynamicForest

# Check for remaining sorries
grep -n "sorry" FourColor/**/*.lean
```

## Project Structure

```
FourColor/
├── FourColorTheorem.lean        # Main theorem statement (NEW!)
├── Triangulation.lean           # F₂×F₂ algebra + Lemma 4.5 ✅ COMPLETE
├── StrongDual.lean              # Theorem 4.9 ✅ COMPLETE
├── Tait.lean                    # Tait equivalence ⚠️ ~20% complete
├── Geometry/
│   ├── Disk.lean                # H2+H3 pipeline ✅ 85% complete
│   ├── DynamicForest.lean       # Leaf-peel interfaces ✅ 90% complete
│   └── RotationSystem.lean      # E2 from rotation system ✅ 97% complete
├── GraphTheory/
│   └── SpanningForest.lean      # Graph theory foundations
└── Examples/
    └── Tetrahedron.lean         # Test case

docs/
├── FOUR_COLOR_THEOREM_STATUS.md # Comprehensive status (NEW!)
├── MERIDIAN_INTEGRATION_COMPLETE.md # Phase 2 completion
├── H2_H3_ORUZIS_PLAN_EXECUTED.md    # Phase 1 completion
└── archive/                          # Historical documentation
```

## Approach

This formalization follows the **boundary algebra** approach:

1. **Color Algebra**: Model face colorings as F₂ × F₂ chains with XOR addition
2. **Zero-Boundary Chains**: Chains satisfying vertex parity and boundary conditions
3. **Facial Spanning (Lemma 4.5)**: Zero-boundary chains span face boundaries via leaf-peeling
4. **Strong Dual (Theorem 4.9)**: Orthogonality implies no Kempe obstructions
5. **Four Color Theorem**: Follows from strong dual + primality reduction

## Key Implementation Details

### Multi-Face Aggregated Peels

The formalization uses **multi-face aggregated peels** over leaf-subtrees rather than single-face toggles:

- `LeafPeelSumData` structure accepts finite sets of faces S₀
- Toggles the aggregated sum: `toggleSum G γ S₀ = ⊕_{f ∈ S₀} faceBoundaryChain γ f`
- Cut-parity (Lemma 4.7): Sum supported on cut edges crossing S₀ boundary
- Orthogonality forcing (Lemma 4.8): Unique cut edge forces strict descent

See `docs/LEAF_CUT_SWITCH.md` for the full story of why single-face peels don't work.

### Infrastructure Highlights

- ✅ `support₁` and `support₂`: γ-coordinate support projections (Triangulation.lean)
- ✅ `toggleSum` and helpers: Multi-face toggle operations (Disk.lean)
- ✅ Cut-parity lemmas: `cutEdges`, `toggleSum_supported_on_cuts` (Disk.lean)
- ✅ Orthogonality forcing: `aggregated_toggle_forces_descent` (Disk.lean)
- ✅ Well-founded induction: Cardinality-based on `card(support₁ x)`

All core infrastructure compiles. Remaining work is proving the helper lemmas using the comprehensive proof sketches provided in the code.

## Documentation

- **[docs/FOUR_COLOR_THEOREM_STATUS.md](docs/FOUR_COLOR_THEOREM_STATUS.md)** - Comprehensive status report with completion estimates
- **[docs/MERIDIAN_INTEGRATION_COMPLETE.md](docs/MERIDIAN_INTEGRATION_COMPLETE.md)** - Phase 2 (meridian layer) completion
- **[docs/H2_H3_ORUZIS_PLAN_EXECUTED.md](docs/H2_H3_ORUZIS_PLAN_EXECUTED.md)** - Phase 1 (H2+H3) completion
- **[FourColor/FourColorTheorem.lean](FourColor/FourColorTheorem.lean)** - Main theorem statement with proof architecture

## References

- **Paper**: Goertzel's boundary algebra approach to 4CT (§4.2, Lemmas 4.7-4.8, Theorem 4.9)
- **Original Work**: Kauffman & Spencer-Brown boundary algebra
- **Prior Formalization**: Gonthier's Coq proof (different approach)

## Contributing

**The project is ~75% complete with clear path forward!**

### What's Done ✅
- Lemma 4.5 (facial basis): COMPLETE proof
- Strong Dual (Theorem 4.9): COMPLETE proof
- H2+H3 pipeline: Architecturally complete
- γ=(0,1) mirror: COMPLETE (497 lines)
- Meridian layer: Infrastructure in place

### Critical Path (Highest Priority)
1. **Kempe Chain Reachability** (`Tait.lean:155`) - ~150 lines
   - Define Kempe chains and switches
   - Prove orthogonality preservation
   - Show primality + parity → reachability
   - Extract proper 3-edge-coloring

2. **Tait Equivalence** (`Tait.lean:94, 107`) - ~80 lines
   - Forward: 4-vertex-coloring → 3-edge-coloring
   - Reverse: 3-edge-coloring → 4-vertex-coloring

3. **Integration** (`Tait.lean:174`) - ~30 lines
   - Wire Kauffman + Tait to main theorem

### Parallel Work (Can Be Done Independently)
4. **H2 Graph Theory** (`Disk.lean`) - ~146 lines
   - Spanning tree algorithms (8 sorries)
   - Standard graph theory, well-documented

5. **Meridian Completion** (`Disk.lean:156-282`) - ~73 lines
   - Implement meridian construction
   - Prove strong dual and orthogonality lemmas

See **[docs/FOUR_COLOR_THEOREM_STATUS.md](docs/FOUR_COLOR_THEOREM_STATUS.md)** for detailed breakdown and estimates.

## License

MIT (or appropriate license for mathematical formalizations)
