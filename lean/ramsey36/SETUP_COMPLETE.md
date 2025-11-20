# Ramsey36 Project Setup - COMPLETE ✅

**Date**: 2025-11-20

## What Was Done

### 1. Mathlib Cache Sharing Configuration ✅

**Problem**: Without sharing mathlib builds, each project would rebuild mathlib from scratch (30+ minutes).

**Solution**: Configured ramsey36 to use **identical** Lean version and mathlib commit as fourcolor:
- Lean toolchain: `v4.24.0-rc1` (changed from v4.25.1)
- Mathlib commit: `06d95e5f5311594940c0c3dff5381fabe4fcabe7`

**Files Modified**:
- `lean-toolchain` - Downgraded to match fourcolor
- `lakefile.toml` - Added mathlib dependency with pinned revision

**Result**: Both projects share the same mathlib cache. Rebuilds take **5.8 seconds** instead of 30+ minutes!

### 2. Mathlib Infrastructure Survey ✅

Surveyed `Mathlib.Combinatorics.SimpleGraph.*` to identify what exists:

**Available in Mathlib** (Ready to use):
- ✅ `SimpleGraph` - Basic graph structure
- ✅ `IsClique`, `IsNClique`, `CliqueFree` - Clique operations
- ✅ `IsIndepSet`, `IsNIndepSet`, `IndepSetFree` - Independent set operations
- ✅ `neighborSet`, `neighborFinset`, `commonNeighbors` - Neighborhood operations
- ✅ `degree`, `IsRegularOfDegree` - Degree operations
- ✅ `isIndepSet_neighborSet_of_triangleFree` - Key lemma for triangle-free graphs
- ✅ `sum_degrees_eq_twice_card_edges` - Handshaking lemma

**Need to Define** (Project-specific):
- Ramsey number definition
- R(3,5) = 14 (prerequisite)
- The 17-vertex critical graph
- Specific counting arguments

### 3. Ramsey36/Basic.lean - Complete Skeleton ✅

Created comprehensive definitions file (159 lines) with:

**Core Definitions**:
```lean
noncomputable def ramseyNumber (k l : ℕ) : ℕ := ...
def HasRamseyProperty (k l : ℕ) (G : SimpleGraph (Fin n)) : Prop := ...
def TriangleFree (G : SimpleGraph α) : Prop := G.CliqueFree 3
def NoKIndepSet (k : ℕ) (G : SimpleGraph α) : Prop := G.IndepSetFree k
def commonNeighborsCard (G : SimpleGraph α) [LocallyFinite G] (v w : α) : ℕ := ...
```

**Proof Structure** (following paper exactly):
- `criticalGraph17` - The 17-vertex counterexample
- `claim1_five_regular` - Triangle-free + no 6-IS ⟹ 5-regular
- `claim2_neighbor_structure` - 4 + 8 split of non-neighbors
- `claim3_four_cycle` - p-vertices form 4-cycle
- `final_contradiction` - Exhaustive case analysis
- `ramsey_three_six_lower` - R(3,6) ≥ 18
- `ramsey_three_six_upper` - R(3,6) ≤ 18
- `ramsey_three_six` - Main theorem (combines lower + upper)

**Status**: ✅ Compiles with zero errors, only expected warnings for sorries

### 4. Documentation ✅

Created comprehensive project documentation:

**CLAUDE.md** (300+ lines):
- Build rules matching fourcolor
- Mathlib pinning strategy
- Project structure
- Available mathlib infrastructure
- Formalization insights
- Estimated effort breakdown

**README.md**: Project overview and status

**PAPER_ANALYSIS.md**: Detailed feasibility analysis (6700+ chars)

**FORMALIZATION_ROADMAP.md**: Week-by-week implementation plan (8000+ chars)

## Build Performance

### Initial Setup
```bash
lake exe cache get    # Downloaded prebuilt mathlib cache
lake build Ramsey36   # Built project: 5.8 seconds ✅
```

### Comparison
| Operation | Without Cache | With Cache |
|-----------|--------------|------------|
| First build | 30-40 minutes | 5.8 seconds |
| Rebuild after edit | 3-5 seconds | 3-5 seconds |

## Verification

### Build Test
```bash
$ export LAKE_JOBS=3 && lake build Ramsey36
✔ [1101/1102] Built Ramsey36 (3.8s)
Build completed successfully (1102 jobs).

real    0m5.828s
```

### Cache Verification
Both projects have mathlib builds:
- `fourcolor/.lake/packages/mathlib/.lake/build/lib/` ✅
- `ramsey36/.lake/packages/mathlib/.lake/build/lib/` ✅

Same Lean version (v4.24.0-rc1) and mathlib commit means **shared cache**.

## Next Steps (For Future Work)

Following `FORMALIZATION_ROADMAP.md`:

### Phase 1: Lower Bound (Week 1-2)
- [ ] Define `criticalGraph17` from paper Figure 1
- [ ] Prove `criticalGraph17_triangleFree` (decidable)
- [ ] Prove `criticalGraph17_no_6_indep` (decidable)
- [ ] Complete `ramsey_three_six_lower`

### Phase 2: Claim 1 (Week 3)
- [ ] Formalize or axiomatize R(3,5) = 14
- [ ] Implement `claim1_five_regular` proof
- [ ] Use triangle-free + R(3,5) = 14 to derive regularity

### Phase 3: Claim 2 (Week 4-5)
- [ ] Edge counting between induced subgraphs
- [ ] Prove 4 + 8 split of non-neighbors
- [ ] Complete `claim2_neighbor_structure`

### Phase 4: Claim 3 (Week 6)
- [ ] Analyze adjacency structure of p-vertices
- [ ] Complete `claim3_four_cycle`

### Phase 5: Final (Week 7-8)
- [ ] Implement vertex labeling system
- [ ] Exhaustive case analysis
- [ ] Complete `final_contradiction`
- [ ] Derive `ramsey_three_six_upper`

### Phase 6: Polish (Week 9-10)
- [ ] Remove all sorries
- [ ] Optimize proof terms
- [ ] Write documentation
- [ ] Prepare for publication (ITP 2026?)

## Key Files

```
/home/zar/claude/lean-projects/ramsey36/
├── CLAUDE.md                    # Build rules and project guide
├── README.md                    # Project overview
├── PAPER_ANALYSIS.md            # Feasibility analysis
├── FORMALIZATION_ROADMAP.md     # Week-by-week plan
├── SETUP_COMPLETE.md            # This file
├── lakefile.toml                # Mathlib pinned to fourcolor's version
├── lean-toolchain               # Lean v4.24.0-rc1
├── Ramsey36.lean                # Root module
└── Ramsey36/
    └── Basic.lean               # Main definitions (159 lines, 0 errors)
```

## Summary

✅ **Project fully set up and ready for formalization work!**

Key achievements:
- Mathlib cache sharing with fourcolor (5.8s builds!)
- Complete skeleton with all theorem statements
- Comprehensive documentation
- Zero compilation errors
- Clear roadmap for 7-10 week formalization

The hard infrastructure work is done. Now it's just filling in the proofs! 🚀
