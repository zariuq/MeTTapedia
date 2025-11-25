# Graph Theory Formalization

**Location**: `/home/zar/claude/megalodon/graph_theory/`

**Purpose**: General graph theory formalization in Megalodon, independent of specific applications.

---

## Files

- **`graph_basics.mg`** - Core graph theory definitions and theorems
  - Chapters 1-6 covering vertices, edges, paths, connectivity, cliques, independence, coloring
  - ~1549 lines, verifies with Egal preamble

- **`CODEX_GRAPH_THEORY_GUIDE.md`** - Development guide
  - Parser rules and best practices
  - Chapter outlines and theorem roadmap
  - Verification workflow

---

## Verification

```bash
cd /home/zar/claude/megalodon
./bin/megalodon -I Megalodon/examples/egal/PfgEAug2022Preamble.mgs graph_theory/graph_basics.mg
```

---

## Distinction from Ramsey Theory

**This directory** (`graph_theory/`): General graph theory applicable to any domain

**Ramsey directory** (`ramsey36/`): Specific application to Ramsey(3,3) = 6 problem

Graph theory is a foundational theory that Ramsey theory builds upon, hence the separation.

---

## Current Status

**Chapters Complete**:
- ✅ Chapter 1: Basic definitions (graphs, vertices, edges)
- ✅ Chapter 2: Paths and connectivity
- ✅ Chapter 3: Cliques and independent sets
- ✅ Chapter 4: Triangles and K4
- ✅ Chapter 5: Blocks (2-vertex-connected components)
- ⚠️ Chapter 6: Graph coloring (definitions added, proofs in progress)

**Next Steps**:
- Prove `bipartite_is_2_colorable` theorem
- Add chromatic number concepts
- Extend to hypergraphs (if needed for applications)
