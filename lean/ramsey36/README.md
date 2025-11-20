# R(3,6) = 18 - Lean 4 Formalization

Formalization of David Cariolaro's elementary proof of the Ramsey number R(3,6) = 18.

## Paper

**Title**: On the Ramsey number R(3,6)  
**Author**: David Cariolaro (Academia Sinica, Taiwan)  
**Source**: Australian Journal of Combinatorics, Vol 37 (2007), 301-305  
**PDF**: `paper/2025_02_07_b1cb8ce31b5aabf14429g.tex`

## Main Result

**Theorem**: R(3,6) = 18

This means that in any graph with 18 vertices, either:
- There exist 3 mutually adjacent vertices (a triangle), OR
- There exist 6 mutually non-adjacent vertices (an independent set)

And 17 vertices is insufficient (there exists a counterexample graph).

## Project Status

🚧 **NEWLY CREATED** - Infrastructure phase

### Current Progress

- [x] Project setup
- [x] Basic definitions skeleton
- [ ] Ramsey number definition
- [ ] R(3,5) = 14 (prerequisite)
- [ ] 17-vertex critical graph
- [ ] Claim 1: 5-regularity
- [ ] Claim 2: Neighborhood structure  
- [ ] Claim 3: 4-cycle
- [ ] Final contradiction
- [ ] Complete proof

## Building

```bash
lake build
```

## Structure

```
Ramsey36/
├── Basic.lean          # Definitions and main theorem statements
├── Critical17.lean     # The 17-vertex counterexample (TODO)
├── Claim1.lean         # 5-regularity proof (TODO)
├── Claim2.lean         # Neighborhood structure (TODO)
├── Claim3.lean         # 4-cycle proof (TODO)
└── Final.lean          # Final contradiction (TODO)
```

## Formalization Approach

See `PAPER_ANALYSIS.md` for detailed feasibility analysis.

**Estimated effort**: 800-1200 lines of Lean, 7-10 weeks

## Why This Project?

- **Accessible**: Much shorter than Four Color Theorem
- **Beautiful**: Elegant elementary proof
- **Educational**: Great example of graph theory formalization
- **Novel**: First elementary Ramsey proof in a theorem prover?
- **Foundation**: Opens door to R(3,7), R(4,4), etc.

## References

1. David Cariolaro. On the Ramsey number R(3,6). Australian J. Combinatorics 37 (2007), 301-305.
2. [Radziszowski's Dynamic Survey on Small Ramsey Numbers](http://www.combinatorics.org/ojs/index.php/eljc/article/view/DS1)
