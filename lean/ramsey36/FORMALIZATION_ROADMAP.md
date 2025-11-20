# R(3,6) = 18 Formalization Roadmap

## Quick Assessment: ✅ HIGHLY DOABLE!

**Difficulty**: ⭐⭐⭐ Medium (similar to Four Color infrastructure, much shorter proof)  
**Time Estimate**: 7-10 weeks for experienced Lean developer  
**LOC Estimate**: 800-1200 lines

## Why This is Perfect

1. **Self-contained**: Elementary combinatorics, no deep theorems
2. **Finite**: Only 18 vertices (decidable properties!)
3. **Beautiful**: Elegant proof with clear structure
4. **Precedent**: Four Color shows graph theory formalization is viable
5. **Impact**: First elementary Ramsey proof formally verified?

## The Proof at a Glance

### Lower Bound (Easy)
Exhibit a 17-vertex triangle-free graph with no 6-IS.
- **Method**: Concrete graph construction + decidable verification
- **LOC**: ~100 lines

### Upper Bound (The Work)
Prove any triangle-free 18-vertex graph has a 6-IS by contradiction.

**Assume**: G is triangle-free, 18 vertices, no 6-IS

**Claim 1 (⭐⭐)**: G is 5-regular  
**Claim 2 (⭐⭐⭐)**: Precise neighborhood structure (4 + 8 split)  
**Claim 3 (⭐⭐⭐)**: The 4 "p-vertices" form a 4-cycle  
**Final (⭐⭐⭐⭐)**: Exhaustive case analysis → contradiction

## Infrastructure Needed

### From Mathlib (Check What Exists)
```lean
-- Probably available:
SimpleGraph, Fintype graphs, degree, neighborhood
CliqueFree, IsRegular, independent sets

-- May need to add:
Ramsey number definition
R(3,5) = 14 (prerequisite or axiom)
Neighborhood intersection counting lemmas
```

### To Develop
```
Phase 1: Basics (Week 1-2)
- [ ] Ramsey number definition (20 lines)
- [ ] Triangle-free predicate (10 lines)  
- [ ] Independent set helpers (30 lines)
- [ ] Neighborhood intersection (40 lines)

Phase 2: Lower Bound (Week 3)
- [ ] 17-vertex graph construction (60 lines)
- [ ] Triangle-free verification (30 lines)
- [ ] No 6-IS verification (40 lines)

Phase 3: Claim 1 (Week 4)
- [ ] Degree bound from triangle-free (50 lines)
- [ ] R(3,5) = 14 usage (50 lines)
- [ ] 5-regular conclusion (50 lines)

Phase 4: Claim 2 (Week 5-6)
- [ ] Edge counting setup (100 lines)
- [ ] 4 + 8 split proof (150 lines)
- [ ] Distinctness properties (50 lines)

Phase 5: Claim 3 (Week 7-8)
- [ ] Subgraph structure (100 lines)
- [ ] 5-cycle argument (100 lines)
- [ ] 4-cycle conclusion (50 lines)

Phase 6: Final Contradiction (Week 9-10)
- [ ] Vertex labeling system (100 lines)
- [ ] Case explosion management (200 lines)
- [ ] Contradiction derivation (100 lines)
```

**Total**: ~1200 lines across 10 weeks

## Key Insights for Formalization

### 1. Decidability is Your Friend
With Fin 18, everything is decidable! Use:
```lean
decide  -- For concrete computations
fin_cases  -- For exhaustive case analysis
```

### 2. Subtype for Vertex Sets
```lean
def PVertices (G : SimpleGraph (Fin 18)) (v : Fin 18) :=
  {u : Fin 18 // u ∉ G[v] ∧ (G[u] ∩ G[v]).card = 1}
```

### 3. Finset Cardinality Lemmas
You'll need many of these (similar to NoDigons work):
```lean
have h_count : (edges_between s t).card = k := by
  -- Counting arguments
```

### 4. R(3,5) = 14 Strategy
**Option A**: Axiomatize temporarily
```lean
axiom ramsey_three_five : ramseyNumber 3 5 = 14
```

**Option B**: Formalize it! (Similar techniques, good warmup)

### 5. The Final Step Will Be Ugly
Accept that the last contradiction involves:
- 18 labeled vertices  
- Many subcases
- Lots of "by symmetry" reasoning

**Solution**: Break it into MANY small lemmas, use automation aggressively.

## Comparison to Four Color

| Aspect | Four Color | R(3,6) |
|--------|-----------|--------|
| **Pages** | 200+ | 5 |
| **Proof technique** | Reducibility + Discharging | Direct + Case analysis |
| **Graph properties** | Planarity, coloring | Triangle-free, regularity |
| **Computation** | Heavy (Gonthier) | Light (one graph) |
| **Formalization** | Years | Weeks |
| **Difficulty** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ |

## Potential Pitfalls and Mitigations

### Pitfall 1: Case Explosion in Final Step
**Risk**: 18 vertices × symmetry breaking × many subcases  
**Mitigation**: 
- Write case-dispatch automation
- Use `fin_cases` heavily
- Break into ~20 small lemmas

### Pitfall 2: R(3,5) Dependency
**Risk**: Might need to formalize R(3,5) first  
**Mitigation**:
- Axiomatize initially
- Formalize R(3,5) in parallel (it's valuable anyway)

### Pitfall 3: Finset Cardinality Arithmetic
**Risk**: Omega can't always solve card equations  
**Mitigation**:
- We just learned this in NoDigons!
- Use explicit intermediate steps
- Build library of card lemmas

### Pitfall 4: Mathlib Gaps
**Risk**: Missing definitions/lemmas  
**Mitigation**:
- Check mathlib thoroughly first
- Contribute missing pieces upstream
- Build local infrastructure as needed

## Success Metrics

### Minimum Viable Product (MVP)
✅ R(3,6) = 18 proven with R(3,5) = 14 axiomatized  
**Time**: 7 weeks  
**Impact**: Novel result, publishable

### Full Version
✅ R(3,6) = 18 with R(3,5) = 14 fully proven  
**Time**: 10-12 weeks  
**Impact**: Complete standalone formalization

### Stretch Goals
✅ R(3,7) = 23 (next Ramsey number)  
✅ General framework for small Ramsey numbers  
**Time**: 15-20 weeks  
**Impact**: Foundation for Ramsey number library

## Publication Strategy

### Target Venue: ITP 2026
- Conference: Interactive Theorem Proving
- Deadline: ~March 2026
- Format: 15-page paper

### Narrative Arc:
1. **Motivation**: Computer-free Ramsey proofs are rare
2. **Challenge**: Formalizing elementary combinatorics
3. **Contribution**: First formal verification of R(3,6)
4. **Insights**: Lessons for finite graph theory
5. **Future**: Path to other Ramsey numbers

### Novelty:
- First Ramsey number formally verified
- Showcases Lean 4 for combinatorics
- Demonstrates decidability advantages

## Next Steps

### Immediate (This Week)
1. ✅ Extract paper
2. ✅ Create project structure
3. ✅ Analyze feasibility
4. [ ] Survey mathlib for existing infrastructure
5. [ ] Start basic definitions

### Short Term (Month 1)
- Set up Ramsey number framework
- Build 17-vertex counterexample
- Prove or axiomatize R(3,5) = 14

### Medium Term (Month 2-3)
- Formalize Claims 1-3
- Develop case analysis infrastructure
- Complete upper bound proof

### Long Term (Beyond)
- Polish and document
- Write paper
- Submit to ITP
- Consider R(3,7) or R(4,4)

## Conclusion

**This is absolutely doable and worth doing!**

The proof is elementary, the scope is manageable, and the impact would be significant. With the experience from Four Color formalization, this is the perfect next project for showcasing Lean's capabilities in combinatorics.

**Recommendation**: START IMMEDIATELY! 🚀

The mathematics is beautiful, the formalization is achievable, and the result would be novel.
