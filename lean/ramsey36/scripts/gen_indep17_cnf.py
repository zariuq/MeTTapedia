#!/usr/bin/env python3
"""Generate CNF encoding 'no 6-independent set in the Graver-Yackel graph'
using only 17 variables (no auxiliary cardinality variables).

Variables: x_1..x_17 where x_i means vertex (i-1) is in the independent set.

Clauses:
  Type 1 (edge): for each edge (u,v), clause {-(u+1), -(v+1)}
  Type 2 (cardinality): for each 12-subset T of {1..17}, clause T
    (forces at most 5 false, i.e., at least 6 true)
"""
from itertools import combinations

# Graver-Yackel graph edges
neighbors = {
    0: {9, 14, 15, 16}, 1: {7, 11, 13, 16}, 2: {8, 10, 12, 15},
    3: {6, 8, 13, 15, 16}, 4: {5, 7, 12, 14, 16}, 5: {4, 9, 10, 11, 13},
    6: {3, 10, 11, 12, 14}, 7: {1, 4, 9, 10, 15}, 8: {2, 3, 9, 11, 14},
    9: {0, 5, 7, 8, 12}, 10: {2, 5, 6, 7, 16}, 11: {1, 5, 6, 8, 15},
    12: {2, 4, 6, 9, 13}, 13: {1, 3, 5, 12, 14}, 14: {0, 4, 6, 8, 13},
    15: {0, 2, 3, 7, 11}, 16: {0, 1, 3, 4, 10},
}

edges = set()
for u, nbrs in neighbors.items():
    for v in nbrs:
        if u < v:
            edges.add((u, v))

print(f"Graph has {len(edges)} edges", flush=True)

# Edge clauses
edge_clauses = []
for u, v in sorted(edges):
    edge_clauses.append([-(u+1), -(v+1)])

# Cardinality clauses: for each 5-subset of {0..16}, the complementary
# 12-subset must have at least one true variable.
# Equivalently: for each 5-subset S, clause {i+1 : i not in S}
card_clauses = []
for five_sub in combinations(range(17), 5):
    five_set = set(five_sub)
    clause = [i+1 for i in range(17) if i not in five_set]
    card_clauses.append(clause)

total_clauses = len(edge_clauses) + len(card_clauses)
print(f"Edge clauses: {len(edge_clauses)}")
print(f"Cardinality clauses: {len(card_clauses)}")
print(f"Total clauses: {total_clauses}")

# Write CNF
cnf_path = "/home/zar/claude/lean-projects/ramsey36/Ramsey36/indep17_simple.cnf"
with open(cnf_path, "w") as f:
    f.write(f"p cnf 17 {total_clauses}\n")
    for clause in edge_clauses:
        f.write(" ".join(str(l) for l in clause) + " 0\n")
    for clause in card_clauses:
        f.write(" ".join(str(l) for l in clause) + " 0\n")

print(f"Written {cnf_path}")
