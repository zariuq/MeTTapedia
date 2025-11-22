#!/usr/bin/env python3
"""
Counterexample Construction for Hypothesis Class Expressiveness

GOAL: Construct a SAT instance (or family of instances) where the
optimal local decoder has high circuit complexity, demonstrating
that "local" does NOT imply "simple".

This would show a gap in Goertzel's P!=NP proof.
"""

import math
from itertools import product

def construct_parity_based_sat():
    """
    Construct a SAT instance where recovering bit i requires
    computing PARITY over the neighborhood.

    PARITY on k bits has:
    - Circuit complexity: O(k) with XOR gates
    - Formula complexity: 2^{k-1} (DNF size)
    - K-complexity: O(log k)

    This is actually a GOOD case for the proof - PARITY is simple!
    """
    print("=" * 60)
    print("EXAMPLE 1: PARITY-BASED SAT")
    print("=" * 60)

    print("""
Consider a 3-CNF formula phi where:
- Variables: x_1, ..., x_m, a_1, ..., a_m
- Clauses encode: a_i = XOR of x_j for j in neighborhood(i)

For this instance:
- The unique satisfying assignment has a_i = PARITY(neighborhood(i))
- Recovering a_i from neighborhood requires computing PARITY
- PARITY has circuit complexity O(k) with XOR gates
- PARITY has K-complexity O(log k) = O(log log m)

VERDICT: PARITY is SIMPLE! This does NOT break the proof.
""")


def construct_majority_based_sat():
    """
    Construct a SAT instance where recovering bit i requires
    computing MAJORITY over the neighborhood.

    MAJORITY on k bits has:
    - Circuit complexity: O(k) with threshold gates, or O(k log k) with AND/OR
    - Formula complexity: Θ(k^{k/2} / sqrt(k)) for DNF
    - K-complexity: O(log k)

    Still a relatively simple function!
    """
    print("=" * 60)
    print("EXAMPLE 2: MAJORITY-BASED SAT")
    print("=" * 60)

    print("""
Consider a 3-CNF formula phi where:
- Variables: x_1, ..., x_m, a_1, ..., a_m
- Clauses encode: a_i = MAJORITY of x_j for j in neighborhood(i)

For this instance:
- Recovering a_i requires computing MAJORITY
- MAJORITY has circuit complexity O(k) with threshold gates
- MAJORITY has K-complexity O(log k)

VERDICT: MAJORITY is SIMPLE! This does NOT break the proof.
""")


def construct_lookup_table_sat():
    """
    Construct a SAT instance where recovering bit i requires
    looking up a value in an arbitrary lookup table.

    A random function on k bits has:
    - Circuit complexity: Θ(2^k / k) by Shannon
    - K-complexity: Θ(2^k)

    This WOULD break the proof!
    """
    print("=" * 60)
    print("EXAMPLE 3: LOOKUP TABLE SAT (Potential Counterexample)")
    print("=" * 60)

    print("""
CONSTRUCTION:

Let T be a random truth table on k = log(m) bits.
Define T: {0,1}^k -> {0,1} randomly.

Create a formula phi(x, a) where:
- x = (x_1, ..., x_m) are the main variables
- a = (a_1, ..., a_m) are auxiliary bits
- For each i, define neighborhood N_i as bits {i, i+1, ..., i+k-1}

Clauses enforce: a_i = T(x_{N_i})

For example, if k = 3 and T(000) = 1, T(001) = 0, T(010) = 1, ...
then we add clauses:
  (x_i ∨ x_{i+1} ∨ x_{i+2} ∨ a_i)       -- if T(000) = 1
  (x_i ∨ x_{i+1} ∨ ¬x_{i+2} ∨ ¬a_i)     -- if T(001) = 0
  ... etc.

PROPERTIES:
- Each a_i is a function of k = O(log m) bits
- But that function is RANDOM, hence complex
- Circuit complexity of T: Θ(2^k / k) = Θ(m / log m)
- K-complexity of T: Θ(2^k) = Θ(m)

For recovery:
- Given the neighborhood x_{N_i}, must compute T(x_{N_i})
- This requires ~ m / log m gates
- But hypothesis class only allows (log m)^c gates

GAP: m / log m >> (log m)^c for large m

VERDICT: This COULD break the proof!
""")

    # Numerical analysis
    print("NUMERICAL ANALYSIS:")
    for m in [1000, 10000, 100000, 1000000]:
        k = int(math.log2(m))
        circuit_needed = m / math.log2(m)  # 2^k / k = m / log m
        for c in [2, 3, 4, 5]:
            circuit_allowed = k ** c
            gap = circuit_needed / circuit_allowed
            status = "GAP!" if circuit_needed > circuit_allowed else "OK"
            print(f"  m={m:7}, k={k:2}, needed={circuit_needed:8.0f}, "
                  f"allowed(c={c})={circuit_allowed:8}, ratio={gap:6.1f}x  {status}")
        print()


def analyze_sat_encoding_complexity():
    """
    Analyze: Can we actually ENCODE an arbitrary function in 3-CNF?
    """
    print("=" * 60)
    print("SAT ENCODING ANALYSIS")
    print("=" * 60)

    print("""
KEY QUESTION: Can we encode a = T(x_{N_i}) in 3-CNF efficiently?

ANSWER: Yes! The Tseitin transformation:
- Any Boolean circuit of size s can be encoded in 3-CNF with O(s) clauses
- For a lookup table T on k bits: O(2^k) clauses per bit
- For m bits: O(m * 2^k) = O(m * m) = O(m^2) total clauses

But wait - this is relevant for the CLAUSE DENSITY:
- The paper uses clause density α = O(1)
- With m variables, this means O(m) clauses total
- But encoding m lookup tables requires O(m^2) clauses!

NEW CONSTRAINT: Clause density limits function complexity!

If φ has αm clauses and m variables:
- Each clause involves 3 variables
- Total "constraint bits": O(αm) = O(m)
- Cannot encode m arbitrary functions on log(m) bits each
- Each function needs ~2^{log m} = m bits to specify
- Total needed: m * m = m^2 >> m

IMPLICATION:
At clause density α = O(1), the local decoder CANNOT be arbitrary!
The constraints force local functions to be SIMPLE.
""")


def analyze_random_sat_structure():
    """
    Analyze the structure of local decoders in random 3-SAT.
    """
    print("=" * 60)
    print("RANDOM 3-SAT STRUCTURE ANALYSIS")
    print("=" * 60)

    print("""
The proof uses D_m = random 3-SAT at density α near threshold.

KEY OBSERVATION:
In random 3-SAT, there is NO explicit target function T!
The satisfying assignments are determined by clause interactions.

STRUCTURE OF RANDOM SAT:
1. Each clause is uniformly random
2. Clauses overlap only in O(1/m) fraction of variable pairs
3. Local structure is "generic" - no planted secrets

FOR VV-SAT (Valiant-Vazirani isolated):
- There is (w.h.p.) exactly ONE satisfying assignment σ
- σ is the XOR of all VV-constraints with the original solution
- But VV-constraints are RANDOM linear equations!

LOCAL DECODER FOR RANDOM VV-SAT:
- Given: neighborhood x_{N_i}
- Task: predict σ_i
- Key: σ_i depends on clause satisfaction in neighborhood

CLAIM: For random 3-SAT, the local decoder is SIMPLE.

ARGUMENT:
1. Clause satisfaction is a 3-CNF function
2. Local neighborhood has O(log m) variables
3. Number of clauses touching neighborhood: O(log m) on average
4. Each clause is a disjunction of 3 literals
5. Local function is CNF on O(log m) clauses
6. CNF complexity: O(number of clauses) = O(log m)

THEREFORE: Local decoder has circuit size O(log m), not O(m)!

But wait - this argument is AVERAGE-case...
What about WORST-case instances?
""")


def construct_planted_counterexample():
    """
    Construct a PLANTED SAT instance with complex local decoder.
    """
    print("=" * 60)
    print("PLANTED SAT COUNTEREXAMPLE")
    print("=" * 60)

    print("""
CONSTRUCTION: Planted SAT with Hidden Function

1. Choose a random function T: {0,1}^k -> {0,1} where k = log(m)

2. Choose a random "seed" s ∈ {0,1}^m

3. For each i, define σ_i = T(s_{N_i}) where N_i = {i, i+1, ..., i+k-1}

4. Generate random 3-SAT clauses that are:
   - All satisfied by σ
   - Otherwise uniformly random

5. Add VV constraints to isolate σ

RESULT:
- The unique satisfying assignment is σ
- Recovering σ_i requires computing T on the local neighborhood
- T is random, so circuit complexity is Θ(2^k / k) = Θ(m / log m)
- This exceeds poly(log m)!

PROBLEM WITH THIS CONSTRUCTION:
The generated clauses REVEAL information about T!
If a clause (x_i ∨ x_j ∨ x_k) exists, it constrains T.
The clauses form an implicit circuit for T.

REFINED ANALYSIS:
- Number of clauses: αm
- Each clause constrains T(·) for certain inputs
- Total constraint bits: O(αm)
- Not enough to specify arbitrary T (needs m bits)

THEREFORE: Even planted SAT cannot encode arbitrary functions!
The clause density LIMITS the complexity of local decoders.

CONCLUSION:
The hypothesis class expressiveness concern may be MITIGATED by
the clause density constraint. Local decoders in SAT instances
at constant clause density cannot be arbitrary functions.
""")


def final_analysis():
    """
    Synthesize findings about hypothesis class expressiveness.
    """
    print("=" * 60)
    print("FINAL ANALYSIS: HYPOTHESIS CLASS EXPRESSIVENESS")
    print("=" * 60)

    print("""
SUMMARY OF FINDINGS:

1. THEORETICAL GAP EXISTS:
   - Functions on k = O(log m) bits can require Θ(2^k/k) = Θ(m/log m) gates
   - Hypothesis class H has only poly(log m)-size circuits
   - In the WORST CASE, there's a gap

2. SAT INSTANCES ARE CONSTRAINED:
   - 3-CNF formulas at clause density α = O(1) have O(m) clauses
   - Cannot encode m arbitrary functions (would need m^2 clauses)
   - Local decoders are IMPLICITLY specified by clauses
   - Clause constraints limit decoder complexity

3. RANDOM SAT HAS SIMPLE DECODERS:
   - Random 3-SAT has "generic" local structure
   - Local decoders are low-complexity on average
   - The proof uses random SAT distribution D_m

4. PLANTED COUNTEREXAMPLES FAIL:
   - Cannot plant arbitrary function without revealing it
   - Clause structure must be consistent with function
   - Polynomial clauses cannot specify exponential function

REVISED RISK ASSESSMENT:

Original concern: LOCAL != SIMPLE, so proof fails
After analysis: SAT structure constrains local functions to be simple

The hypothesis class expressiveness concern is PARTIALLY MITIGATED
by the SAT encoding constraint. However, there remain open questions:

OPEN QUESTIONS:
a) Is there a formal proof that SAT local decoders are simple?
b) Does the calibration requirement add additional simplicity?
c) Are there pathological SAT instances with complex decoders?
d) Does the VV isolation step preserve simplicity?

RISK LEVEL: MEDIUM (revised from MEDIUM-HIGH)

The gap between local and simple functions is REAL in general,
but SAT instances may not be able to realize this gap due to
encoding constraints. More investigation is needed.
""")


def main():
    print("=" * 70)
    print(" COUNTEREXAMPLE CONSTRUCTION FOR HYPOTHESIS CLASS EXPRESSIVENESS")
    print("=" * 70)
    print()

    construct_parity_based_sat()
    print()
    construct_majority_based_sat()
    print()
    construct_lookup_table_sat()
    print()
    analyze_sat_encoding_complexity()
    print()
    analyze_random_sat_structure()
    print()
    construct_planted_counterexample()
    print()
    final_analysis()


if __name__ == "__main__":
    main()
