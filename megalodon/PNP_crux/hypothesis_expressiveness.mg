Definition hypothesis_expressiveness_analysis : prop := True.

(* ============================================================
   HYPOTHESIS CLASS EXPRESSIVENESS ANALYSIS
   ============================================================

   CRITICAL QUESTION: Are poly(log m) circuits sufficient?

   In Goertzel's proof, the Switching-by-Weakness theorem claims that
   after wrapper, each bit i has a "local" decoder h_i that depends
   only on O(log m) bits (the log-radius neighborhood in G_phi).

   The proof then claims this allows ERM-style learning with:
   - Sample complexity: O(|H| * log(1/delta))
   - Where |H| is the hypothesis class size

   KEY CLAIM: H consists of poly(log m)-size circuits

   ============================================================
   THE POTENTIAL FLAW
   ============================================================

   SHANNON'S COUNTING ARGUMENT:
   - A Boolean function f: {0,1}^k -> {0,1} can require up to
     2^k / k gates in the worst case
   - For k = c * log m (the neighborhood size), this gives:
     2^{c*log m} / (c*log m) = m^c / (c*log m)
   - This is POLYNOMIAL in m, NOT poly(log m)!

   THE GAP:
   - "Local" functions (depending on O(log m) bits): can require Omega(m) gates
   - Hypothesis class H: claimed to have poly(log m) circuits
   - These are NOT the same!

   ============================================================
   DETAILED ANALYSIS
   ============================================================

   1. What does "local" mean in the proof?
      - A function is "local" if it depends only on bits in a
        log-radius neighborhood in the formula graph G_phi
      - Neighborhood size: O(log m) bits (from sparsification)
      - This is a STRUCTURAL constraint, not a COMPUTATIONAL one

   2. What circuits can compute local functions?
      - Any function on k bits can be computed by a circuit of size 2^k
      - Most functions on k bits require circuits of size 2^k / k
      - For k = log m: size ~ m / log m

   3. The actual proof claim:
      - The DESCRIPTION of h_i is poly(log m) bits
      - This comes from K_poly(h_i | neighborhood) being small
      - But K_poly uses a FIXED polynomial-time universal machine

   4. The resolution attempt:
      - If h_i has small Kolmogorov complexity, it IS simple
      - K_poly(h_i) <= poly(log m) means h_i can be described in
        poly(log m) bits relative to a universal TM
      - This DOES imply small circuit size (with some overhead)

   ============================================================
   CRITICAL DISTINCTION
   ============================================================

   TWO DIFFERENT CLAIMS:

   (A) h_i depends on O(log m) input bits
       -> This is structural, from sparsification
       -> Does NOT bound circuit size

   (B) K_poly(h_i | neighborhood) <= poly(log m)
       -> This is informational, from K-complexity bounds
       -> DOES bound description length
       -> DOES imply bounded circuit size

   THE QUESTION: Does the proof establish (B) or only (A)?

   Looking at Theorem 4.2 (Switching-by-Weakness):
   - Claims K(sigma | phi, h, epsilon) + K(h | phi, neighborhood)
     gives the bound
   - The "locality" is about WHICH bits, not HOW COMPLEX

   ============================================================
   POTENTIAL VULNERABILITY
   ============================================================

   If the proof only establishes that h_i is LOCAL (depends on few bits)
   but not that h_i is SIMPLE (has low K-complexity), then:

   - The sample complexity for learning h_i could be exp(log m) = poly(m)
   - This ruins the information-theoretic argument
   - The lower bound eta*t might not accumulate properly

   SPECIFIC CONCERN:
   - Sparsification gives: h_i depends on O(log m) bits
   - But: h_i might be an arbitrary function on those bits
   - Arbitrary function on k bits: K-complexity up to 2^k
   - For k = log m: K-complexity up to m bits!

   This would mean K_poly(h_i) could be O(m), not O(poly(log m))

   ============================================================
   COUNTEREXAMPLE CONSTRUCTION
   ============================================================

   Suppose the local decoder h_i for bit i is:
   - h_i(x) = PARITY of the log(m) bits in neighborhood(i)

   PARITY on k bits:
   - Has K-complexity O(log k) = O(log log m)  [GOOD: very simple]
   - Has circuit size k  [GOOD: linear in neighborhood]

   But suppose instead h_i is:
   - h_i(x) = majority(complicated_function_1(x), ..., complicated_function_k(x))

   Where each complicated_function encodes problem-specific structure...

   The proof needs to BOUND K_poly(h_i), not just assume it.

   ============================================================
   WHERE THE PROOF MIGHT BE SAVED
   ============================================================

   1. CALIBRATION PROPERTY:
      The proof uses calibration, meaning h_i must satisfy:
      P(bit_i = 1 | h_i(neighborhood) = p) = p

      Calibrated functions have special structure:
      - They are not arbitrary functions
      - They must reflect actual conditional probabilities

      Q: Does calibration bound K-complexity?
      A: Not obviously! There are 2^{2^k} Boolean functions on k bits,
         but only... how many are calibrated?

   2. ERM DISTILLATION:
      The proof uses ERM to find h_i, which means:
      - h_i minimizes empirical error over the hypothesis class H
      - H is defined as poly(log m)-size circuits
      - So by CONSTRUCTION, h_i has small complexity

      BUT: This only works if the TRUE optimal h_i is IN H!
      If true h_i requires larger circuits, ERM gives wrong answer.

   3. INFORMATION-THEORETIC ARGUMENT:
      The proof might argue: K_poly(sigma_i | phi, everything) is small
      because we're only extracting one bit of information.

      This would give: K_poly(h_i | context) = O(1)
      Because h_i outputs just sigma_i, one bit.

      Q: Is this sufficient?
      A: Maybe! If h_i is described as "the function that outputs sigma_i
         given the neighborhood", then K_poly(h_i | sigma_i, phi) = O(1).

   ============================================================
   QUANTITATIVE CHECK
   ============================================================

   Let's count bits:

   Inputs to h_i:
   - log(m) bits from neighborhood

   Output of h_i:
   - 1 bit (the predicted sigma_i)

   Description of h_i:
   - If arbitrary: 2^{log m} = m bits (truth table)
   - If poly(log m) circuit: poly(log m) bits
   - If simple pattern: O(log log m) bits

   For ERM to work:
   - Need |H| <= 2^{poly(log m)}
   - This means each h in H has description <= poly(log m) bits
   - This is ASSUMED, not PROVEN in the paper

   ============================================================
   VERDICT
   ============================================================

   RISK LEVEL: MEDIUM-HIGH

   The proof ASSUMES that local functions have poly(log m) complexity,
   but this is NOT PROVEN. The assumption appears in:
   - Definition of hypothesis class H
   - Sample complexity bounds for ERM
   - Information-theoretic lower bound calculation

   POSSIBLE COUNTEREXAMPLE:
   - Construct a VV-SAT instance where the optimal local decoder
     is a high-complexity function on O(log m) bits
   - This would require: K_poly(h_i) = omega(poly(log m))
   - The adversarial instance construction might achieve this

   POSSIBLE DEFENSE:
   - The paper might implicitly use that under D_m (random phi),
     the local decoder is "typical" and hence simple
   - Random functions have high complexity, but STRUCTURED
     functions (those arising from SAT) might be simple

   NEEDS INVESTIGATION:
   1. Can we prove bounds on K_poly(h_i) from the construction?
   2. Does calibration + locality imply simplicity?
   3. Are there explicit counterexamples in the SAT domain?

   ============================================================*)

Theorem hypothesis_class_assumption : True.
exact I.
Qed.

(* The key formalization needed: *)

Definition local_function : prop :=
  forall m k:set, k :e m ->
  True.  (* Function depends only on k bits *)

Definition simple_function : prop :=
  forall m c:set,
  True.  (* Function has K-complexity <= c *)

(* THE GAP: local does NOT imply simple! *)

Definition gap_theorem : prop :=
  ~(local_function -> simple_function).

(* This would be a counterexample to the proof *)
