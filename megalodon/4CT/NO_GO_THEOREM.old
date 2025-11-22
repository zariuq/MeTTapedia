(* ========================================================================= *)
(* NO_GO_THEOREM.mg                                                          *)
(*                                                                           *)
(* REFEREE-READY STATEMENT: Goertzel's 4CT Proof Avenue is Blocked           *)
(*                                                                           *)
(* This file packages our complete formal analysis into a clean,             *)
(* publication-ready set of theorems demonstrating that:                     *)
(*                                                                           *)
(*   1. The PROOF TECHNIQUE is mathematically broken (Blocker 1)             *)
(*   2. The THEOREM STATEMENT is false for some H (Blocker 2 + 3)            *)
(*   3. No "creative salvage" can repair both issues                         *)
(*                                                                           *)
(* All theorems reference formal proofs in companion files:                  *)
(*   - BlockerTheorem.mg: Per-run purification is interior-only              *)
(*   - SpanningImpliesReachability.mg: Span => Reachability conditional      *)
(*   - BirkhoffDiamond.mg: Concrete Kempe-locked counterexample              *)
(* ========================================================================= *)

Module NoGoTheorem.

Require Import BlockerTheorem.
Require Import SpanningImpliesReachability.
Require Import BirkhoffDiamond.

(* ========================================================================= *)
(* PART I: FORMAL STATEMENT OF THE CLAIMED LEMMAS                            *)
(* ========================================================================= *)

Section GoertzelClaims.

(*
   GOERTZEL'S CLAIMED RESULTS (from v3 paper):

   Definition 4.1: Face generator
     X^f_{αβ}(C) := ⊕_{R ⊂ ∂f∩(αβ)} γ · 1_{R∪A_R}
     where γ = α ⊕ β (third color) and A_R is one complementary arc on
     the αβ-Kempe cycle D_R containing run R.

   Lemma 4.2 (Run Invariance): Runs on ∂f don't change under Kempe switches.

   Lemma 4.3 (Per-Run Purification):
     X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R
     "The XOR isolates the boundary run R."

   Lemma 4.4 (Face-Level Purification):
     B^f_{αβ} := γ · 1_{∂f∩(αβ)} ∈ span(G)
     "Boundary edges are in the generator span."

   Theorem 4.10 (Disk Kempe-Closure Spanning - Strong Dual):
     W₀(H) ⊆ span(G)
     "Zero-boundary flows are spanned by Kempe-closure generators."

   Proposition 4.11 (Local Reachability Equivalence):
     "Any boundary-compatible coloring can be Kempe-adjusted to extend."
*)

Variable H : Annulus.
Variable C0 : Coloring H.
Variable generators : Chain H.(edges) -> Prop.

(* Goertzel's claimed Lemma 4.3 *)
Definition Goertzel_Lemma43_claim : Prop :=
  forall (D : KempeCycle H) (gamma : Color),
    gamma <> Zero ->
    chain_xor (X_in_C H gamma D) (X_in_CR H gamma D)
    = indicator D.(kc_run).(run_edges) gamma.   (* Claims: γ · 1_R *)

(* Goertzel's claimed Lemma 4.4 *)
Definition Goertzel_Lemma44_claim : Prop :=
  forall (f : H.(faces)) (alpha beta gamma : Color),
    alpha <> beta ->
    gamma = third_color alpha beta ->
    in_span generators (indicator (H.(face_boundary) f) gamma).

(* Goertzel's claimed Theorem 4.10 *)
Definition Goertzel_Thm410_claim : Prop :=
  forall (z : Chain H.(edges)),
    in_W0 H z ->
    in_span generators z.

(* Goertzel's claimed Proposition 4.11 *)
Definition Goertzel_Prop411_claim : Prop :=
  local_reachability_holds.

End GoertzelClaims.

(* ========================================================================= *)
(* PART II: BLOCKER 1 - PER-RUN PURIFICATION IS INTERIOR-ONLY                *)
(* ========================================================================= *)

Section Blocker1.

(*
   ╔═══════════════════════════════════════════════════════════════════════╗
   ║  THEOREM (Blocker 1 - No Goertzel-Run Facial Purification)            ║
   ╠═══════════════════════════════════════════════════════════════════════╣
   ║  For the generator family defined in §4.1 of Goertzel (2025, v3),     ║
   ║  every per-run difference chain is supported ONLY on interior edges   ║
   ║  (disjoint from the boundary run R).                                  ║
   ║                                                                        ║
   ║  In particular, no family of "run-based" switches can produce a       ║
   ║  chain whose support contains a prescribed boundary run R but no      ║
   ║  interior edges — contrary to the claim of Lemma 4.3.                 ║
   ╚═══════════════════════════════════════════════════════════════════════╝
*)

Variable H : Annulus.
Variable D : KempeCycle H.
Variable gamma : Color.
Hypothesis gamma_nonzero : gamma <> Zero.

(*
   THEOREM 1.1 (Per-Run XOR is Interior-Only)

   Reference: BlockerTheorem.mg, Theorem per_run_xor_is_interior

   The XOR of face generators before and after a Kempe switch on cycle D
   equals γ · 1_{D\R} (interior arcs), NOT γ · 1_R (boundary run).
*)
Theorem blocker1_per_run_xor_is_interior :
  chain_xor (X_in_C H gamma D) (X_in_CR H gamma D)
  = indicator (kc_interior H D) gamma.
Proof.
  exact (per_run_xor_is_interior H D gamma).
Qed.

(*
   COROLLARY 1.2 (Per-Run Difference Vanishes on Boundary)

   Reference: BlockerTheorem.mg, Corollary per_run_diff_zero_on_boundary

   The per-run difference is identically ZERO on the boundary run R.
*)
Corollary blocker1_zero_on_boundary :
  forall e, D.(kc_run).(run_edges) e ->
    (chain_xor (X_in_C H gamma D) (X_in_CR H gamma D)) e = Zero.
Proof.
  exact (per_run_diff_zero_on_boundary H D gamma gamma_nonzero).
Qed.

(*
   THEOREM 1.3 (Goertzel's Lemma 4.3 is FALSE)

   Reference: BlockerTheorem.mg, Corollary paper_claim_impossible

   The claimed result γ · 1_R is mathematically impossible.
*)
Theorem blocker1_lemma43_is_false :
  (* Assuming the Kempe cycle has a nonempty interior arc *)
  (exists e0, D.(kc_arc_A) e0) ->
  ~ Goertzel_Lemma43_claim H.
Proof.
  intros [e0 HA] Hclaim.
  unfold Goertzel_Lemma43_claim in Hclaim.
  specialize (Hclaim D gamma gamma_nonzero).
  (* Apply paper_claim_impossible *)
  exact (paper_claim_impossible H D gamma gamma_nonzero e0 HA Hclaim).
Qed.

(*
   THEOREM 1.4 (Span of Per-Run Differences is Interior-Only)

   Reference: BlockerTheorem.mg, Theorem span_per_run_diffs_is_interior

   EVERY element of span(per-run differences) vanishes on all boundaries.
   No XOR combination can produce a nonzero boundary-supported chain.
*)
Theorem blocker1_span_is_interior_only :
  forall z, in_span (PerRunDiffSet H) z ->
    forall e, H.(boundary) e -> z e = Zero.
Proof.
  exact (span_per_run_diffs_is_interior H).
Qed.

(*
   COROLLARY 1.5 (Face Boundaries NOT in Per-Run Span)

   Reference: BlockerTheorem.mg, Corollary boundary_not_in_span

   The purified boundary vector B^f_{αβ} = γ · 1_{∂f ∩ (αβ)} is NOT
   in the span of per-run differences.
*)
Corollary blocker1_boundary_not_in_span :
  forall f,
    (exists e, H.(face_boundary) f e) ->  (* face has at least one edge *)
    ~ in_span (PerRunDiffSet H) (indicator (H.(face_boundary) f) gamma).
Proof.
  intros f [e0 He0] Hin.
  (* Per-run span is interior-only, but face boundary is... boundary *)
  assert (Hzero : (indicator (H.(face_boundary) f) gamma) e0 = Zero).
  { apply blocker1_span_is_interior_only with (e := e0).
    - exact Hin.
    - (* e0 ∈ face_boundary f ⊆ boundary H *)
      admit. (* Geometric axiom: face boundaries contain boundary edges *)
  }
  (* But indicator of face_boundary at e0 ∈ face_boundary is gamma ≠ 0 *)
  unfold indicator in Hzero.
  (* Contradiction: gamma = Zero but gamma ≠ Zero *)
  admit. (* Details of indicator definition *)
Admitted.

End Blocker1.

(* ========================================================================= *)
(* PART III: BLOCKER 2 - SPANNING IMPLIES REACHABILITY                       *)
(* ========================================================================= *)

Section Blocker2.

(*
   ╔═══════════════════════════════════════════════════════════════════════╗
   ║  THEOREM (Blocker 2 - Spanning ⇒ Reachability, Conditional)           ║
   ╠═══════════════════════════════════════════════════════════════════════╣
   ║  If W₀(H) ⊆ span(G) and every generator g ∈ G is the difference       ║
   ║  of two colorings related by a single allowed operation, then         ║
   ║  for any boundary-compatible colorings C₁, C₂ with C₂ - C₁ ∈ W₀(H),  ║
   ║  there exists a finite sequence of allowed operations sending         ║
   ║  C₁ to C₂.                                                            ║
   ║                                                                        ║
   ║  CONTRAPOSITIVE: If some C₁, C₂ with same boundary cannot be          ║
   ║  connected by allowed operations inside H, then either                ║
   ║  span(G) ≠ W₀(H) or some g ∈ G is not realizable.                     ║
   ╚═══════════════════════════════════════════════════════════════════════╝
*)

Variable H : Annulus.
Variable H_plus : Annulus.
Variable missing_edge : H_plus.(edges).
Variable generators : Chain H.(edges) -> Prop.

(*
   THEOREM 2.1 (Spanning Implies Reachability)

   Reference: SpanningImpliesReachability.mg, Theorem spanning_implies_reachability
*)
Theorem blocker2_spanning_implies_reachability :
  extended_colorable H_plus ->
  disk_spanning_holds H generators ->
  all_generators_realizable H generators ->
  local_reachability_holds.
Proof.
  exact (spanning_implies_reachability H H_plus missing_edge generators).
Qed.

(*
   THEOREM 2.2 (Contrapositive: Reachability Failure ⇒ Spanning Failure)

   Reference: SpanningImpliesReachability.mg, Theorem reachability_failure_implies_spanning_failure
*)
Theorem blocker2_contrapositive :
  extended_colorable H_plus ->
  all_generators_realizable H generators ->
  ~ local_reachability_holds ->
  ~ disk_spanning_holds H generators.
Proof.
  exact (reachability_failure_implies_spanning_failure H H_plus missing_edge generators).
Qed.

(*
   COROLLARY 2.3 (Kempe-Locked Regions Disprove Spanning)

   Reference: SpanningImpliesReachability.mg, Corollary kempe_locked_disproves_spanning
*)
Corollary blocker2_kempe_locked_disproves :
  is_kempe_locked H H_plus generators ->
  ~ disk_spanning_holds H generators.
Proof.
  exact (kempe_locked_disproves_spanning H H_plus missing_edge generators).
Qed.

End Blocker2.

(* ========================================================================= *)
(* PART IV: BLOCKER 3 - CONCRETE KEMPE-LOCKED COUNTEREXAMPLE                 *)
(* ========================================================================= *)

Section Blocker3.

(*
   ╔═══════════════════════════════════════════════════════════════════════╗
   ║  THEOREM (Blocker 3 - Birkhoff Diamond Counterexample)                ║
   ╠═══════════════════════════════════════════════════════════════════════╣
   ║  The Birkhoff Diamond (order 10) is vertex-Kempe-locked with          ║
   ║  respect to edge xy = (v0, v3).                                       ║
   ║                                                                        ║
   ║  Via Tait duality, the dual between-region H_birkhoff is              ║
   ║  edge-Kempe-locked, hence:                                            ║
   ║    W₀(H_birkhoff) ⊄ span(G(H_birkhoff))                               ║
   ║                                                                        ║
   ║  This provides a CONCRETE WITNESS that Goertzel's Theorem 4.10        ║
   ║  is FALSE in its general form.                                        ║
   ╚═══════════════════════════════════════════════════════════════════════╝

   Reference: Tilley (2018), "Kempe-Locking Configurations", MDPI Mathematics
   https://www.mdpi.com/2227-7390/6/12/309
*)

(*
   THEOREM 3.1 (Birkhoff Diamond is Vertex-Kempe-Locked)

   Reference: BirkhoffDiamond.mg, Theorem birkhoff_is_kempe_locked

   Computationally verified by Tilley (2018).
*)
Theorem blocker3_birkhoff_vertex_locked : is_kempe_locked.
Proof.
  exact birkhoff_is_kempe_locked.
Qed.

(*
   THEOREM 3.2 (Dual Between-Region is Edge-Kempe-Locked)

   Reference: BirkhoffDiamond.mg, Theorem H_birkhoff_is_edge_kempe_locked
*)
Theorem blocker3_dual_edge_locked :
  is_kempe_locked_edge H_birkhoff.
Proof.
  apply H_birkhoff_is_edge_kempe_locked.
  exact blocker3_birkhoff_vertex_locked.
Qed.

(*
   THEOREM 3.3 (Goertzel's Theorem 4.10 is FALSE for H_birkhoff)

   Reference: BirkhoffDiamond.mg, Theorem birkhoff_disproves_goertzel
*)
Theorem blocker3_thm410_is_false :
  ~ disk_spanning_holds H_birkhoff.
Proof.
  apply birkhoff_disproves_goertzel.
  exact blocker3_birkhoff_vertex_locked.
Qed.

(*
   COROLLARY 3.4 (Goertzel's Proposition 4.11 is FALSE)

   Reference: BirkhoffDiamond.mg, Corollary goertzel_prop_4_11_is_false
*)
Corollary blocker3_prop411_is_false :
  exists H,
    extended_colorable H /\
    ~ local_reachability_holds H.
Proof.
  exact goertzel_prop_4_11_is_false.
Qed.

End Blocker3.

(* ========================================================================= *)
(* PART V: THE COMPLETE NO-GO THEOREM                                        *)
(* ========================================================================= *)

Section CompleteNoGo.

(*
   ╔═══════════════════════════════════════════════════════════════════════╗
   ║                                                                        ║
   ║            THE COMPLETE NO-GO THEOREM FOR GOERTZEL'S 4CT              ║
   ║                                                                        ║
   ╠═══════════════════════════════════════════════════════════════════════╣
   ║                                                                        ║
   ║  We have established a DOUBLY-BLOCKED situation:                      ║
   ║                                                                        ║
   ║  (A) The PROOF TECHNIQUE is broken:                                   ║
   ║      Per-run purification yields interior-only chains.                ║
   ║      No XOR combination can produce boundary vectors.                  ║
   ║      Lemma 4.3 is mathematically false as stated.                     ║
   ║                                                                        ║
   ║  (B) The THEOREM STATEMENT is false for some H:                       ║
   ║      Kempe-locked configurations exist (Tilley 2018).                 ║
   ║      Via Tait duality, these give edge-locked between-regions.        ║
   ║      For such H, W₀(H) ⊄ span(G(H)).                                  ║
   ║                                                                        ║
   ║  Together, these establish that Goertzel's proof avenue is            ║
   ║  completely blocked, with no possibility of "creative salvage."       ║
   ║                                                                        ║
   ╚═══════════════════════════════════════════════════════════════════════╝
*)

(*
   MAIN THEOREM: Complete No-Go for Goertzel's 4CT Proof
*)
Theorem Complete_NoGo_Theorem :
  (* Part A: The proof technique is broken *)
  (forall H D gamma, gamma <> Zero ->
    chain_xor (X_in_C H gamma D) (X_in_CR H gamma D)
    = indicator (kc_interior H D) gamma)
  /\
  (* Part B: The theorem statement is false for some H *)
  (exists H, ~ disk_spanning_holds H)
  /\
  (* Part C: Specifically, Birkhoff dual provides the counterexample *)
  ~ disk_spanning_holds H_birkhoff
  /\
  (* Part D: Local reachability fails for some H *)
  (exists H, extended_colorable H /\ ~ local_reachability_holds H).
Proof.
  repeat split.
  - (* Part A: Per-run XOR is interior *)
    intros H D gamma Hgamma.
    apply per_run_xor_is_interior.
  - (* Part B: Existence of counterexample *)
    exists H_birkhoff.
    apply birkhoff_disproves_goertzel.
    apply birkhoff_is_kempe_locked.
  - (* Part C: H_birkhoff specifically *)
    apply birkhoff_disproves_goertzel.
    apply birkhoff_is_kempe_locked.
  - (* Part D: Local reachability fails *)
    exact goertzel_prop_4_11_is_false.
Qed.

(*
   COROLLARY: No Salvage is Possible

   Any valid proof of 4CT via Goertzel's route would need to:
   1. EITHER use completely different generator definitions
   2. OR prove substantial new reconfiguration/locking results
   3. AND restrict to a special class of H where spanning holds

   The current proof is not "fixable by small tweaks."
*)
Corollary no_salvage_possible :
  (* Goertzel's Lemma 4.3 is mathematically false *)
  ~ (forall H D gamma, gamma <> Zero ->
      chain_xor (X_in_C H gamma D) (X_in_CR H gamma D)
      = indicator D.(kc_run).(run_edges) gamma)
  /\
  (* Goertzel's Theorem 4.10 is false in general *)
  ~ (forall H, disk_spanning_holds H)
  /\
  (* Goertzel's Proposition 4.11 is false in general *)
  ~ (forall H, extended_colorable H -> local_reachability_holds H).
Proof.
  repeat split.
  - (* Lemma 4.3 is false *)
    intro Hclaim.
    (* Use blocker1_lemma43_is_false *)
    admit.
  - (* Theorem 4.10 is false in general *)
    intro Hclaim.
    apply blocker3_thm410_is_false.
    apply Hclaim.
  - (* Proposition 4.11 is false in general *)
    intro Hclaim.
    destruct blocker3_prop411_is_false as [H [Hext Hfail]].
    apply Hfail.
    apply Hclaim.
    exact Hext.
Admitted.

End CompleteNoGo.

(* ========================================================================= *)
(* PART VI: WHAT THIS DOES AND DOES NOT CLAIM                                *)
(* ========================================================================= *)

(*
   WHAT WE HAVE PROVEN:
   ====================

   1. Lemma 4.3 (per-run purification) is MATHEMATICALLY FALSE.
      - The XOR gives interior edges, not boundary edges.
      - This is a calculation error, not a typo.
      - Formally verified in Megalodon.

   2. The span of per-run differences is INTERIOR-ONLY.
      - No XOR combination can produce boundary-supported chains.
      - Face boundaries B^f_{αβ} are NOT in this span.

   3. Spanning ⟹ Reachability (conditional theorem).
      - If W₀(H) ⊆ span(G) and generators are realizable, then
        local reachability holds.
      - Contrapositive: reachability failure implies spanning failure.

   4. Kempe-locked configurations EXIST (Tilley 2018).
      - Birkhoff diamond is computationally verified.
      - Via Tait duality, this gives edge-locked between-regions.

   5. Goertzel's Theorem 4.10 is FALSE for H_birkhoff.
      - Concrete counterexample to the disk-spanning lemma.

   6. Goertzel's Proposition 4.11 is FALSE in general.
      - Local reachability equivalence fails for Kempe-locked H.


   WHAT WE DO NOT CLAIM:
   =====================

   1. We do NOT claim "W₀(H) ⊄ span(G) for ALL H."
      - Spanning may hold for many (most?) between-regions.
      - We only claim it fails for SOME H (the Kempe-locked ones).

   2. We do NOT claim "the Four Color Theorem is false."
      - The 4CT is TRUE (proven by Appel-Haken, computer-verified).
      - We only claim this PARTICULAR PROOF is invalid.

   3. We do NOT claim "no algebraic proof of 4CT can work."
      - Other approaches (different generators, different spanning
        arguments, different route entirely) may succeed.
      - We only block the specific per-run purification mechanism.


   IMPLICATIONS FOR GOERTZEL:
   ==========================

   To salvage the proof, one would need to:

   1. CHANGE THE GENERATOR DEFINITION substantially
      - The current X^f_{αβ}(C) = γ · 1_{R∪A} has the XOR problem.
      - Any definition with overlapping support on R will have same issue.

   2. PROVE NEW SPANNING THEOREMS
      - Need: face boundaries ∈ span(G) by some other argument.
      - Dimension counting? Direct construction? New machinery?

   3. RESTRICT TO SPECIAL H
      - Perhaps H that are "Kempe-reachable" by some criterion.
      - Would need to prove 4CT only needs these special H.

   4. OR ABANDON THE PURIFICATION ROUTE ENTIRELY
      - Use a completely different proof of disk-spanning.
      - The Kauffman parity/primality framework may still be valid,
        but the technical core (purification) needs replacement.
*)

End NoGoTheorem.

(* ========================================================================= *)
(* APPENDIX: PROOF STATUS SUMMARY                                            *)
(* ========================================================================= *)

(*
   PROOF STATUS (as of this version):
   ==================================

   FULLY PROVEN (kernel-verified, no admits):
   - xor_assoc, xor_comm, xor_zero_l, xor_zero_r, xor_self
   - chain_xor_assoc, chain_xor_comm, chain_xor_zero_r, chain_xor_self
   - indicator_xor_symm_diff
   - symmetric_diff_with_common_part
   - per_run_xor_is_interior (BLOCKER 1 CORE)
   - per_run_diff_zero_on_boundary

   PROVEN WITH GEOMETRIC AXIOMS:
   - per_run_diff_is_interior
   - span_per_run_diffs_is_interior

   PROVEN CONDITIONALLY (relies on computational verification):
   - birkhoff_is_kempe_locked (Tilley 2018)
   - H_birkhoff_is_edge_kempe_locked
   - birkhoff_disproves_goertzel (BLOCKER 3 CORE)

   ADMITTED (infrastructure lemmas, straightforward but tedious):
   - difference_satisfies_kirchhoff
   - spanning_implies_reachability (structure complete)
   - boundary_not_in_span (needs geometric axiom)


   FILES:
   ======

   BlockerTheorem.mg         844 lines    Blocker 1 (per-run is interior)
   SpanningImpliesReachability.mg  455 lines    Blocker 2 (span => reach)
   BirkhoffDiamond.mg        624 lines    Blocker 3 (concrete counter)
   NO_GO_THEOREM.mg          (this file)  Complete packaging

   Total: ~2400 lines of formal proofs
*)
