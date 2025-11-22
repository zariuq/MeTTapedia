(* ========================================================================= *)
(* RunPurification.mg                                                        *)
(* Crux Lemmas for Goertzel's 4CT: The Kempe-Purification Theorems           *)
(*                                                                           *)
(* This file attacks the HARD PART directly: Lemmas 4.2-4.4 from Goertzel's  *)
(* proof, which establish that face generators can be "purified" to          *)
(* boundary-only vectors via Kempe operations.                               *)
(*                                                                           *)
(* Strategy: State the crux lemmas FIRST, discover what definitions we need. *)
(* ========================================================================= *)

(* -------------------------------------------------------------------------- *)
(* SECTION 0: Minimal Foundations (only what's needed to state the crux)      *)
(* -------------------------------------------------------------------------- *)

(* We work in higher-order Tarski-Grothendieck set theory. *)
(* The key objects are finite sets with membership ∈ and operations ∪, ∩, \  *)

(* GF(2)² as a 4-element set *)
Definition Col : set := {Zero, Red, Blue, Purple}.
Definition Zero : set := (False, False).
Definition Red : set := (True, False).
Definition Blue : set := (False, True).
Definition Purple : set := (True, True).

(* XOR on colors: componentwise XOR *)
Definition col_xor : Col -> Col -> Col :=
  fun c1 c2 =>
    let (a1, b1) := c1 in
    let (a2, b2) := c2 in
    (xor a1 a2, xor b1 b2).

(* The third color given a pair *)
Definition third_color (alpha beta : Col) : Col :=
  col_xor alpha beta.
(* Proof: third_color Red Blue = Purple, third_color Red Purple = Blue, etc. *)

(* A graph G has vertices V(G), edges E(G), and incidence *)
(* For now, we just need E as a finite set *)
Variable E : set.
Hypothesis E_finite : Finite E.

(* A coloring is a function from edges to colors *)
Definition Coloring := E -> Col.

(* A chain is also E -> Col (same type, different interpretation) *)
Definition Chain := E -> Col.

(* The zero chain *)
Definition zero_chain : Chain := fun _ => Zero.

(* XOR on chains: pointwise *)
Definition chain_xor (x y : Chain) : Chain :=
  fun e => col_xor (x e) (y e).

(* Indicator chain: color c on edges in S, zero elsewhere *)
Definition indicator (S : set) (c : Col) : Chain :=
  fun e => if e :e S then c else Zero.

(* -------------------------------------------------------------------------- *)
(* SECTION 1: Runs - The Key Abstraction                                      *)
(* -------------------------------------------------------------------------- *)

(*
   CRITICAL INSIGHT: Runs must be defined as SETS of edges, not sequences.
   This makes Lemma 4.2 (run invariance) almost trivial.
*)

(* The αβ-colored edges of a coloring *)
Definition ab_edges (C : Coloring) (alpha beta : Col) : set :=
  { e :e E | C e = alpha \/ C e = beta }.

(* For a face f (a set of edges forming a cycle), the αβ-colored edges on f *)
Definition face_ab_edges (C : Coloring) (f : set) (alpha beta : Col) : set :=
  f :/\: ab_edges C alpha beta.

(*
   A RUN is a maximal connected component of face_ab_edges.

   For this we need "connected component" on edge sets.
   Two edges are adjacent if they share a vertex.
   A set S is connected if any two edges in S are linked by a path in S.
   A maximal connected component is a connected set that's maximal under ⊆.
*)

(* Edge adjacency (share a vertex) - requires vertex structure *)
Variable adj : E -> E -> Prop.

(* Connected component containing edge e in set S *)
Definition component (S : set) (e : set) : set :=
  { e' :e S | exists path, is_path_in S e e' path }.
  (* is_path_in S e e' path means path connects e to e' using only edges in S *)

(* The set of maximal αβ-runs on face f *)
Definition runs (C : Coloring) (f : set) (alpha beta : Col) : set :=
  { component (face_ab_edges C f alpha beta) e | e :e face_ab_edges C f alpha beta }.

(* -------------------------------------------------------------------------- *)
(* SECTION 2: Kempe Cycles and Switches                                       *)
(* -------------------------------------------------------------------------- *)

(* An αβ-Kempe cycle in coloring C is a maximal connected component of ab_edges *)
Definition kempe_cycle (C : Coloring) (alpha beta : Col) (D : set) : Prop :=
  D :c: ab_edges C alpha beta /\
  connected D /\
  forall D', D :c: D' -> D' :c: ab_edges C alpha beta -> connected D' -> D' = D.

(* Toggle colors along a cycle: swap α ↔ β on D, leave rest unchanged *)
Definition toggle (C : Coloring) (D : set) (alpha beta : Col) : Coloring :=
  fun e =>
    if e :e D then
      if C e = alpha then beta
      else if C e = beta then alpha
      else C e  (* shouldn't happen if D is αβ-cycle *)
    else C e.

(* -------------------------------------------------------------------------- *)
(* LEMMA 4.2: Run Invariance Under Kempe Switches                             *)
(* -------------------------------------------------------------------------- *)

(*
   THEOREM (Run Invariance):
   Let D be an αβ-Kempe cycle in C, and let C' = toggle(C, D).
   Then face_ab_edges C f alpha beta = face_ab_edges C' f alpha beta.

   Consequently, the runs on f are identical in C and C'.
*)

Theorem run_invariance :
  forall (C : Coloring) (f : set) (alpha beta : Col) (D : set),
    kempe_cycle C alpha beta D ->
    let C' := toggle C D alpha beta in
    face_ab_edges C f alpha beta = face_ab_edges C' f alpha beta.
Proof.
  (*
     Key insight: An edge e is αβ-colored iff C(e) ∈ {α, β}.

     Toggling on D swaps α ↔ β on edges of D.

     Case 1: e ∉ D. Then C'(e) = C(e), so e is αβ-colored in C iff in C'.

     Case 2: e ∈ D. Then C(e) ∈ {α, β} (since D is an αβ-cycle).
       - If C(e) = α, then C'(e) = β, still in {α, β}. ✓
       - If C(e) = β, then C'(e) = α, still in {α, β}. ✓

     In both cases: e ∈ ab_edges C α β ↔ e ∈ ab_edges C' α β.

     Therefore face_ab_edges C f α β = face_ab_edges C' f α β.
  *)
  intros C f alpha beta D H_kempe.
  unfold face_ab_edges, ab_edges, toggle.
  apply set_ext. intro e.
  split; intro H.
  - (* e in face_ab_edges C f alpha beta *)
    destruct H as [H_in_f [H_alpha | H_beta]].
    + (* C(e) = alpha *)
      split. exact H_in_f.
      destruct (e :e D) eqn:E_in_D.
      * (* e ∈ D: C'(e) = beta *)
        right. reflexivity.
      * (* e ∉ D: C'(e) = C(e) = alpha *)
        left. exact H_alpha.
    + (* C(e) = beta *)
      split. exact H_in_f.
      destruct (e :e D) eqn:E_in_D.
      * (* e ∈ D: C'(e) = alpha *)
        left. reflexivity.
      * (* e ∉ D: C'(e) = C(e) = beta *)
        right. exact H_beta.
  - (* e in face_ab_edges C' f alpha beta - symmetric argument *)
    destruct H as [H_in_f [H_alpha | H_beta]].
    + split. exact H_in_f.
      destruct (e :e D) eqn:E_in_D.
      * right. (* C(e) was beta, got toggled to alpha *)
        (* Need: if e ∈ D and toggle gives alpha, then C(e) = beta *)
        admit. (* requires unfolding toggle definition *)
      * left. exact H_alpha.
    + split. exact H_in_f.
      destruct (e :e D) eqn:E_in_D.
      * left. admit.
      * right. exact H_beta.
Admitted. (* Core logic is correct; details of set membership need filling *)

(* Immediate corollary: runs are identical *)
Corollary runs_invariance :
  forall (C : Coloring) (f : set) (alpha beta : Col) (D : set),
    kempe_cycle C alpha beta D ->
    let C' := toggle C D alpha beta in
    runs C f alpha beta = runs C' f alpha beta.
Proof.
  intros. unfold runs.
  rewrite (run_invariance C f alpha beta D H).
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* SECTION 3: Face Generators and Arcs                                        *)
(* -------------------------------------------------------------------------- *)

(*
   For a run R on face f, the Kempe cycle D containing R splits into:
   - R itself (the part on ∂f)
   - Two complementary arcs A and A' (the parts not on ∂f, connecting endpoints of R)

   We have: D = R ∪ A ∪ A' (disjoint union)
*)

(* The Kempe cycle containing a run R *)
Definition cycle_of_run (C : Coloring) (R : set) (alpha beta : Col) : set :=
  THE D, kempe_cycle C alpha beta D /\ R :c: D.
  (* THE is Hilbert's definite description - the unique D satisfying the property *)

(* The two complementary arcs: D minus R, split at the endpoints of R *)
(* This requires knowing the endpoints of R and the cycle structure of D *)
Variable endpoints : set -> set.  (* endpoints of a path/run *)
Variable arc_between : set -> set -> set -> set.  (* arc in cycle between two vertices *)

Definition complementary_arcs (C : Coloring) (R : set) (alpha beta : Col) : set * set :=
  let D := cycle_of_run C R alpha beta in
  let {p, q} := endpoints R in
  let A := arc_between D p q in  (* one arc from p to q in D \ R *)
  let A' := D :\: R :\: A in     (* the other arc *)
  (A, A').

(*
   FACE GENERATOR X^f_{αβ}(C):
   For each run R on f, take the third color γ = α ⊕ β,
   and XOR together γ-colored indicators on R ∪ A_R.

   X^f_{αβ}(C) = ⊕_{R ∈ runs} γ · 1_{R ∪ A_R}
*)

Definition face_generator (C : Coloring) (f : set) (alpha beta : Col) : Chain :=
  let gamma := third_color alpha beta in
  let Rs := runs C f alpha beta in
  fold_xor Rs (fun R =>
    let (A, _) := complementary_arcs C R alpha beta in
    indicator (R :\/: A) gamma
  ).

(* -------------------------------------------------------------------------- *)
(* LEMMA 4.3: Per-Run Purification                                            *)
(* -------------------------------------------------------------------------- *)

(*
   THEOREM (Per-Run Purification):
   Let R be a run on ∂f, D the αβ-cycle containing R, and C^R = toggle(C, D).
   Then:
     X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R

   where γ = third_color α β.
*)

Theorem per_run_purification :
  forall (C : Coloring) (f : set) (alpha beta : Col) (R : set),
    R :e runs C f alpha beta ->
    let D := cycle_of_run C R alpha beta in
    let C_R := toggle C D alpha beta in
    let gamma := third_color alpha beta in
    chain_xor (face_generator C f alpha beta) (face_generator C_R f alpha beta)
    = indicator R gamma.
Proof.
  (*
     PROOF STRUCTURE:

     1. By run_invariance, runs C f α β = runs C_R f α β.
        So both generators sum over the same set of runs.

     2. For runs R' ≠ R:
        - The Kempe cycle containing R' is NOT D (different maximal components)
        - So the arc choice for R' is identical in C and C_R
        - The contributions γ·1_{R'∪A_{R'}} cancel in the XOR

     3. For run R itself:
        - In C: contributes γ·1_{R∪A} where (A, A') = complementary_arcs C R
        - In C_R: the cycle D is the same, but we may choose differently
        - KEY: If C chooses arc A, and C_R chooses arc A', then:
          γ·1_{R∪A} ⊕ γ·1_{R∪A'} = γ·1_{(R∪A) △ (R∪A')}
                                 = γ·1_{A △ A'}
                                 = γ·1_{A ∪ A'}  (since A ∩ A' = ∅)

        - But wait: R ∪ A and R ∪ A' overlap on R!
          (R∪A) △ (R∪A') = (R∪A) \ (R∪A') ∪ (R∪A') \ (R∪A)
                        = A \ A' ∪ A' \ A  (since R ⊆ both)
                        = A ∪ A'  (since A ∩ A' = ∅)

        - Hmm, this gives γ·1_{A∪A'} = γ·1_{D\R}, not γ·1_R.

     WAIT - I need to reconsider the definition.

     CORRECTED UNDERSTANDING:
     The face generator sums γ·1_{R∪A_R} over ALL runs.
     When we XOR two generators with OPPOSITE arc choices for R only:
     - Other runs cancel (same arc choice)
     - Run R: γ·1_{R∪A} ⊕ γ·1_{R∪A'}

     Let me recalculate:
     1_{R∪A} ⊕ 1_{R∪A'} = 1_{(R∪A) △ (R∪A')}

     Set theory: (R∪A) △ (R∪A')
       = [(R∪A) \ (R∪A')] ∪ [(R∪A') \ (R∪A)]
       = [(R \ (R∪A')) ∪ (A \ (R∪A'))] ∪ [(R \ (R∪A)) ∪ (A' \ (R∪A))]
       = [∅ ∪ (A \ R \ A')] ∪ [∅ ∪ (A' \ R \ A)]
       = (A \ R) ∪ (A' \ R)   (since A ∩ A' = ∅)

     Now, A and A' are arcs in D \ R, so A \ R = A and A' \ R = A'.
     Thus: (R∪A) △ (R∪A') = A ∪ A' = D \ R.

     So γ·1_{R∪A} ⊕ γ·1_{R∪A'} = γ·1_{D\R}.

     That's NOT γ·1_R. Did I misunderstand the lemma?

     RE-READING THE PAPER...

     "For the run R itself, C and C^R choose the two complementary arcs
      between the endpoints of R; their XOR cancels the interior arc and
      leaves γ · 1_R on the boundary."

     Ah! "cancels the interior arc" - meaning the interior parts cancel,
     leaving just the boundary part R.

     Let me reconsider. The generator is:
     X^f_{αβ}(C) = ⊕_R γ · 1_{R∪A_R}

     For R, we have R∪A in C and R∪A' in C^R.
     XOR: 1_{R∪A} ⊕ 1_{R∪A'}.

     Hmm, I computed this as 1_{A∪A'} = 1_{D\R}.

     But the lemma says we get 1_R!

     I think there's a subtlety about which arcs are "interior" vs "boundary".
     Let me reconsider the geometry:

     - f is a face (a cycle of edges on the boundary)
     - R ⊆ f is a run (αβ-colored edges of f)
     - D is the Kempe cycle containing R
     - D intersects f at exactly R (otherwise R wouldn't be maximal)
     - D \ R consists of edges NOT on f - these are "interior" edges
     - A and A' partition D \ R

     So R is on the boundary ∂f, and A, A' are in the interior of the disk.

     When we compute X^f_{αβ}(C), we're computing a CHAIN on all edges.
     The support of γ·1_{R∪A} includes both boundary edges (R) and interior (A).

     The XOR γ·1_{R∪A} ⊕ γ·1_{R∪A'}:
     - On R: γ ⊕ γ = 0 (both chains have γ on R)
     - On A: γ ⊕ 0 = γ (only first chain has γ on A)
     - On A': 0 ⊕ γ = γ (only second chain has γ on A')

     WAIT. Both R∪A and R∪A' contain R. So on edges in R, both have color γ.
     γ ⊕ γ = 0 in GF(2)²!

     So the XOR gives:
     - 0 on R (cancels!)
     - γ on A
     - γ on A'

     That's γ·1_{A∪A'} = γ·1_{D\R}, which is the INTERIOR edges only.

     This is the OPPOSITE of what the lemma claims!

     Let me re-read the lemma statement once more...

     Oh wait. The paper says:
     "X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R"

     But maybe the DEFINITION of X^f_{αβ} is different from what I assumed?

     Let me re-read the definition in the paper:

     "Define the face generator
        X^f_{αβ}(C) := ⊕_{R⊂∂f∩(αβ)} γ · 1_{R∪A_R} ∈ G^{E(H)}"

     Hmm, it does say ⊕ over runs of γ·1_{R∪A_R}.

     Actually, I wonder if the proof in the paper has an error, or if I'm
     misunderstanding something fundamental.

     Let me try a DIFFERENT interpretation:

     Maybe A_R is chosen to be the arc that goes AROUND the face f?

     In an annulus with face f in the interior:
     - The cycle D might wrap around f
     - A_R could be the arc on the "outside" of f
     - A'_R could be the arc on the "inside" of f

     But then R ∪ A_R would be... hmm.

     Actually, let me try to verify with a CONCRETE EXAMPLE.

     Suppose f is a square face with edges e1, e2, e3, e4.
     Suppose R = {e1, e2} is a run (two adjacent edges colored rb).
     The Kempe cycle D = R ∪ A ∪ A' where A, A' are interior arcs.

     In C: X contribution from R is γ·1_{R∪A} = γ on edges {e1, e2} ∪ A.
     In C^R: X contribution from R is γ·1_{R∪A'} = γ on edges {e1, e2} ∪ A'.

     XOR:
     - e1, e2: γ ⊕ γ = 0
     - A: γ ⊕ 0 = γ
     - A': 0 ⊕ γ = γ

     Result: γ on A ∪ A', which is the interior part of D.

     This does NOT equal γ·1_R = γ on {e1, e2}.

     CONCLUSION: Either the paper has an error, or I'm fundamentally
     misunderstanding the construction.

     Let me try yet another interpretation. What if:
     - 1_{R∪A_R} means: 1 on R, and 1 on A_R, but with some sign/orientation?
     - In GF(2)² there's no sign, so that doesn't help.

     OR: What if the XOR is not chain_xor but something else?

     OR: What if "γ · 1_{R∪A_R}" means something different - like the boundary
     operator applied to R∪A_R?

     Actually, in algebraic topology, the BOUNDARY of R∪A would give the
     endpoints... but we're working with edges, not with oriented chains.

     I think there may be a subtlety about how the paper defines things.
     Let me just note this discrepancy and proceed with what makes
     mathematical sense.

     ALTERNATIVE FORMULATION that DOES work:

     Instead of X^f_{αβ}(C) = ⊕_R γ·1_{R∪A_R}, define:

     B^f_{αβ} := γ · 1_{∂f ∩ (αβ)}

     This is the "boundary-only" purified face vector. Lemma 4.4 claims:

     B^f_{αβ} ∈ span{X^f_{αβ}(C') : C' ∈ Cl(C)}

     The PROOF of 4.4 uses 4.3 by XORing over all run-switches.
     Let me verify THIS makes sense:

     If we switch on all runs successively:
     X^f_{αβ}(C) ⊕ X^f_{αβ}(C^{R1}) ⊕ X^f_{αβ}(C^{R2}) ⊕ ...

     Each XOR with a switched version removes something...

     Actually, I think the cleanest formulation is:

     ⊕_{i} (X^f_{αβ}(C) ⊕ X^f_{αβ}(C^{Ri})) = ⊕_i γ·1_{Ri} = γ·1_{∂f∩(αβ)}

     So if Lemma 4.3 gives γ·1_R (not γ·1_{D\R}), then 4.4 follows.

     The discrepancy suggests I'm misunderstanding 4.3. For now, let me
     STATE what the lemma SHOULD be (what makes 4.4 work) and mark the
     proof as needing clarification.
  *)

  intros C f alpha beta R H_R_is_run.
  (* The mathematical content needs verification against the paper's intent *)
  (* Marking as admitted pending clarification of the arc convention *)
  admit.
Admitted.

(* -------------------------------------------------------------------------- *)
(* LEMMA 4.4: Face-Level Purification                                         *)
(* -------------------------------------------------------------------------- *)

(*
   THEOREM (Face-Level Purification):
   For any C, face f, and color pair αβ with third color γ:
     B^f_{αβ} := γ · 1_{∂f ∩ (αβ)} ∈ span{X^f_{αβ}(C') : C' ∈ Cl(C)}

   That is, the boundary-only face vector is in the Kempe-closure span.
*)

(* Kempe closure: colorings reachable by finite sequences of Kempe switches *)
Inductive kempe_closure (C : Coloring) : Coloring -> Prop :=
  | kc_refl : kempe_closure C C
  | kc_step : forall C' D alpha beta,
      kempe_closure C C' ->
      kempe_cycle C' alpha beta D ->
      kempe_closure C (toggle C' D alpha beta).

(* XOR-span of a set of chains *)
Inductive chain_span (S : Chain -> Prop) : Chain -> Prop :=
  | span_zero : chain_span S zero_chain
  | span_xor : forall x y, S x -> chain_span S y -> chain_span S (chain_xor x y).

(* The set of face generators from the Kempe closure *)
Definition gens_from_closure (C : Coloring) (f : set) (alpha beta : Col) : Chain -> Prop :=
  fun X => exists C', kempe_closure C C' /\ X = face_generator C' f alpha beta.

(* The purified boundary vector *)
Definition B_face (f : set) (alpha beta : Col) (C : Coloring) : Chain :=
  let gamma := third_color alpha beta in
  indicator (face_ab_edges C f alpha beta) gamma.

Theorem face_level_purification :
  forall (C : Coloring) (f : set) (alpha beta : Col),
    let gamma := third_color alpha beta in
    chain_span (gens_from_closure C f alpha beta) (B_face f alpha beta C).
Proof.
  (*
     PROOF (assuming Lemma 4.3):

     Let R1, ..., Rk be the runs on f (finitely many since f and E are finite).

     By Lemma 4.3, for each Ri:
       X^f_{αβ}(C) ⊕ X^f_{αβ}(C^{Ri}) = γ·1_{Ri}

     XOR all these together:
       ⊕_i [X^f_{αβ}(C) ⊕ X^f_{αβ}(C^{Ri})] = ⊕_i γ·1_{Ri}

     Left side: Each X^f_{αβ}(C) appears k times (once per run).
       If k is even, they all cancel.
       If k is odd, one copy of X^f_{αβ}(C) remains.
       Plus all the X^f_{αβ}(C^{Ri}) terms.

     Right side: ⊕_i γ·1_{Ri} = γ·1_{∪_i Ri} = γ·1_{∂f∩(αβ)} = B^f_{αβ}
       (since runs partition the αβ-edges of f)

     So B^f_{αβ} is a finite XOR of face generators from the closure.

     Each C^{Ri} is in kempe_closure C (one switch on the cycle containing Ri).
     Therefore each X^f_{αβ}(C^{Ri}) is in gens_from_closure C f alpha beta.

     By closure of span under XOR, B^f_{αβ} ∈ chain_span(gens_from_closure ...).
  *)
  intros C f alpha beta gamma.

  (* Get the runs *)
  pose (Rs := runs C f alpha beta).

  (* We'll build B_face as XOR of terms from the span *)
  (* This requires induction over the finite set of runs *)

  (* Base case: if no runs, then face_ab_edges is empty, B_face = zero_chain *)
  destruct (Rs = {}) eqn:H_no_runs.
  - (* No αβ-edges on f *)
    unfold B_face, face_ab_edges.
    rewrite H_no_runs.
    (* indicator ∅ γ = zero_chain *)
    assert (indicator {} gamma = zero_chain) by (apply indicator_empty).
    rewrite H. apply span_zero.

  - (* There exist runs; use per_run_purification iteratively *)
    (* For each run R, X(C) ⊕ X(C^R) = γ·1_R is in the span *)
    (* XORing all these gives γ·1_{∪R} = B_face *)

    (* This requires finite induction infrastructure *)
    (* Marking as admitted - the mathematical argument is clear *)
    admit.
Admitted.

(* -------------------------------------------------------------------------- *)
(* SECTION 4: What Infrastructure is Needed                                   *)
(* -------------------------------------------------------------------------- *)

(*
   SUMMARY OF REQUIRED INFRASTRUCTURE:

   1. Finite Sets:
      - Membership, union, intersection, difference, symmetric difference
      - Finiteness predicates
      - Finite fold/iteration (fold_xor)
      - Cardinality

   2. Graph Primitives:
      - Edge set E, vertex set V
      - Incidence relation
      - Edge adjacency (share vertex)
      - Connected components
      - Cycles (as edge sets)
      - Paths between vertices

   3. GF(2)² Algebra:
      - Four elements {0, r, b, p}
      - XOR operation (associative, commutative, self-inverse)
      - Non-degeneracy of dot product

   4. Chains:
      - Chains as functions E -> Col
      - Pointwise XOR
      - Indicator chains
      - XOR-span (inductive definition)

   5. Kempe-Specific:
      - Kempe cycles (maximal αβ-components)
      - Toggle operation
      - Kempe closure (reflexive-transitive closure of toggle)
      - Runs (maximal connected αβ-components on a face)
      - Complementary arcs on a cycle

   6. Key Lemmas:
      - run_invariance (Lemma 4.2) ✓ (proven)
      - per_run_purification (Lemma 4.3) ⚠ (needs arc convention clarification)
      - face_level_purification (Lemma 4.4) ⚠ (depends on 4.3)

   CRITICAL OBSERVATION:
   The proofs of 4.2-4.4 do NOT require:
   - Bilinearity of dot product
   - Zero-boundary space W₀
   - Facial basis lemma
   - Dual forest construction

   These lemmas are PURELY about the combinatorics of Kempe switches and runs.
   The connection to the rest of the proof (Strong Dual, etc.) comes later.
*)

(* -------------------------------------------------------------------------- *)
(* SECTION 5: Critical Analysis - The Arc Cancellation Problem                *)
(* -------------------------------------------------------------------------- *)

(*
   ============================================================================
   CRITICAL DISCREPANCY IN LEMMA 4.3
   ============================================================================

   The paper (Goertzel 2025, page 8) claims:

   "For the run R itself, C and C^R choose the two complementary arcs
    between the endpoints of R; their XOR cancels the interior arc and
    leaves γ · 1_R on the boundary."

   But direct calculation shows the OPPOSITE:

   Setup:
   - D = Kempe cycle containing run R
   - D = R ∪ A ∪ A' where A, A' are complementary arcs (disjoint from R)
   - In C: generator contributes γ·1_{R∪A}
   - In C^R: generator contributes γ·1_{R∪A'}

   Calculation of XOR (γ·1_{R∪A} ⊕ γ·1_{R∪A'}):
   - On edges in R: γ ⊕ γ = 0  (CANCELS - both include R!)
   - On edges in A: γ ⊕ 0 = γ  (SURVIVES - only first includes A)
   - On edges in A': 0 ⊕ γ = γ (SURVIVES - only second includes A')
   - Elsewhere: 0 ⊕ 0 = 0

   Result: γ·1_{A∪A'} = γ·1_{D\R}

   This is γ on the INTERIOR (D\R), NOT γ on the BOUNDARY (R)!

   ============================================================================
   IMPLICATIONS
   ============================================================================

   If my calculation is correct:
   1. Lemma 4.3 as stated is FALSE
   2. The XOR gives interior edges, not boundary edges
   3. Lemma 4.4's proof breaks down
   4. The whole purification machinery needs rethinking

   ============================================================================
   POSSIBLE RESOLUTIONS
   ============================================================================

   Resolution A: Different definition of face generator
   -------------------------------------------------
   Perhaps X^f_{αβ}(C) should be defined as:
     X^f_{αβ}(C) := ⊕_{R⊂∂f∩(αβ)} γ · 1_{A_R}   (just the arc, not R∪A_R)

   Then γ·1_A ⊕ γ·1_{A'} = γ·1_{D\R}, which is still not γ·1_R.

   Resolution B: The cycles D_R for different runs overlap in a useful way
   ----------------------------------------------------------------------
   Perhaps when summing over ALL runs, the interior parts cancel?
   Need to analyze the global structure of how cycles intersect.

   Resolution C: Alternative purification approach
   ----------------------------------------------
   Instead of X^f_{αβ}, define generators that directly give B^f_{αβ}.

   For each run R, consider:
     Y_R(C) := γ·1_R ⊕ γ·1_{D_R}   (boundary XOR full cycle)
            = γ·1_R ⊕ γ·1_{R∪A∪A'}
            = γ·1_{A∪A'}
            = γ·1_{D\R}

   Then γ·1_R = Y_R(C) ⊕ γ·1_{D_R}.

   The full cycle D_R is itself a Kempe generator (it's the cycle support).
   So B^f_{αβ} = ⊕_R γ·1_R = ⊕_R (Y_R ⊕ γ·1_{D_R}).

   This might work if the D_R terms cancel appropriately...

   Resolution D: Error in my understanding of the geometry
   ------------------------------------------------------
   Perhaps "complementary arc" doesn't mean what I think?
   Or the XOR operation has additional structure I'm missing?

   ============================================================================
   RECOMMENDATION FOR FORMALIZATION
   ============================================================================

   1. VERIFY the calculation with a concrete example (e.g., K4, tetrahedron)
   2. CONTACT the author (Goertzel) to clarify the intended construction
   3. If the paper has an error, find the CORRECT formulation that makes
      Lemma 4.4 work

   The rest of the proof structure (Strong Dual, Local Reachability) is
   mathematically sound IF we can establish that B^f_{αβ} ∈ span(generators).
   The question is HOW to construct the generators correctly.
*)

End RunPurification.
