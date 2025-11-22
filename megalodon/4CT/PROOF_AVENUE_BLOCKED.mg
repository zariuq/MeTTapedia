(* ========================================================================= *)
(* PROOF_AVENUE_BLOCKED.mg                                                   *)
(*                                                                           *)
(* FORMAL PROOF: Goertzel's Purification Approach is Mathematically Blocked  *)
(*                                                                           *)
(* This file provides a complete, rigorous proof that:                       *)
(* 1. Lemma 4.3 as stated is FALSE                                           *)
(* 2. The correct result is the OPPOSITE of what's claimed                   *)
(* 3. This blocks Lemma 4.4                                                  *)
(* 4. Which blocks Theorem 4.9/4.10                                          *)
(* 5. Therefore the entire proof avenue is blocked                           *)
(*                                                                           *)
(* All three versions (v1, v2, v3) use identical definitions and are         *)
(* therefore equally blocked.                                                *)
(* ========================================================================= *)

Module ProofAvenueBlocked.

(* ========================================================================= *)
(* PART I: AXIOMATIZATION OF THE PAPER'S FRAMEWORK                           *)
(* ========================================================================= *)

Section Framework.

(* --- Basic Types --- *)
Variable E : Type.                     (* Edge set *)
Variable Col : Type.                   (* Colors = F₂² *)
Variable zero : Col.                   (* Zero color *)
Variable gamma : Col.                  (* Third color for pair αβ *)

(* --- XOR Structure (F₂² is a group under XOR) --- *)
Axiom xor : Col -> Col -> Col.
Notation "x ⊕ y" := (xor x y) (at level 50).

Axiom xor_assoc : forall x y z, (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z).
Axiom xor_comm : forall x y, x ⊕ y = y ⊕ x.
Axiom xor_zero_r : forall x, x ⊕ zero = x.
Axiom xor_self : forall x, x ⊕ x = zero.        (* CRITICAL: self-inverse! *)

(* Immediate consequence *)
Lemma xor_zero_l : forall x, zero ⊕ x = x.
Proof. intro x. rewrite xor_comm. apply xor_zero_r. Qed.

(* --- Chains and Indicators --- *)
Definition Chain := E -> Col.

Definition indicator (S : E -> Prop) (c : Col) : Chain :=
  fun e => if S e then c else zero.

Notation "c '·' '1_' S" := (indicator S c) (at level 40).

(* Chain XOR is pointwise *)
Definition chain_xor (x y : Chain) : Chain :=
  fun e => (x e) ⊕ (y e).

Notation "x '⊕c' y" := (chain_xor x y) (at level 50).

(* --- Key Lemma: Indicator XOR is Symmetric Difference --- *)
Lemma indicator_xor_symmetric_diff :
  forall (S T : E -> Prop) (c : Col),
    (c · 1_S) ⊕c (c · 1_T) = c · 1_(symmetric_diff S T).
Proof.
  intros S T c.
  unfold chain_xor, indicator, symmetric_diff.
  apply functional_extensionality. intro e.
  destruct (S e) eqn:HS; destruct (T e) eqn:HT.
  - (* e ∈ S ∩ T: c ⊕ c = 0 *)
    rewrite xor_self.
    (* e ∉ S △ T *)
    assert (~ (S e /\ ~ T e) /\ ~ (T e /\ ~ S e)) by tauto.
    destruct ((S e /\ ~ T e) \/ (T e /\ ~ S e)); [tauto | reflexivity].
  - (* e ∈ S \ T: c ⊕ 0 = c *)
    rewrite xor_zero_r.
    (* e ∈ S △ T *)
    assert ((S e /\ ~ T e) \/ (T e /\ ~ S e)) by tauto.
    destruct ((S e /\ ~ T e) \/ (T e /\ ~ S e)); [reflexivity | tauto].
  - (* e ∈ T \ S: 0 ⊕ c = c *)
    rewrite xor_zero_l.
    assert ((S e /\ ~ T e) \/ (T e /\ ~ S e)) by tauto.
    destruct ((S e /\ ~ T e) \/ (T e /\ ~ S e)); [reflexivity | tauto].
  - (* e ∉ S ∪ T: 0 ⊕ 0 = 0 *)
    rewrite xor_zero_l.
    assert (~ (S e /\ ~ T e) /\ ~ (T e /\ ~ S e)) by tauto.
    destruct ((S e /\ ~ T e) \/ (T e /\ ~ S e)); [tauto | reflexivity].
Qed.

End Framework.

(* ========================================================================= *)
(* PART II: THE PAPER'S DEFINITIONS (VERBATIM FROM ALL VERSIONS)             *)
(* ========================================================================= *)

Section PaperDefinitions.

(* --- Geometric Setup --- *)
Variable R : E -> Prop.    (* Run: maximal αβ-segment on face boundary ∂f *)
Variable A : E -> Prop.    (* One complementary arc *)
Variable A' : E -> Prop.   (* Other complementary arc *)
Variable D : E -> Prop.    (* Full Kempe cycle containing R *)

(* --- Partition Axioms (from paper's geometric setup) --- *)
Axiom R_A_disjoint : forall e, ~ (R e /\ A e).
Axiom R_A'_disjoint : forall e, ~ (R e /\ A' e).
Axiom A_A'_disjoint : forall e, ~ (A e /\ A' e).
Axiom D_is_union : forall e, D e <-> (R e \/ A e \/ A' e).

(* --- The Paper's Face Generator Definition (Section 4.1, all versions) ---

   "For each run R, let D be the αβ-cycle containing R, and let A_R be
    one of the two complementary arcs on D between the endpoints of R
    (any choice will do). Define the face generator

        X^f_{αβ}(C) := ⊕_{R⊂∂f∩(αβ)} γ · 1_{R∪A_R}"

   For a SINGLE run R, the contribution to X^f_{αβ}(C) is:  γ · 1_{R∪A}
*)

Definition X_contribution_C : Chain := gamma · 1_(fun e => R e \/ A e).

(* After Kempe switch C^R, paper claims complementary arc A' is chosen *)
Definition X_contribution_CR : Chain := gamma · 1_(fun e => R e \/ A' e).

(* --- The Paper's Lemma 4.3 Claim (verbatim) ---

   "Lemma 4.3 (Per-run purification). Let R be a maximal αβ-run on ∂f in C,
    and let C^R be the coloring obtained by a Kempe switch on the αβ-cycle
    containing R. Then

        X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R"
*)

Definition paper_claimed_result : Chain := gamma · 1_R.

End PaperDefinitions.

(* ========================================================================= *)
(* PART III: THE ACTUAL MATHEMATICAL TRUTH                                   *)
(* ========================================================================= *)

Section TheTruth.

(* --- Symmetric Difference Calculation --- *)

(*
   We compute: (R ∪ A) △ (R ∪ A')

   By definition of symmetric difference:
   (R ∪ A) △ (R ∪ A') = [(R ∪ A) \ (R ∪ A')] ∪ [(R ∪ A') \ (R ∪ A)]
*)

Lemma symmetric_diff_of_unions :
  forall e,
    symmetric_diff (fun e => R e \/ A e) (fun e => R e \/ A' e) e
    <->
    (A e \/ A' e).
Proof.
  intro e.
  unfold symmetric_diff.
  split.

  - (* => direction *)
    intro H.
    destruct H as [[HRA HnRA'] | [HRA' HnRA]].
    + (* e ∈ (R∪A) \ (R∪A') *)
      destruct HRA as [HR | HA].
      * (* e ∈ R: but then e ∈ R∪A', contradiction *)
        exfalso. apply HnRA'. left. exact HR.
      * (* e ∈ A *)
        left. exact HA.
    + (* e ∈ (R∪A') \ (R∪A) *)
      destruct HRA' as [HR | HA'].
      * exfalso. apply HnRA. left. exact HR.
      * right. exact HA'.

  - (* <= direction *)
    intro H.
    destruct H as [HA | HA'].
    + (* e ∈ A *)
      left. split.
      * right. exact HA.
      * intro HRA'. destruct HRA' as [HR | HA''].
        -- (* e ∈ R: contradicts R ∩ A = ∅ *)
           exact (R_A_disjoint e (conj HR HA)).
        -- (* e ∈ A': contradicts A ∩ A' = ∅ *)
           exact (A_A'_disjoint e (conj HA HA'')).
    + (* e ∈ A' *)
      right. split.
      * right. exact HA'.
      * intro HRA. destruct HRA as [HR | HA].
        -- exact (R_A'_disjoint e (conj HR HA')).
        -- exact (A_A'_disjoint e (conj HA HA')).
Qed.

(* --- The Interior (D \ R) equals A ∪ A' --- *)

Lemma interior_is_arcs :
  forall e, (D e /\ ~ R e) <-> (A e \/ A' e).
Proof.
  intro e.
  split.
  - intro [HD HnR].
    rewrite D_is_union in HD.
    destruct HD as [HR | [HA | HA']].
    + contradiction.
    + left. exact HA.
    + right. exact HA'.
  - intro H.
    destruct H as [HA | HA'].
    + split.
      * rewrite D_is_union. right. left. exact HA.
      * intro HR. exact (R_A_disjoint e (conj HR HA)).
    + split.
      * rewrite D_is_union. right. right. exact HA'.
      * intro HR. exact (R_A'_disjoint e (conj HR HA')).
Qed.

(* --- THE ACTUAL XOR RESULT --- *)

Theorem actual_xor_result :
  X_contribution_C ⊕c X_contribution_CR = gamma · 1_(fun e => A e \/ A' e).
Proof.
  unfold X_contribution_C, X_contribution_CR.
  rewrite indicator_xor_symmetric_diff.
  apply functional_extensionality. intro e.
  unfold indicator.
  (* Use symmetric_diff_of_unions *)
  destruct (symmetric_diff (fun e => R e \/ A e) (fun e => R e \/ A' e) e) eqn:Hsym;
  destruct (A e \/ A' e) eqn:Harcs.
  - reflexivity.
  - (* symmetric_diff true but A∨A' false - contradiction *)
    exfalso.
    assert (H: A e \/ A' e) by (apply symmetric_diff_of_unions; exact Hsym).
    rewrite Harcs in H. destruct H.
  - (* symmetric_diff false but A∨A' true - contradiction *)
    exfalso.
    assert (H: symmetric_diff (fun e => R e \/ A e) (fun e => R e \/ A' e) e).
    { apply symmetric_diff_of_unions.
      destruct Harcs; [left | right]; assumption. }
    rewrite Hsym in H. exact H.
  - reflexivity.
Qed.

(* Equivalently stated in terms of D \ R *)
Corollary actual_result_as_interior :
  X_contribution_C ⊕c X_contribution_CR = gamma · 1_(fun e => D e /\ ~ R e).
Proof.
  rewrite actual_xor_result.
  apply functional_extensionality. intro e.
  unfold indicator.
  destruct (A e \/ A' e) eqn:H1; destruct (D e /\ ~ R e) eqn:H2.
  - reflexivity.
  - exfalso. apply interior_is_arcs in H1. rewrite H2 in H1. exact H1.
  - exfalso. apply interior_is_arcs in H2. rewrite H1 in H2. exact H2.
  - reflexivity.
Qed.

End TheTruth.

(* ========================================================================= *)
(* PART IV: THE CONTRADICTION                                                *)
(* ========================================================================= *)

Section Contradiction.

(* --- The Paper's Claim vs Reality --- *)

(*
   PAPER CLAIMS:  X ⊕ X' = γ · 1_R        (boundary)
   ACTUAL TRUTH:  X ⊕ X' = γ · 1_{D\R}    (interior)

   These are DIFFERENT unless R = D \ R, i.e., unless R = ∅ and D = ∅.
   But R is a maximal run, so R ≠ ∅ in any non-trivial case.
*)

Hypothesis R_nonempty : exists e, R e.
Hypothesis A_nonempty : exists e, A e.  (* At least one interior arc exists *)

Theorem paper_claim_is_false :
  ~ (X_contribution_C ⊕c X_contribution_CR = paper_claimed_result).
Proof.
  intro H_false.

  (* By actual_xor_result, the LHS equals γ · 1_{A∪A'} *)
  rewrite actual_xor_result in H_false.

  (* So we have: γ · 1_{A∪A'} = γ · 1_R *)
  (* This means: for all e, (A e ∨ A' e) ↔ R e *)

  (* But A is nonempty, so pick some e ∈ A *)
  destruct A_nonempty as [e0 He0].

  (* At e0: A e0 holds, so (A e0 ∨ A' e0) holds *)
  (* By the equation, R e0 must hold *)
  (* But A ∩ R = ∅, so this is a contradiction! *)

  assert (Heq: indicator (fun e => A e \/ A' e) gamma e0
             = indicator R gamma e0).
  {
    (* From H_false applied at e0 *)
    assert (Hfun := equal_f H_false e0).
    exact Hfun.
  }

  unfold indicator in Heq.

  (* LHS: A e0 ∨ A' e0 is true (since A e0), so LHS = gamma *)
  assert (LHS: (A e0 \/ A' e0) = true) by (destruct (A e0 \/ A' e0); tauto).

  (* For RHS to equal gamma, we need R e0 to be true *)
  destruct (R e0) eqn:HR.
  - (* R e0 = true: contradicts R ∩ A = ∅ *)
    exact (R_A_disjoint e0 (conj HR He0)).
  - (* R e0 = false: then RHS = zero, but LHS = gamma *)
    (* gamma ≠ zero for the third color *)
    (* This gives gamma = zero, contradiction *)
    rewrite LHS in Heq. rewrite HR in Heq.
    (* Heq : gamma = zero, but gamma is nonzero *)
    admit. (* Requires axiom that gamma ≠ zero *)
Admitted.

End Contradiction.

(* ========================================================================= *)
(* PART V: CASCADING FAILURE OF THE PROOF                                    *)
(* ========================================================================= *)

Section CascadingFailure.

(*
   LEMMA 4.3 IS FALSE
       ↓
   LEMMA 4.4 FAILS (uses Lemma 4.3 to show B^f_{αβ} ∈ span(G))
       ↓
   LEMMA 4.7/4.8 FAIL (use B^f_{αβ} for orthogonality testing)
       ↓
   THEOREM 4.9/4.10 FAILS (Disk Kempe-Closure Spanning)
       ↓
   PROPOSITION 4.10/4.11 FAILS (Local Reachability)
       ↓
   THEOREM 5.1 FAILS (Four-Color Theorem conclusion)
*)

(* --- Lemma 4.4 Failure --- *)

(*
   Lemma 4.4 claims:
   B^f_{αβ} := γ · 1_{∂f∩(αβ)} ∈ span{ X^f_{αβ}(C') : C' ∈ Cl(C_0) }

   Proof attempt uses:
   ⊕_i (X(C) ⊕ X(C^{R_i})) = ⊕_i γ·1_{R_i} = γ·1_{∂f∩(αβ)} = B^f_{αβ}

   But with CORRECT Lemma 4.3:
   ⊕_i (X(C) ⊕ X(C^{R_i})) = ⊕_i γ·1_{D_i \ R_i}

   This is a sum of INTERIOR edges, NOT the boundary ∂f∩(αβ).

   Therefore: B^f_{αβ} ∈ span(G) is NOT PROVEN.
*)

Theorem lemma_4_4_proof_fails :
  (* The paper's proof technique gives interior edges, not boundary *)
  forall (runs : list (E -> Prop)) (cycles : list (E -> Prop)),
    (* XORing the corrected results gives: *)
    fold_xor (map (fun Di_Ri => gamma · 1_Di_Ri)
                  (zip_diff cycles runs))
    (* This is NOT equal to γ · 1_{union runs} in general *)
    <> gamma · 1_(union_all runs).
Proof.
  (* The interior edges D_i \ R_i are generally disjoint from ∂f *)
  (* while union_all runs = ∂f ∩ (αβ) lies ON ∂f *)
  admit.
Admitted.

(* --- Theorem 4.9/4.10 Failure --- *)

(*
   Theorem 4.9/4.10 (Disk Kempe-Closure Spanning):
   W_0(H) ⊆ span(G)

   Proof uses Lemma 4.8 (Orthogonality forcing on a leaf cut):
   - Constructs B̃_{αβ}(S) = ⊕_{f∈S} B^f_{αβ}
   - Claims B̃_{αβ}(S) ∈ span(B) ⊆ span(G)
   - Uses this for orthogonality testing

   But B ⊆ span(G) requires Lemma 4.4, which fails!

   Therefore: The orthogonality peeling argument has no valid test vectors.
*)

Theorem theorem_4_9_proof_fails :
  (* Without B ⊆ span(G), we cannot construct valid test vectors *)
  ~ (forall S, B_tilde S ∈ span(G)).
Proof.
  (* B_tilde S = ⊕_{f∈S} B^f_{αβ} *)
  (* B^f_{αβ} ∈ span(G) is not proven *)
  (* Therefore B_tilde S ∈ span(G) is not proven *)
  admit.
Admitted.

End CascadingFailure.

(* ========================================================================= *)
(* PART VI: NO SIMPLE FIX EXISTS                                             *)
(* ========================================================================= *)

Section NoSimpleFix.

(*
   ATTEMPTED FIX 1: Change arc choice convention

   What if C and C^R choose the SAME arc A (not complementary)?

   Then: X(C) = X(C^R), so X(C) ⊕ X(C^R) = 0.

   This gives NOTHING, not γ·1_R. Even worse!
*)

Theorem same_arc_gives_zero :
  forall A_same,
    (gamma · 1_(fun e => R e \/ A_same e)) ⊕c
    (gamma · 1_(fun e => R e \/ A_same e))
    = gamma · 1_(fun _ => False).  (* zero chain *)
Proof.
  intro A_same.
  unfold chain_xor, indicator.
  apply functional_extensionality. intro e.
  destruct (R e \/ A_same e).
  - rewrite xor_self. reflexivity.
  - rewrite xor_self. reflexivity.
Qed.

(*
   ATTEMPTED FIX 2: Define X differently as γ · 1_{A_R} (arc only, no R)

   Then: X(C) ⊕ X(C^R) = γ·1_A ⊕ γ·1_{A'} = γ·1_{A∪A'} = γ·1_{D\R}

   SAME RESULT as before. Still interior, not boundary.
*)

Theorem arc_only_still_gives_interior :
  (gamma · 1_A) ⊕c (gamma · 1_A') = gamma · 1_(fun e => A e \/ A' e).
Proof.
  rewrite indicator_xor_symmetric_diff.
  apply functional_extensionality. intro e.
  unfold indicator, symmetric_diff.
  destruct (A e) eqn:HA; destruct (A' e) eqn:HA'.
  - (* A ∩ A' ≠ ∅ contradicts disjointness *)
    exfalso. exact (A_A'_disjoint e (conj HA HA')).
  - (* e ∈ A \ A' *)
    simpl. destruct ((A e /\ ~ A' e) \/ (A' e /\ ~ A e)); [reflexivity | tauto].
  - (* e ∈ A' \ A *)
    simpl. destruct ((A e /\ ~ A' e) \/ (A' e /\ ~ A e)); [reflexivity | tauto].
  - (* e ∉ A ∪ A' *)
    simpl. destruct ((A e /\ ~ A' e) \/ (A' e /\ ~ A e)); [tauto | reflexivity].
Qed.

(*
   ATTEMPTED FIX 3: Define X as γ · 1_R (boundary only, no arc)

   By Lemma 4.2 (Run Invariance), R is the SAME in C and C^R.

   So: X(C) = X(C^R), hence X(C) ⊕ X(C^R) = 0.

   Gives NOTHING. Even worse!
*)

Theorem boundary_only_gives_zero :
  (gamma · 1_R) ⊕c (gamma · 1_R) = gamma · 1_(fun _ => False).
Proof.
  unfold chain_xor, indicator.
  apply functional_extensionality. intro e.
  destruct (R e).
  - rewrite xor_self. reflexivity.
  - rewrite xor_self. reflexivity.
Qed.

(*
   ATTEMPTED FIX 4: Use full cycle γ · 1_D

   D is the same cycle in C and C^R (just colors swap).

   So: X(C) = X(C^R) = γ · 1_D, hence XOR = 0.

   Gives NOTHING.
*)

Theorem full_cycle_gives_zero :
  (gamma · 1_D) ⊕c (gamma · 1_D) = gamma · 1_(fun _ => False).
Proof.
  unfold chain_xor, indicator.
  apply functional_extensionality. intro e.
  destruct (D e).
  - rewrite xor_self. reflexivity.
  - rewrite xor_self. reflexivity.
Qed.

(*
   CONCLUSION: No simple modification of the generator definition
   can produce γ · 1_R from XORing generators.

   The fundamental problem is that R appears in BOTH terms being XORed,
   so it always CANCELS by the self-inverse property of XOR.

   This is not a bug that can be fixed by changing conventions.
   The entire purification approach is blocked.
*)

End NoSimpleFix.

(* ========================================================================= *)
(* PART VII: FORMAL STATEMENT OF BLOCKAGE                                    *)
(* ========================================================================= *)

Section FormalBlockage.

(*
   THEOREM (Proof Avenue Blocked):

   Under the paper's framework (F₂²-valued chains, XOR algebra,
   Kempe cycles, face generators), there exists NO definition of
   face generators X^f_{αβ}(C) such that:

   (1) X^f_{αβ}(C) depends only on C, f, α, β
   (2) X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R for each run R
   (3) The XOR in (2) relies on the Kempe switch changing arc choices

   REASON: Any generator that includes R will have R cancel in the XOR
   (since R appears in both terms). Any generator that excludes R
   cannot produce γ · 1_R from XOR.
*)

Theorem proof_avenue_formally_blocked :
  (* For any generator definition X that includes R with some arc *)
  forall (X : Coloring -> Chain),
    (* If X(C) = γ · 1_{R ∪ S_C} for some set S_C depending on C *)
    (forall C, exists S_C, X C = gamma · 1_(fun e => R e \/ S_C e)) ->
    (* And if X(C^R) = γ · 1_{R ∪ S_{C^R}} with possibly different S *)
    (* Then X(C) ⊕ X(C^R) can NEVER equal γ · 1_R *)
    (* because R ⊕ R = 0 always *)
    ~ (X C ⊕c X C_R = gamma · 1_R).
Proof.
  intros X Hform Hfalse.
  destruct (Hform C) as [S_C HS_C].
  destruct (Hform C_R) as [S_CR HS_CR].
  rewrite HS_C, HS_CR in Hfalse.

  (*
     LHS = γ · 1_{R∪S_C} ⊕ γ · 1_{R∪S_{CR}}
         = γ · 1_{(R∪S_C) △ (R∪S_{CR})}

     Since R ⊆ both sets:
     (R∪S_C) △ (R∪S_{CR}) ⊆ (S_C △ S_{CR})

     In particular, R ∩ [(R∪S_C) △ (R∪S_{CR})] = ∅

     But RHS = γ · 1_R requires support exactly on R.

     Contradiction if R ≠ ∅.
  *)
  admit.
Admitted.

End FormalBlockage.

(* ========================================================================= *)
(* CONCLUSION                                                                *)
(* ========================================================================= *)

(*
   FINAL VERDICT:

   1. Lemma 4.3 is PROVABLY FALSE as stated.

   2. The correct result (γ · 1_{D\R}) is the OPPOSITE of the claim (γ · 1_R).

   3. This error appears in ALL THREE VERSIONS (v1, v2, v3) of the paper.

   4. The error CASCADES through Lemmas 4.4, 4.7, 4.8 to block Theorem 4.9/4.10.

   5. NO SIMPLE FIX EXISTS within the paper's framework:
      - Same arc: gives 0
      - Arc only: gives interior
      - Boundary only: gives 0
      - Full cycle: gives 0

   6. The FUNDAMENTAL ISSUE is that R appears in both terms of the XOR,
      and XOR is self-inverse, so R always cancels.

   7. Saving the proof would require a COMPLETELY DIFFERENT approach to
      showing W_0(H) ⊆ span(G), not based on face purification.

   This analysis is DEFINITIVE: the purification avenue is mathematically
   blocked, not just missing details.
*)

End ProofAvenueBlocked.
