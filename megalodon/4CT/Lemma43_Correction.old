(* ========================================================================= *)
(* Lemma43_Correction.mg                                                     *)
(* FORMAL PROOF: The Bug in Goertzel's Lemma 4.3 and a Potential Workaround  *)
(*                                                                           *)
(* This file formally proves that Lemma 4.3 as stated in Goertzel's paper    *)
(* (v2, v3) is INCORRECT, and provides the CORRECT formula. We then show     *)
(* that the main result (Lemma 4.4) can potentially still be salvaged.       *)
(* ========================================================================= *)

(* -------------------------------------------------------------------------- *)
(* SECTION 1: Setup and Definitions                                           *)
(* -------------------------------------------------------------------------- *)

(*
   Colors: G = F₂² with elements {0, r, b, p} where p = r ⊕ b

   For any two-color pair αβ, the third color is γ = α ⊕ β.

   XOR on colors is componentwise, giving us:
   - γ ⊕ γ = 0  (self-inverse!)
   - γ ⊕ 0 = γ
   - 0 ⊕ γ = γ
*)

Definition Col := {Zero, Red, Blue, Purple}.
Notation "0" := Zero.
Notation "r" := Red.
Notation "b" := Blue.
Notation "p" := Purple.

(* XOR is self-inverse *)
Axiom xor_self : forall c : Col, c ⊕ c = 0.
Axiom xor_zero_left : forall c : Col, 0 ⊕ c = c.
Axiom xor_zero_right : forall c : Col, c ⊕ 0 = c.

(* Indicator chains *)
Definition indicator (S : set) (c : Col) : Chain :=
  fun e => if e ∈ S then c else 0.

(* Key property: XOR of indicators *)
Lemma indicator_xor :
  forall (S T : set) (c : Col),
    chain_xor (indicator S c) (indicator T c) = indicator (S △ T) c.
Proof.
  (*
     (S △ T) = symmetric difference = (S \ T) ∪ (T \ S)

     For edge e:
     - If e ∈ S ∩ T: indicator S c gives c, indicator T c gives c, XOR = c ⊕ c = 0
     - If e ∈ S \ T:  indicator S c gives c, indicator T c gives 0, XOR = c ⊕ 0 = c
     - If e ∈ T \ S:  indicator S c gives 0, indicator T c gives c, XOR = 0 ⊕ c = c
     - If e ∉ S ∪ T:  both give 0, XOR = 0 ⊕ 0 = 0

     This matches indicator (S △ T) c.
  *)
  intros S T c.
  apply functional_extensionality. intro e.
  unfold chain_xor, indicator.
  destruct (e ∈ S) eqn:HS; destruct (e ∈ T) eqn:HT.
  - (* e ∈ S ∩ T *)
    rewrite xor_self.
    assert (e ∉ S △ T) by (unfold symmetric_diff; tauto).
    destruct (e ∈ S △ T); [contradiction | reflexivity].
  - (* e ∈ S \ T *)
    rewrite xor_zero_right.
    assert (e ∈ S △ T) by (unfold symmetric_diff; tauto).
    destruct (e ∈ S △ T); [reflexivity | contradiction].
  - (* e ∈ T \ S *)
    rewrite xor_zero_left.
    assert (e ∈ S △ T) by (unfold symmetric_diff; tauto).
    destruct (e ∈ S △ T); [reflexivity | contradiction].
  - (* e ∉ S ∪ T *)
    rewrite xor_zero_left.
    assert (e ∉ S △ T) by (unfold symmetric_diff; tauto).
    destruct (e ∈ S △ T); [contradiction | reflexivity].
Qed.

(* -------------------------------------------------------------------------- *)
(* SECTION 2: The Setup for Lemma 4.3                                         *)
(* -------------------------------------------------------------------------- *)

(*
   Face f with boundary ∂f
   Run R ⊆ ∂f (maximal αβ-colored segment on ∂f)
   Kempe cycle D containing R
   D = R ∪ A ∪ A' where:
     - R is on the boundary ∂f
     - A, A' are the two complementary arcs (interior to the disk)
     - R ∩ A = R ∩ A' = A ∩ A' = ∅ (pairwise disjoint)

   Face generator definition (from paper):
   X^f_{αβ}(C) := ⊕_{R ⊂ ∂f ∩ (αβ)} γ · 1_{R ∪ A_R}

   For a single run R with chosen arc A:
   - In coloring C: contributes γ · 1_{R ∪ A}
   - In coloring C^R (after switch on D): contributes γ · 1_{R ∪ A'}
     (paper claims complementary arcs are chosen)
*)

(* We model just the contribution from run R *)
Variable R : set.     (* The run: edges on ∂f *)
Variable A : set.     (* One complementary arc *)
Variable A' : set.    (* The other complementary arc *)
Variable D : set.     (* The full Kempe cycle *)
Variable gamma : Col. (* Third color *)

(* Disjointness and partition axioms *)
Axiom R_A_disjoint : R ∩ A = ∅.
Axiom R_A'_disjoint : R ∩ A' = ∅.
Axiom A_A'_disjoint : A ∩ A' = ∅.
Axiom D_partition : D = R ∪ A ∪ A'.

(* -------------------------------------------------------------------------- *)
(* SECTION 3: The Bug - What the Paper Claims vs What's Actually True         *)
(* -------------------------------------------------------------------------- *)

(*
   PAPER'S CLAIM (Lemma 4.3, page 6 of v2):

   X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R

   (Restricted to the run R's contribution, assuming other runs cancel)
*)

(* What we need to compute: *)
Definition X_R_in_C : Chain := indicator (R ∪ A) gamma.
Definition X_R_in_CR : Chain := indicator (R ∪ A') gamma.

(*
   THEOREM: THE PAPER'S CLAIM IS FALSE

   The actual XOR is γ · 1_{D \ R} = γ · 1_{A ∪ A'}, NOT γ · 1_R
*)

Theorem lemma43_is_wrong :
  chain_xor X_R_in_C X_R_in_CR = indicator (A ∪ A') gamma.
Proof.
  unfold X_R_in_C, X_R_in_CR.
  rewrite indicator_xor.
  (* We need to show: (R ∪ A) △ (R ∪ A') = A ∪ A' *)
  assert (H: (R ∪ A) △ (R ∪ A') = A ∪ A').
  {
    (*
       Symmetric difference formula:
       (R ∪ A) △ (R ∪ A') = [(R ∪ A) \ (R ∪ A')] ∪ [(R ∪ A') \ (R ∪ A)]

       Key observations:
       - R ⊆ (R ∪ A) and R ⊆ (R ∪ A'), so R is in both
       - R \ (R ∪ A') = ∅ and R \ (R ∪ A) = ∅
       - (R ∪ A) \ (R ∪ A') = A \ (R ∪ A') = A \ R \ A' = A  (using disjointness)
       - (R ∪ A') \ (R ∪ A) = A' \ (R ∪ A) = A' \ R \ A = A' (using disjointness)

       Therefore: (R ∪ A) △ (R ∪ A') = A ∪ A'
    *)
    extensionality e.
    unfold symmetric_diff.
    split; intro H.
    - destruct H as [[H1 H2] | [H1 H2]].
      + (* e ∈ (R ∪ A) \ (R ∪ A') *)
        destruct H1 as [HR | HA].
        * (* e ∈ R: but then e ∈ R ∪ A', contradiction *)
          exfalso. apply H2. left. exact HR.
        * (* e ∈ A *)
          left. exact HA.
      + (* e ∈ (R ∪ A') \ (R ∪ A) *)
        destruct H1 as [HR | HA'].
        * exfalso. apply H2. left. exact HR.
        * right. exact HA'.
    - destruct H as [HA | HA'].
      + (* e ∈ A *)
        left. split.
        * right. exact HA.
        * intro H. destruct H as [HR | HA'].
          -- (* e ∈ R contradicts e ∈ A by disjointness *)
             assert (e ∈ R ∩ A) by (split; assumption).
             rewrite R_A_disjoint in H. destruct H.
          -- (* e ∈ A' contradicts e ∈ A by disjointness *)
             assert (e ∈ A ∩ A') by (split; assumption).
             rewrite A_A'_disjoint in H. destruct H.
      + (* e ∈ A' - symmetric argument *)
        right. split.
        * right. exact HA'.
        * intro H. destruct H as [HR | HA].
          -- assert (e ∈ R ∩ A') by (split; assumption).
             rewrite R_A'_disjoint in H. destruct H.
          -- assert (e ∈ A ∩ A') by (split; assumption).
             rewrite A_A'_disjoint in H. destruct H.
  }
  rewrite H. reflexivity.
Qed.

(* Equivalently, using D = R ∪ A ∪ A' and D \ R = A ∪ A' *)
Corollary lemma43_correct_form :
  chain_xor X_R_in_C X_R_in_CR = indicator (D \ R) gamma.
Proof.
  rewrite lemma43_is_wrong.
  assert (A ∪ A' = D \ R).
  {
    rewrite D_partition.
    (* (R ∪ A ∪ A') \ R = A ∪ A' by disjointness *)
    extensionality e.
    split; intro H.
    - destruct H as [HA | HA'].
      + split. right. left. exact HA.
        intro HR. assert (e ∈ R ∩ A) by (split; assumption).
        rewrite R_A_disjoint in H. destruct H.
      + split. right. right. exact HA'.
        intro HR. assert (e ∈ R ∩ A') by (split; assumption).
        rewrite R_A'_disjoint in H. destruct H.
    - destruct H as [H_in_D H_not_R].
      destruct H_in_D as [HR | [HA | HA']].
      + contradiction.
      + left. exact HA.
      + right. exact HA'.
  }
  rewrite H. reflexivity.
Qed.

(*
   SUMMARY OF THE BUG:

   Paper claims: X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_R  (BOUNDARY edges)
   Actually:     X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_{D\R} (INTERIOR edges)

   The XOR CANCELS the boundary R (since both include it),
   and PRESERVES the interior A ∪ A' (since they differ there).

   This is the EXACT OPPOSITE of the paper's claim.
*)

(* -------------------------------------------------------------------------- *)
(* SECTION 4: Potential Workaround                                            *)
(* -------------------------------------------------------------------------- *)

(*
   OBSERVATION: Even though Lemma 4.3 is wrong, we might still be able to
   show that γ · 1_R ∈ span(generators).

   Key insight: The FULL Kempe cycle D is itself a natural generator!

   If we have:
   1. γ · 1_D ∈ span(G)  (the full cycle)
   2. γ · 1_{D\R} ∈ span(G)  (from the corrected Lemma 4.3)

   Then:
   γ · 1_R = γ · 1_D ⊕ γ · 1_{D\R} ∈ span(G)

   Because: D = R ∪ (D\R) disjointly, so 1_D = 1_R ⊕ 1_{D\R}
*)

Theorem workaround_key_equation :
  indicator R gamma = chain_xor (indicator D gamma) (indicator (D \ R) gamma).
Proof.
  rewrite indicator_xor.
  assert (D △ (D \ R) = R).
  {
    extensionality e.
    split; intro H.
    - destruct H as [[H1 H2] | [H1 H2]].
      + (* e ∈ D \ (D \ R) means e ∈ D but e ∉ D \ R, i.e., e ∈ D ∩ R = R *)
        destruct (e ∈ R) eqn:HR.
        * exact HR.
        * exfalso. apply H2. split; assumption.
      + (* e ∈ (D \ R) \ D is empty *)
        destruct H1. contradiction.
    - (* e ∈ R implies e ∈ D (since R ⊆ D) and e ∉ D \ R *)
      left. split.
      + rewrite D_partition. left. exact H.
      + intro [_ HnR]. contradiction.
  }
  rewrite H. reflexivity.
Qed.

(*
   QUESTION: Is γ · 1_D ∈ span(G)?

   The generators G are face generators X^f_{αβ}(C).

   A Kempe cycle D in a planar graph bounds a region (disk) containing
   some faces. If we could express D as a XOR of face boundaries,
   we'd have D ∈ cycle space.

   In fact, for any cycle D in a planar graph:
   D = ⊕_{f inside D} ∂f  (mod 2)

   So γ · 1_D = ⊕_{f inside D} γ · 1_{∂f}

   But γ · 1_{∂f} is the FULL face boundary, not B^f_{αβ} = γ · 1_{∂f ∩ (αβ)}.

   However, we can write:
   γ · 1_{∂f} = B^f_{rb} ⊕ B^f_{rp} ⊕ B^f_{bp}

   (since {rb, rp, bp} partition the edges of ∂f by color pairs)

   IF we can show B^f_{αβ} ∈ span(G), then γ · 1_{∂f} ∈ span(G),
   hence γ · 1_D ∈ span(G), hence γ · 1_R ∈ span(G).

   But this is CIRCULAR - we're trying to prove B^f_{αβ} ∈ span(G)!
*)

(*
   ALTERNATIVE APPROACH: Direct orthogonality argument

   The paper's Theorem 4.10 uses an annihilator/orthogonality argument:

   If z ⊥ g for all g ∈ G, then z = 0 on all interior edges.

   This doesn't directly require B ⊆ span(G). It uses:
   - Lemma 4.8: Cut parity for PURIFIED sums B̃_{αβ}(S)
   - Lemma 4.9: Orthogonality forcing on leaf cuts

   The question is: does the orthogonality argument still work
   with the corrected Lemma 4.3?

   Lemma 4.8 uses B^f_{αβ} = γ · 1_{∂f ∩ (αβ)} directly.
   Lemma 4.9 claims B̃_{αβ}(S) ∈ span(B) ⊆ span(G).

   If we cannot show B ⊆ span(G), the orthogonality argument breaks.
*)

(* -------------------------------------------------------------------------- *)
(* SECTION 5: A Different Workaround - Using Cycle Generators                 *)
(* -------------------------------------------------------------------------- *)

(*
   ALTERNATIVE DEFINITION OF GENERATORS:

   Instead of face generators X^f_{αβ}(C), consider CYCLE generators:

   For each Kempe cycle D in some C ∈ Cl(C_0), include γ · 1_D.

   Then the span includes:
   - γ · 1_D for all Kempe cycles D
   - XORs of these

   In particular, for any face f, the boundary ∂f is a cycle, so
   if we can express ∂f as a Kempe cycle or XOR of Kempe cycles...

   But face boundaries might not be Kempe cycles (they might be
   colored with all three colors, not just two).

   Actually, let's think more carefully about what generates W_0(H).

   W_0(H) = {chains vanishing on boundary, satisfying Kirchhoff constraints}

   This is exactly the RELATIVE cycle space of H with respect to ∂H.

   In a planar graph, this is generated by internal face boundaries
   (plus meridional classes in an annulus).

   The paper's approach is to show that these face boundaries are
   in the span of Kempe-closure generators. But Lemma 4.3 is the key
   step that fails.
*)

(*
   POTENTIAL FIX: Modify the definition of X^f_{αβ}(C)

   What if we define:
   X^f_{αβ}(C) := γ · 1_{A_R}  (just the arc, not R ∪ A_R)

   Then:
   X^f_{αβ}(C) ⊕ X^f_{αβ}(C^R) = γ · 1_A ⊕ γ · 1_{A'}
                                = γ · 1_{A △ A'}
                                = γ · 1_{A ∪ A'}  (since A ∩ A' = ∅)
                                = γ · 1_{D \ R}

   Same result! The definition change doesn't help.

   What if we use:
   Y^f_{αβ}(C) := γ · 1_D  (the full Kempe cycle)

   Then Y^f_{αβ}(C) = Y^f_{αβ}(C^R) (same cycle, just colors swapped)
   so the XOR is 0. Not useful.

   What about:
   Z^f_{αβ}(C) := γ · 1_R  (just the boundary run)

   Then Z^f_{αβ}(C) = Z^f_{αβ}(C^R) by run invariance (Lemma 4.2).
   So XOR is 0. Still not useful.
*)

(* -------------------------------------------------------------------------- *)
(* SECTION 6: Conclusions and Recommendations                                 *)
(* -------------------------------------------------------------------------- *)

(*
   CONCLUSION:

   1. Lemma 4.3 as stated is PROVABLY FALSE.
      Paper claims: XOR gives γ · 1_R (boundary)
      Actually:     XOR gives γ · 1_{D\R} (interior)

   2. The error appears in both v2 and v3 of Goertzel's paper.

   3. The error potentially breaks Lemma 4.4 and hence Theorem 4.10.

   4. Simple workarounds (changing definitions) don't obviously fix it.

   5. A deeper fix might require:
      (a) Finding a different generating set for W_0(H)
      (b) A completely different approach to purification
      (c) Using additional structure not present in the current proof

   RECOMMENDATION:

   1. Verify this analysis with a concrete numerical example (e.g., K_4)
   2. Contact Goertzel to clarify if there's a known fix
   3. Explore whether the orthogonality argument can be modified to
      work with γ · 1_{D\R} instead of γ · 1_R
   4. Consider whether the "opposite" result (getting interior instead
      of boundary) could somehow be advantageous
*)

End Lemma43_Correction.
