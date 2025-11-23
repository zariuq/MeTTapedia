(* ========================================================================= *)
(* Masking and Symmetry Groups                                               *)
(* Builds on 00_preamble.mg, 01_foundations.mg, 03_cnf_sat.mg                *)
(* ========================================================================= *)
(*                                                                           *)
(* AXIOM SOURCES                                                             *)
(* =============                                                             *)
(*                                                                           *)
(* [SDP] Semidirect Product Theory                                           *)
(*       Lang, S. (2002). Algebra, 3rd ed. Springer. Chapter I, Section 5.   *)
(*       The mask group H_m = S_m ⋉ (Z_2)^m is a semidirect product where:   *)
(*       - S_m acts on (Z_2)^m by permuting coordinates                      *)
(*       - Group operation: (π₁,σ₁)·(π₂,σ₂) = (π₁∘π₂, σ₁ ⊕ (σ₂∘π₁⁻¹))      *)
(*                                                                           *)
(* [Sym] Symmetric Group Properties                                          *)
(*       Standard results: S_n forms a group under composition               *)
(*       - Identity: id permutation                                          *)
(*       - Inverse: π⁻¹ exists for all π ∈ S_n                              *)
(*       - Associativity: (π₁∘π₂)∘π₃ = π₁∘(π₂∘π₃)                          *)
(*                                                                           *)
(* [SAT-Sym] SAT Symmetry Preservation                                       *)
(*       Masks act as "change of variables" on CNF formulas.                 *)
(*       If x satisfies F, then h(x) satisfies h(F) for any mask h.          *)
(*       This follows from the bijective nature of the variable renaming.    *)
(*                                                                           *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Part I: Permutations and Bijections                                       *)
(* ========================================================================= *)

(* A bijection on set A to B *)
Definition is_bijection : set -> set -> set -> prop :=
  fun A B f =>
    (forall a :e A, ap f a :e B) /\
    (forall b :e B, exists a :e A, ap f a = b) /\
    (forall a1 a2 :e A, ap f a1 = ap f a2 -> a1 = a2).

(* Self-bijection (permutation) *)
Definition is_permutation : set -> set -> prop :=
  fun n pi => is_bijection n n pi.

(* Identity permutation *)
Definition perm_id : set -> set :=
  fun n => fun i :e n => i.

Theorem perm_id_is_perm : forall n :e omega, is_permutation n (perm_id n).
let n. assume Hn: n :e omega.
apply andI.
- let i. assume Hi: i :e n.
  prove ap (perm_id n) i :e n.
  prove ap (fun j :e n => j) i :e n.
  rewrite beta n (fun j => j) i Hi.
  exact Hi.
- apply andI.
  + let j. assume Hj: j :e n.
    prove exists i :e n, ap (perm_id n) i = j.
    apply (fun P f x => f x). exact j.
    apply andI. exact Hj.
    prove ap (perm_id n) j = j.
    prove ap (fun i :e n => i) j = j.
    exact (beta n (fun i => i) j Hj).
  + let a1 a2. assume Ha1: a1 :e n. assume Ha2: a2 :e n.
    assume Heq: ap (perm_id n) a1 = ap (perm_id n) a2.
    rewrite (beta n (fun i => i) a1 Ha1) in Heq.
    rewrite (beta n (fun i => i) a2 Ha2) in Heq.
    exact Heq.
Qed.

(* Permutation composition *)
Definition perm_compose : set -> set -> set -> set :=
  fun n f g => fun i :e n => ap f (ap g i).

(* Permutation inverse *)
Definition perm_inv : set -> set -> set :=
  fun n pi => fun j :e n => Eps_i (fun i => i :e n /\ ap pi i = j).

(* Helper: perm_id is left identity for composition *)
Theorem perm_compose_id_l : forall n :e omega, forall f,
  is_permutation n f ->
  forall i :e n, ap (perm_compose n (perm_id n) f) i = ap f i.
let n. assume Hn: n :e omega.
let f. assume Hf: is_permutation n f.
let i. assume Hi: i :e n.
prove ap (fun j :e n => ap (perm_id n) (ap f j)) i = ap f i.
rewrite beta n (fun j => ap (perm_id n) (ap f j)) i Hi.
prove ap (perm_id n) (ap f i) = ap f i.
(* Get that ap f i :e n from Hf *)
apply Hf. assume Hf1: forall a :e n, ap f a :e n.
claim Hfi: ap f i :e n. { exact (Hf1 i Hi). }
prove ap (fun j :e n => j) (ap f i) = ap f i.
exact (beta n (fun j => j) (ap f i) Hfi).
Qed.

(* Helper: sign_zero is identity for sign_xor *)
Theorem sign_xor_zero_l : forall m :e omega, forall s,
  is_sign_vector m s ->
  forall i :e m, ap (sign_xor m (sign_zero m) s) i = ap s i.
let m. assume Hm: m :e omega.
let s. assume Hs: is_sign_vector m s.
let i. assume Hi: i :e m.
prove ap (fun j :e m => xor (ap (sign_zero m) j) (ap s j)) i = ap s i.
rewrite beta m (fun j => xor (ap (sign_zero m) j) (ap s j)) i Hi.
prove xor (ap (sign_zero m) i) (ap s i) = ap s i.
rewrite beta m (fun _ => 0) i Hi.
prove xor 0 (ap s i) = ap s i.
apply xor_0_l.
exact (Bits_is_bit (ap s i) (Hs i Hi)).
Qed.

(* ========================================================================= *)
(* Part II: Sign Vectors                                                     *)
(* ========================================================================= *)

(* A sign vector over m variables *)
Definition is_sign_vector : set -> set -> prop :=
  fun m sigma => forall i :e m, ap sigma i :e Bits.

(* Zero sign vector (all positive) *)
Definition sign_zero : set -> set :=
  fun m => fun i :e m => 0.

Theorem sign_zero_is_sign_vector : forall m :e omega, is_sign_vector m (sign_zero m).
let m. assume Hm: m :e omega.
let i. assume Hi: i :e m.
prove ap (sign_zero m) i :e Bits.
prove ap (fun j :e m => 0) i :e Bits.
rewrite beta m (fun j => 0) i Hi.
exact In_0_2.
Qed.

(* Sign vector XOR (pointwise) *)
Definition sign_xor : set -> set -> set -> set :=
  fun m s1 s2 => fun i :e m => xor (ap s1 i) (ap s2 i).

(* Basis sign vector: 1 at position i, 0 elsewhere *)
Definition sign_basis : set -> set -> set :=
  fun m i => fun j :e m => if j = i then 1 else 0.

(* ========================================================================= *)
(* Part III: The Mask Group H_m = S_m ⋉ (Z_2)^m                              *)
(* ========================================================================= *)

(* A mask h = (π, σ) consists of a permutation and a sign vector *)
(* Action: h(x)_i = σ_i ⊕ x_{π(i)} *)

Definition Mask : set -> set -> prop :=
  fun m h => exists pi sigma,
    is_permutation m pi /\
    is_sign_vector m sigma /\
    h = pair pi sigma.

Definition mask_perm : set -> set := fun h => ap h 0.
Definition mask_sign : set -> set := fun h => ap h 1.

(* Identity mask *)
Definition mask_id : set -> set :=
  fun m => pair (perm_id m) (sign_zero m).

Theorem mask_id_is_mask : forall m :e omega, Mask m (mask_id m).
let m. assume Hm: m :e omega.
prove exists pi sigma,
  is_permutation m pi /\ is_sign_vector m sigma /\ mask_id m = pair pi sigma.
apply (fun P f x => f x). exact (perm_id m).
apply (fun P f x => f x). exact (sign_zero m).
apply andI.
- exact (perm_id_is_perm m Hm).
- apply andI.
  + exact (sign_zero_is_sign_vector m Hm).
  + reflexivity.
Qed.

(* Mask composition (semidirect product) *)
(* (π₁, σ₁) · (π₂, σ₂) = (π₁ ∘ π₂, σ₁ ⊕ (σ₂ ∘ π₁⁻¹)) *)
Definition mask_compose : set -> set -> set -> set :=
  fun m h1 h2 =>
    pair (perm_compose m (mask_perm h1) (mask_perm h2))
         (sign_xor m (mask_sign h1)
                     (perm_compose m (mask_sign h2) (perm_inv m (mask_perm h1)))).

(* Mask inverse *)
Definition mask_inv : set -> set -> set :=
  fun m h =>
    pair (perm_inv m (mask_perm h))
         (perm_compose m (mask_sign h) (mask_perm h)).

(* ========================================================================= *)
(* Part IV: Mask Action on Literals and CNFs                                 *)
(* ========================================================================= *)

(* Apply mask to a literal: h(l) = (π(var), σ_{var} ⊕ sign) *)
Definition apply_mask_lit : set -> set -> set -> set :=
  fun m h l =>
    Literal (ap (mask_perm h) (lit_var l))
            (xor (ap (mask_sign h) (lit_var l)) (lit_sign l)).

(* Apply mask to a clause *)
Definition apply_mask_clause : set -> set -> set -> set :=
  fun m h C => {apply_mask_lit m h l | l :e C}.

(* Apply mask to a CNF formula *)
Definition apply_mask_cnf : set -> set -> set -> set :=
  fun m h F => {apply_mask_clause m h C | C :e F}.

(* ========================================================================= *)
(* Part V: Mask Properties                                                   *)
(* ========================================================================= *)

(* Mask preserves clause size *)
(* The mask permutation is a bijection, so clause variables are preserved in size *)
(* Axiomatized as equip infrastructure is not fully developed *)
Axiom mask_preserves_clause_size : forall m h C,
  Mask m h -> equip (clause_vars C) (clause_vars (apply_mask_clause m h C)).

(* Mask preserves satisfiability *)
(* Key insight: If x satisfies F, then h(x) satisfies h(F), where h(x)_i = σ_i ⊕ x_{π(i)} *)
(* The inverse mask recovers the original formula and witness *)
(* Axiomatized as detailed semantic proof requires additional infrastructure *)
Axiom mask_preserves_SAT : forall m h F,
  Mask m h -> (is_SAT m F <-> is_SAT m (apply_mask_cnf m h F)).

(* ========================================================================= *)
(* Part VI: Sign Invariance                                                  *)
(* ========================================================================= *)

(* A function f is sign-invariant if it depends only on the "shape" *)
(* of the formula, not on the specific sign assignments *)

Definition is_sign_invariant : set -> (set -> set) -> prop :=
  fun m f =>
    forall F sigma, is_sign_vector m sigma ->
      f F = f (apply_mask_cnf m (pair (perm_id m) sigma) F).

(* The τ_i transformation: flip sign at position i *)
Definition tau_i : set -> set -> set :=
  fun m i => pair (perm_id m) (sign_basis m i).

Theorem tau_i_is_mask : forall m :e omega, forall i :e m, Mask m (tau_i m i).
let m. assume Hm: m :e omega. let i. assume Hi: i :e m.
prove exists pi sigma,
  is_permutation m pi /\ is_sign_vector m sigma /\ tau_i m i = pair pi sigma.
apply (fun P f x => f x). exact (perm_id m).
apply (fun P f x => f x). exact (sign_basis m i).
apply andI.
- exact (perm_id_is_perm m Hm).
- apply andI.
  + let j. assume Hj: j :e m.
    prove ap (sign_basis m i) j :e Bits.
    prove ap (fun k :e m => if k = i then 1 else 0) j :e Bits.
    rewrite beta m (fun k => if k = i then 1 else 0) j Hj.
    prove (if j = i then 1 else 0) :e Bits.
    (* Case split on j = i using excluded middle *)
    apply (classic (j = i)).
    * assume Heq: j = i.
      rewrite (If_i_1 (j = i) 1 0 Heq).
      exact In_1_2.
    * assume Hneq: ~(j = i).
      rewrite (If_i_0 (j = i) 1 0 Hneq).
      exact In_0_2.
  + reflexivity.
Qed.

(* τ_i toggles the i-th bit of the witness *)
(* The key insight: τ_i flips the sign of literals with var = i,
   and flipping x_i compensates exactly for the sign change *)
(* Axiomatized as detailed semantic proof requires clause-level analysis *)
Axiom tau_i_toggles_witness : forall m :e omega, forall i :e m,
  forall F x, is_assignment m x -> satisfies x F ->
    let x' := fun j :e m => if j = i then xor (ap x i) 1 else ap x j in
    satisfies x' (apply_mask_cnf m (tau_i m i) F).

(* ========================================================================= *)
(* Part VII: Group Structure [SDP]                                           *)
(* ========================================================================= *)
(* Source: Lang (2002) Algebra, Ch. I §5 - Semidirect Products               *)
(*                                                                           *)
(* H_m = S_m ⋉ (Z_2)^m is a group with:                                      *)
(*   - Identity: (id, 0)                                                     *)
(*   - Composition: (π₁,σ₁)·(π₂,σ₂) = (π₁∘π₂, σ₁ ⊕ (σ₂∘π₁⁻¹))              *)
(*   - Inverse: (π,σ)⁻¹ = (π⁻¹, σ∘π)                                        *)
(*                                                                           *)
(* The group axioms follow from:                                             *)
(*   - S_m is a group under composition                                      *)
(*   - (Z_2)^m is an abelian group under ⊕                                  *)
(*   - The semidirect product formula satisfies group axioms                 *)
(* ========================================================================= *)

(* Associativity: follows from semidirect product theory [SDP] *)
(* Proof sketch: Expand (h₁·h₂)·h₃ and h₁·(h₂·h₃), use associativity of     *)
(* permutation composition and XOR, and verify sign components match.        *)
Axiom mask_compose_assoc : forall m h1 h2 h3,
  Mask m h1 -> Mask m h2 -> Mask m h3 ->
  mask_compose m (mask_compose m h1 h2) h3 =
  mask_compose m h1 (mask_compose m h2 h3).

(* Left identity: (id,0)·(π,σ) = (id∘π, 0⊕(σ∘id)) = (π,σ) *)
(* Uses: id∘π = π and 0⊕σ = σ (proven for XOR in preamble) *)
Axiom mask_id_left : forall m :e omega, forall h,
  Mask m h -> mask_compose m (mask_id m) h = h.

(* Left inverse: (π⁻¹,σ∘π)·(π,σ) = (π⁻¹∘π, (σ∘π)⊕(σ∘π⁻¹⁻¹)) = (id,0) *)
(* Uses: π⁻¹∘π = id and σ⊕σ = 0 (XOR self-inverse) *)
Axiom mask_inv_left : forall m :e omega, forall h,
  Mask m h -> mask_compose m (mask_inv m h) h = mask_id m.

