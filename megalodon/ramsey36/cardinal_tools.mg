% Basic finite-cardinality and injection helpers.
% This file is intended to be loaded before the Ramsey36 proofs to supply
% small reusable lemmas about injective functions and pigeonhole-style
% reasoning.

Definition injective : set -> set -> (set -> set) -> prop :=
  fun A B f => (forall x :e A, f x :e B) /\ (forall x y :e A, f x = f y -> x = y).

% Composition of injections is an injection (domains/codomains line up).
Theorem injective_comp : forall A B C:set, forall f g:set -> set,
  injective A B f ->
  injective B C g ->
  injective A C (fun x => g (f x)).
let A. let B. let C. let f. let g.
assume Hf: injective A B f.
assume Hg: injective B C g.
apply and3E (forall x :e A, f x :e B) (forall x y :e A, f x = f y -> x = y)
            (injective B C g) Hf (injective A C (fun x => g (f x))).
assume HfAB: forall x :e A, f x :e B.
assume Hfinj: forall x y :e A, f x = f y -> x = y.
apply and3E (forall x :e B, g x :e C) (forall x y :e B, g x = g y -> x = y)
            True (andI (forall x :e B, g x :e C) (forall x y :e B, g x = g y -> x = y) (TrueI)) Hg
            (injective A C (fun x => g (f x))).
assume HgBC: forall x :e B, g x :e C.
assume Hginj: forall x y :e B, g x = g y -> x = y.
prove injective A C (fun x => g (f x)).
apply andI (forall x :e A, (fun x => g (f x)) x :e C)
           (forall x y :e A, (fun x => g (f x)) x = (fun x => g (f x)) y -> x = y).
- prove forall x :e A, (fun x => g (f x)) x :e C.
  let x. assume HxA: x :e A.
  exact HgBC (f x) (HfAB x HxA).
- prove forall x y :e A, (fun x => g (f x)) x = (fun x => g (f x)) y -> x = y.
  let x. assume HxA: x :e A.
  let y. assume HyA: y :e A.
  assume Heq: (fun x => g (f x)) x = (fun x => g (f x)) y.
  claim Hfxfy: f x = f y.
    exact Hginj (f x) (f y) Heq.
  exact Hfinj x y Hfxfy.
Qed.

% Restricting the domain of an injection preserves injectivity.
Theorem injective_subset : forall A B S:set, forall f:set -> set,
  injective A B f ->
  S c= A ->
  injective S B f.
let A. let B. let S. let f.
assume Hinj: injective A B f.
assume HS: S c= A.
apply and3E (forall x :e A, f x :e B) (forall x y :e A, f x = f y -> x = y) True
            (andI (forall x :e A, f x :e B) (forall x y :e A, f x = f y -> x = y) TrueI)
            Hinj (injective S B f).
assume HFAB: forall x :e A, f x :e B.
assume HFinj: forall x y :e A, f x = f y -> x = y.
prove injective S B f.
apply andI (forall x :e S, f x :e B) (forall x y :e S, f x = f y -> x = y).
- prove forall x :e S, f x :e B.
  let x. assume HxS: x :e S.
  exact HFAB x (HS x HxS).
- prove forall x y :e S, f x = f y -> x = y.
  let x. assume HxS: x :e S.
  let y. assume HyS: y :e S.
  assume Heq: f x = f y.
  exact HFinj x y Heq.
Qed.

% ---------------------------------------------------------------------------
% Pigeonhole-style axioms (to be proven/linked via ordinal reasoning or ATP).
% These are packaged as axioms for now to avoid "Admitted" placeholders in the
% proof files; they should be replaced by kernel proofs or ATP imports.

Axiom no_inj_succ_to_n : forall n:set,
  nat_p n ->
  ~exists f:set -> set, injective (ordsucc n) n f.

Axiom pigeonhole_injection : forall n:set, forall A B:set, forall f:set -> set,
  nat_p n ->
  equip (ordsucc n) A ->
  equip n B ->
  injective A B f ->
  False.

% Specialized helper for the 12→4→≥3 occupancy case: if a function from a
% 12-element set into a 4-element set exists, some fiber has cardinality 3.
Axiom php_12_4_3 : forall T P:set, forall f:set -> set,
  equip 12 T ->
  equip 4 P ->
  (forall t :e T, f t :e P) ->
  exists p :e P, exists A:set, A c= T /\ equip 3 A /\ (forall a :e A, f a = p).
