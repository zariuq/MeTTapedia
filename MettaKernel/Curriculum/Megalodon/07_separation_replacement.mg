Theorem repl_image : forall F:set->set, forall x:set, F x :e {F z|z :e {x}}.
let F x.
exact (ReplI {x} F x (SingI x)).
Qed.

Theorem repl_elem : forall A:set, forall F:set->set, forall x:set, x :e A -> F x :e {F z|z :e A}.
let A F x.
assume H: x :e A.
exact (ReplI A F x H).
Qed.

Theorem sep_is_subq : forall X:set, forall P:set->prop, {x :e X|P x} c= X.
let X P.
exact (Sep_Subq X P).
Qed.

Theorem ordsucc_self : forall x:set, x :e ordsucc x.
let x.
exact (ordsuccI2 x).
Qed.

Theorem succ_succ_nat : forall n:set, nat_p n -> nat_p (ordsucc (ordsucc n)).
let n.
assume Hn: nat_p n.
exact (nat_ordsucc (ordsucc n) (nat_ordsucc n Hn)).
Qed.

Theorem zero_in_succ : forall n:set, nat_p n -> 0 :e ordsucc n.
let n.
assume Hn: nat_p n.
exact (nat_0_in_ordsucc n Hn).
Qed.

Theorem succ_nat_by_induction : forall n:set, nat_p n -> nat_p (ordsucc n).
claim Base: nat_p (ordsucc 0).
{ exact (nat_ordsucc 0 nat_0). }
claim Step: forall m:set, nat_p m -> nat_p (ordsucc m) -> nat_p (ordsucc (ordsucc m)).
{ let m. assume Hm: nat_p m. assume IH: nat_p (ordsucc m). exact (nat_ordsucc (ordsucc m) IH). }
exact (nat_ind (fun m:set => nat_p (ordsucc m)) Base Step).
Qed.
