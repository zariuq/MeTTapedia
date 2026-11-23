(** The tower of type universes inside the sets.

    A type is a set and typing is membership. The universe at the natural
    number n is an iterate of the operation UnivOf, which gives the least
    transitive ZF-closed set around a set. A function is its trace: the set
    of the pairs of an argument x and a member z of the value at x. The
    library writes a function fun x :e X => F x, applies it by writing the
    argument after it, and writes the function types Pi_ x :e X, Y x. The
    propositions are the members of 2.

    The rules of the tower are stated here as theorems about sets. Each
    theorem names the statement of the Lean development that it mirrors.

    Part 1  the tower
    Part 2  the rules of function types in a transitive ZF-closed set
    Part 3  propositions
    Part 4  two function types with different domains that are one set
    Part 5  no set of all sets, and the universe operation
    Part 6  chains of closed universes
    Part 7  the eleven laws of sets and of the universe operation **)

(** Part 1. The tower. **)

(** Mirrors universeSet over the natural numbers, with the natural numbers
    as the seed: the universe at the natural number n. **)
Definition universeAt : set -> set :=
  nat_primrec (UnivOf omega) (fun _ r => UnivOf r).

(** Mirrors lowerSets_universe_bot: the universe at the least level is the
    least closed universe around the natural numbers. **)
Theorem universeAt_0 : universeAt 0 = UnivOf omega.
exact (nat_primrec_0 (UnivOf omega) (fun _ r => UnivOf r)).
Qed.

(** Mirrors lowerSets_universe_succ: the universe at a successor level is
    the least closed universe around the universe at the level. **)
Theorem universeAt_S : forall n:set, nat_p n ->
  universeAt (ordsucc n) = UnivOf (universeAt n).
exact (nat_primrec_S (UnivOf omega) (fun _ r => UnivOf r)).
Qed.

(** Mirrors universeSet_closed, the part that the universe is transitive. **)
Theorem universeAt_TransSet : forall n:set, nat_p n -> TransSet (universeAt n).
apply nat_ind.
- prove TransSet (universeAt 0).
  rewrite universeAt_0.
  exact (UnivOf_TransSet omega).
- let n.
  assume Hn: nat_p n.
  assume _: TransSet (universeAt n).
  prove TransSet (universeAt (ordsucc n)).
  rewrite (universeAt_S n Hn).
  exact (UnivOf_TransSet (universeAt n)).
Qed.

(** Mirrors universeSet_closed, the three closure conditions. **)
Theorem universeAt_ZF_closed : forall n:set, nat_p n -> ZF_closed (universeAt n).
apply nat_ind.
- prove ZF_closed (universeAt 0).
  rewrite universeAt_0.
  exact (UnivOf_ZF_closed omega).
- let n.
  assume Hn: nat_p n.
  assume _: ZF_closed (universeAt n).
  prove ZF_closed (universeAt (ordsucc n)).
  rewrite (universeAt_S n Hn).
  exact (UnivOf_ZF_closed (universeAt n)).
Qed.

(** Mirrors ClosedChain.mem_succ: a universe is a member of the next one. **)
Theorem universeAt_In_S : forall n:set, nat_p n ->
  universeAt n :e universeAt (ordsucc n).
let n.
assume Hn: nat_p n.
rewrite (universeAt_S n Hn).
exact (UnivOf_In (universeAt n)).
Qed.

(** Mirrors universeSet_mono at a level and its successor. **)
Theorem universeAt_Subq_S : forall n:set, nat_p n ->
  universeAt n c= universeAt (ordsucc n).
let n.
assume Hn: nat_p n.
exact (universeAt_TransSet (ordsucc n) (nat_ordsucc n Hn) (universeAt n)
        (universeAt_In_S n Hn)).
Qed.

(** Mirrors universeSet_mem_of_lt: an earlier universe is a member of every
    later one. **)
Theorem universeAt_In : forall n:set, nat_p n ->
  forall m :e n, universeAt m :e universeAt n.
apply nat_ind.
- prove forall m :e 0, universeAt m :e universeAt 0.
  let m.
  assume Hm: m :e 0.
  prove False.
  exact (EmptyE m Hm).
- let n.
  assume Hn: nat_p n.
  assume IHn: forall m :e n, universeAt m :e universeAt n.
  prove forall m :e ordsucc n, universeAt m :e universeAt (ordsucc n).
  let m.
  assume Hm: m :e ordsucc n.
  apply (ordsuccE n m Hm).
  + assume H1: m :e n.
    exact (universeAt_Subq_S n Hn (universeAt m) (IHn m H1)).
  + assume H1: m = n.
    rewrite H1.
    exact (universeAt_In_S n Hn).
Qed.

(** Mirrors universeSet_mono below a level: an earlier universe is a subset
    of every later one. **)
Theorem universeAt_Subq : forall n:set, nat_p n ->
  forall m :e n, universeAt m c= universeAt n.
let n.
assume Hn: nat_p n.
let m.
assume Hm: m :e n.
exact (universeAt_TransSet n Hn (universeAt m) (universeAt_In n Hn m Hm)).
Qed.

(** Mirrors universeSet_mono: a level at or below a level gives a subset. **)
Theorem universeAt_Subq_le : forall n:set, nat_p n ->
  forall m :e ordsucc n, universeAt m c= universeAt n.
let n.
assume Hn: nat_p n.
let m.
assume Hm: m :e ordsucc n.
apply (ordsuccE n m Hm).
- assume H1: m :e n.
  exact (universeAt_Subq n Hn m H1).
- assume H1: m = n.
  rewrite H1.
  exact (Subq_ref (universeAt n)).
Qed.

(** Mirrors seed_mem_universeSet: the natural numbers are a member of every
    universe of the tower. **)
Theorem universeAt_omega : forall n:set, nat_p n -> omega :e universeAt n.
apply nat_ind.
- prove omega :e universeAt 0.
  rewrite universeAt_0.
  exact (UnivOf_In omega).
- let n.
  assume Hn: nat_p n.
  assume IHn: omega :e universeAt n.
  exact (universeAt_Subq_S n Hn omega IHn).
Qed.

(** Part 2. The rules of function types in a transitive ZF-closed set. Such
    a set is what the Lean development calls a closed universe (Closed). **)

(** Mirrors Closed.empty_mem. **)
Theorem closed_Empty : forall U:set, TransSet U -> ZF_closed U ->
  forall A :e U, 0 :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let A.
assume HA: A :e U.
exact (HT (Power A) (ZF_Power_closed U HC A HA) 0 (Empty_In_Power A)).
Qed.

(** Mirrors Closed.subset_mem. **)
Theorem closed_Subq : forall U:set, TransSet U -> ZF_closed U ->
  forall A :e U, forall B:set, B c= A -> B :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let A.
assume HA: A :e U.
let B.
assume HB: B c= A.
exact (HT (Power A) (ZF_Power_closed U HC A HA) B (PowerI A B HB)).
Qed.

(** Mirrors Closed.separation_mem. **)
Theorem closed_Sep : forall U:set, TransSet U -> ZF_closed U ->
  forall A :e U, forall P:set->prop, {x :e A|P x} :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let A.
assume HA: A :e U.
let P.
exact (closed_Subq U HT HC A HA {x :e A|P x} (Sep_Subq A P)).
Qed.

(** Mirrors Closed.familyUnion_mem. **)
Theorem closed_famunion : forall U:set, ZF_closed U ->
  forall A :e U, forall B:set->set, (forall x :e A, B x :e U) ->
  (\/_ x :e A, B x) :e U.
let U.
assume HC: ZF_closed U.
let A.
assume HA: A :e U.
let B.
assume HB: forall x :e A, B x :e U.
claim L1: (\/_ x :e A, B x) = Union {B x|x :e A}.
{ apply set_ext.
  - let y.
    assume Hy: y :e \/_ x :e A, B x.
    apply (famunionE_impred A B y Hy).
    let x.
    assume Hx: x :e A.
    assume Hyx: y :e B x.
    exact (UnionI {B x|x :e A} y (B x) Hyx (ReplI A B x Hx)).
  - let y.
    assume Hy: y :e Union {B x|x :e A}.
    apply (UnionE_impred {B x|x :e A} y Hy).
    let Y.
    assume HyY: y :e Y.
    assume HY: Y :e {B x|x :e A}.
    apply (ReplE_impred A B Y HY).
    let x.
    assume Hx: x :e A.
    assume HYx: Y = B x.
    apply (famunionI A B x y Hx).
    prove y :e B x.
    rewrite <- HYx.
    exact HyY.
}
rewrite L1.
exact (ZF_Union_closed U HC {B x|x :e A} (ZF_Repl_closed U HC A HA B HB)).
Qed.

(** The ordered pair of the library is x :+: y, built from two injections
    that are defined by recursion on membership. So the proof that they stay
    inside is by induction on membership. No Lean counterpart: the Lean pair
    is the Kuratowski pair, two unordered pairs. **)
Theorem closed_Inj1 : forall U:set, TransSet U -> ZF_closed U ->
  forall X:set, X :e U -> Inj1 X :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
apply In_ind.
let X.
assume IH: forall x :e X, x :e U -> Inj1 x :e U.
assume HX: X :e U.
prove Inj1 X :e U.
rewrite (Inj1_eq X).
prove {0} :\/: {Inj1 x|x :e X} :e U.
apply (ZF_binunion_closed U HC).
- prove {0} :e U.
  exact (ZF_Sing_closed U HC 0 (closed_Empty U HT HC X HX)).
- prove {Inj1 x|x :e X} :e U.
  apply (ZF_Repl_closed U HC X HX Inj1).
  let x.
  assume Hx: x :e X.
  exact (IH x Hx (HT X HX x Hx)).
Qed.

(** No Lean counterpart, as for closed_Inj1. **)
Theorem closed_Inj0 : forall U:set, TransSet U -> ZF_closed U ->
  forall X :e U, Inj0 X :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let X.
assume HX: X :e U.
prove {Inj1 x|x :e X} :e U.
apply (ZF_Repl_closed U HC X HX Inj1).
let x.
assume Hx: x :e X.
exact (closed_Inj1 U HT HC x (HT X HX x Hx)).
Qed.

(** Mirrors Closed.pair_mem. **)
Theorem closed_setsum : forall U:set, TransSet U -> ZF_closed U ->
  forall x y :e U, x :+: y :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let x.
assume Hx: x :e U.
let y.
assume Hy: y :e U.
prove {Inj0 z|z :e x} :\/: {Inj1 z|z :e y} :e U.
apply (ZF_binunion_closed U HC).
- prove {Inj0 z|z :e x} :e U.
  apply (ZF_Repl_closed U HC x Hx Inj0).
  let z.
  assume Hz: z :e x.
  exact (closed_Inj0 U HT HC z (HT x Hx z Hz)).
- prove {Inj1 z|z :e y} :e U.
  apply (ZF_Repl_closed U HC y Hy Inj1).
  let z.
  assume Hz: z :e y.
  exact (closed_Inj1 U HT HC z (HT y Hy z Hz)).
Qed.

(** Mirrors Closed.pair_mem, in the tuple notation. **)
Theorem closed_pair : forall U:set, TransSet U -> ZF_closed U ->
  forall x y :e U, (x,y) :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let x.
assume Hx: x :e U.
let y.
assume Hy: y :e U.
rewrite <- (tuple_pair x y).
exact (closed_setsum U HT HC x Hx y Hy).
Qed.

(** Formation of the types of dependent pairs. Mirrors Closed.sigmaSet_mem. **)
Theorem closed_Sigma : forall U:set, TransSet U -> ZF_closed U ->
  forall A :e U, forall B:set->set, (forall x :e A, B x :e U) ->
  (Sigma_ x :e A, B x) :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let A.
assume HA: A :e U.
let B.
assume HB: forall x :e A, B x :e U.
prove (\/_ x :e A, {x :+: y|y :e B x}) :e U.
apply (closed_famunion U HC A HA (fun x => {x :+: y|y :e B x})).
let x.
assume Hx: x :e A.
prove {x :+: y|y :e B x} :e U.
apply (ZF_Repl_closed U HC (B x) (HB x Hx) (fun y => x :+: y)).
let y.
assume Hy: y :e B x.
exact (closed_setsum U HT HC x (HT A HA x Hx) y (HT (B x) (HB x Hx) y Hy)).
Qed.

(** Formation of function types. Mirrors Closed.tracePiSet_mem. **)
Theorem closed_Pi : forall U:set, TransSet U -> ZF_closed U ->
  forall A :e U, forall B:set->set, (forall x :e A, B x :e U) ->
  (Pi_ x :e A, B x) :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let A.
assume HA: A :e U.
let B.
assume HB: forall x :e A, B x :e U.
prove {f :e Power (Sigma_ x :e A, Union (B x))|forall x :e A, f x :e B x} :e U.
apply (closed_Sep U HT HC (Power (Sigma_ x :e A, Union (B x)))).
prove Power (Sigma_ x :e A, Union (B x)) :e U.
apply (ZF_Power_closed U HC).
prove (Sigma_ x :e A, Union (B x)) :e U.
apply (closed_Sigma U HT HC A HA (fun x => Union (B x))).
let x.
assume Hx: x :e A.
exact (ZF_Union_closed U HC (B x) (HB x Hx)).
Qed.

(** Introduction. Mirrors traceLam_graph_mem. The library has it as lam_Pi. **)
Theorem function_intro : forall A:set, forall B:set->set, forall F:set->set,
  (forall x :e A, F x :e B x) -> (fun x :e A => F x) :e (Pi_ x :e A, B x).
exact lam_Pi.
Qed.

(** Elimination. Mirrors traceApp_mem_fibre. The library has it as ap_Pi. **)
Theorem function_elim : forall A:set, forall B:set->set, forall f x:set,
  f :e (Pi_ x :e A, B x) -> x :e A -> f x :e B x.
exact ap_Pi.
Qed.

(** Computation. Mirrors traceApp_graph_beta. The library has it as beta. **)
Theorem function_beta : forall A:set, forall F:set->set, forall x:set,
  x :e A -> (fun x :e A => F x) x = F x.
exact beta.
Qed.

(** Outside its domain a function gives the empty set. Mirrors
    traceApp_graph_outside. **)
Theorem function_outside : forall A:set, forall F:set->set, forall x:set,
  x /:e A -> (fun x :e A => F x) x = 0.
let A F x.
assume Hx: x /:e A.
apply Empty_eq.
let w.
assume Hw: w :e (fun x :e A => F x) x.
apply Hx.
prove x :e A.
claim L1: x :+: w :e (fun x :e A => F x).
{ exact (apE (fun x :e A => F x) x w Hw). }
claim L2: proj0 (x :+: w) :e A.
{ exact (proj0_Sigma A F (x :+: w) L1). }
rewrite <- (proj0_pair_eq x w).
exact L2.
Qed.

(** Mirrors traceApp_eq_empty_of_not_mem: every member of a function type
    gives the empty set outside the domain of the type. **)
Theorem function_outside_member : forall A:set, forall B:set->set, forall f x:set,
  f :e (Pi_ x :e A, B x) -> x /:e A -> f x = 0.
let A B f x.
assume Hf: f :e Pi_ x :e A, B x.
assume Hx: x /:e A.
apply Empty_eq.
let w.
assume Hw: w :e f x.
apply Hx.
prove x :e A.
claim L1: x :+: w :e f.
{ exact (apE f x w Hw). }
claim Lsub: f c= Sigma_ x :e A, Union (B x).
{ exact (PowerE (Sigma_ x :e A, Union (B x)) f
          (SepE1 (Power (Sigma_ x :e A, Union (B x)))
                 (fun f => forall x :e A, f x :e B x) f Hf)).
}
claim L2: proj0 (x :+: w) :e A.
{ exact (proj0_Sigma A (fun x => Union (B x)) (x :+: w) (Lsub (x :+: w) L1)). }
rewrite <- (proj0_pair_eq x w).
exact L2.
Qed.

(** Mirrors Closed.traceLam_mem: a function over a member, with values that
    are members, is a member. **)
Theorem closed_lam : forall U:set, TransSet U -> ZF_closed U ->
  forall A :e U, forall F:set->set, (forall x :e A, F x :e U) ->
  (fun x :e A => F x) :e U.
exact closed_Sigma.
Qed.

(** The left inverse of the two injections stays inside. No Lean
    counterpart, as for closed_Inj1. **)
Theorem closed_Unj : forall U:set, TransSet U -> ZF_closed U ->
  forall X:set, X :e U -> Unj X :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
apply In_ind.
let X.
assume IH: forall x :e X, x :e U -> Unj x :e U.
assume HX: X :e U.
prove Unj X :e U.
rewrite (Unj_eq X).
prove {Unj x|x :e X :\: {0}} :e U.
apply (ZF_Repl_closed U HC (X :\: {0})
        (closed_Subq U HT HC X HX (X :\: {0}) (setminus_Subq X {0})) Unj).
let x.
assume Hx: x :e X :\: {0}.
exact (IH x (setminusE1 X {0} x Hx) (HT X HX x (setminusE1 X {0} x Hx))).
Qed.

(** The values taken at the members that satisfy a condition are among the
    values taken at all members. No Lean counterpart. **)
Theorem ReplSep_Subq_Repl : forall X:set, forall P:set->prop, forall F:set->set,
  {F x|x :e X, P x} c= {F x|x :e X}.
let X P F y.
assume Hy: y :e {F x|x :e X, P x}.
apply (ReplSepE_impred X P F y Hy).
let x.
assume Hx: x :e X.
assume _: P x.
assume Hyx: y = F x.
rewrite Hyx.
exact (ReplI X F x Hx).
Qed.

(** The second projection stays inside. No Lean counterpart, as for
    closed_Inj1. **)
Theorem closed_proj1 : forall U:set, TransSet U -> ZF_closed U ->
  forall Z :e U, proj1 Z :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let Z.
assume HZ: Z :e U.
prove {Unj z|z :e Z, exists y:set, Inj1 y = z} :e U.
apply (closed_Subq U HT HC {Unj z|z :e Z}).
- prove {Unj z|z :e Z} :e U.
  apply (ZF_Repl_closed U HC Z HZ Unj).
  let z.
  assume Hz: z :e Z.
  exact (closed_Unj U HT HC z (HT Z HZ z Hz)).
- exact (ReplSep_Subq_Repl Z (fun z => exists y:set, Inj1 y = z) Unj).
Qed.

(** Mirrors Closed.traceApp_mem: a member applied to any set is a member. **)
Theorem closed_ap : forall U:set, TransSet U -> ZF_closed U ->
  forall f :e U, forall x:set, f x :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
let f.
assume Hf: f :e U.
let x.
prove {proj1 z|z :e f, exists y:set, z = x :+: y} :e U.
apply (closed_Subq U HT HC {proj1 z|z :e f}).
- prove {proj1 z|z :e f} :e U.
  apply (ZF_Repl_closed U HC f Hf proj1).
  let z.
  assume Hz: z :e f.
  exact (closed_proj1 U HT HC z (HT f Hf z Hz)).
- exact (ReplSep_Subq_Repl f (fun z => exists y:set, z = x :+: y) proj1).
Qed.

(** Mirrors empty_mem_universeSet. **)
Theorem universeAt_Empty : forall n:set, nat_p n -> 0 :e universeAt n.
let n.
assume Hn: nat_p n.
exact (closed_Empty (universeAt n) (universeAt_TransSet n Hn)
        (universeAt_ZF_closed n Hn) omega (universeAt_omega n Hn)).
Qed.

(** Mirrors pi_mem of chain_universeModel_of: a function type with domain at
    level m and fibres at level n lies at every level that bounds both, in
    particular at the larger of the two. **)
Theorem universeAt_Pi : forall k:set, nat_p k -> forall m n :e ordsucc k,
  forall A :e universeAt m, forall B:set->set,
  (forall x :e A, B x :e universeAt n) -> (Pi_ x :e A, B x) :e universeAt k.
let k.
assume Hk: nat_p k.
let m.
assume Hm: m :e ordsucc k.
let n.
assume Hn: n :e ordsucc k.
let A.
assume HA: A :e universeAt m.
let B.
assume HB: forall x :e A, B x :e universeAt n.
apply (closed_Pi (universeAt k) (universeAt_TransSet k Hk)
        (universeAt_ZF_closed k Hk) A (universeAt_Subq_le k Hk m Hm A HA) B).
let x.
assume Hx: x :e A.
exact (universeAt_Subq_le k Hk n Hn (B x) (HB x Hx)).
Qed.

(** Mirrors sigma_mem of chain_universeModel_of. **)
Theorem universeAt_Sigma : forall k:set, nat_p k -> forall m n :e ordsucc k,
  forall A :e universeAt m, forall B:set->set,
  (forall x :e A, B x :e universeAt n) -> (Sigma_ x :e A, B x) :e universeAt k.
let k.
assume Hk: nat_p k.
let m.
assume Hm: m :e ordsucc k.
let n.
assume Hn: n :e ordsucc k.
let A.
assume HA: A :e universeAt m.
let B.
assume HB: forall x :e A, B x :e universeAt n.
apply (closed_Sigma (universeAt k) (universeAt_TransSet k Hk)
        (universeAt_ZF_closed k Hk) A (universeAt_Subq_le k Hk m Hm A HA) B).
let x.
assume Hx: x :e A.
exact (universeAt_Subq_le k Hk n Hn (B x) (HB x Hx)).
Qed.

(** The larger of two natural numbers is their union. It is a natural
    number, and both numbers are at or below it. No Lean counterpart: there
    the larger of two levels comes with the order of the levels. **)
Theorem nat_binunion_bound : forall m n:set, nat_p m -> nat_p n ->
  nat_p (m :\/: n) /\ m :e ordsucc (m :\/: n) /\ n :e ordsucc (m :\/: n).
let m n.
assume Hm: nat_p m.
assume Hn: nat_p n.
claim L: forall a b:set, nat_p a -> nat_p b -> a c= b -> a :e ordsucc b.
{ let a b.
  assume Ha: nat_p a.
  assume Hb: nat_p b.
  assume Hab: a c= b.
  apply (ordinal_In_Or_Subq a b (nat_p_ordinal a Ha) (nat_p_ordinal b Hb)).
  - assume H1: a :e b.
    exact (ordsuccI1 b a H1).
  - assume H1: b c= a.
    claim E: a = b.
    { exact (set_ext a b Hab H1). }
    rewrite E.
    exact (ordsuccI2 b).
}
apply (ordinal_linear m n (nat_p_ordinal m Hm) (nat_p_ordinal n Hn)).
- assume H1: m c= n.
  claim E: m :\/: n = n.
  { apply set_ext.
    - exact (binunion_Subq_min m n n H1 (Subq_ref n)).
    - exact (binunion_Subq_2 m n).
  }
  rewrite E.
  apply and3I.
  + exact Hn.
  + exact (L m n Hm Hn H1).
  + exact (ordsuccI2 n).
- assume H1: n c= m.
  claim E: m :\/: n = m.
  { apply set_ext.
    - exact (binunion_Subq_min m n m (Subq_ref m) H1).
    - exact (binunion_Subq_1 m n).
  }
  rewrite E.
  apply and3I.
  + exact Hm.
  + exact (ordsuccI2 m).
  + exact (L n m Hn Hm H1).
Qed.

(** Mirrors pi_mem of chain_universeModel_of at the larger of the two
    levels, as the Lean rule states it. **)
Theorem universeAt_Pi_max : forall m n:set, nat_p m -> nat_p n ->
  forall A :e universeAt m, forall B:set->set,
  (forall x :e A, B x :e universeAt n) ->
  (Pi_ x :e A, B x) :e universeAt (m :\/: n).
let m n.
assume Hm: nat_p m.
assume Hn: nat_p n.
apply (nat_binunion_bound m n Hm Hn).
assume H12: nat_p (m :\/: n) /\ m :e ordsucc (m :\/: n).
assume H3: n :e ordsucc (m :\/: n).
apply H12.
assume H1: nat_p (m :\/: n).
assume H2: m :e ordsucc (m :\/: n).
exact (universeAt_Pi (m :\/: n) H1 m H2 n H3).
Qed.

(** Mirrors sigma_mem of chain_universeModel_of at the larger of the two
    levels. **)
Theorem universeAt_Sigma_max : forall m n:set, nat_p m -> nat_p n ->
  forall A :e universeAt m, forall B:set->set,
  (forall x :e A, B x :e universeAt n) ->
  (Sigma_ x :e A, B x) :e universeAt (m :\/: n).
let m n.
assume Hm: nat_p m.
assume Hn: nat_p n.
apply (nat_binunion_bound m n Hm Hn).
assume H12: nat_p (m :\/: n) /\ m :e ordsucc (m :\/: n).
assume H3: n :e ordsucc (m :\/: n).
apply H12.
assume H1: nat_p (m :\/: n).
assume H2: m :e ordsucc (m :\/: n).
exact (universeAt_Sigma (m :\/: n) H1 m H2 n H3).
Qed.

(** Part 3. Propositions are the members of 2. **)

(** The truth values are the subsets of the one-element set. The Lean
    development defines the truth values as that power set. **)
Theorem Power_1_eq_2 : Power 1 = 2.
apply set_ext.
- let X.
  assume HX: X :e Power 1.
  claim L1: X c= 1.
  { exact (PowerE 1 X HX). }
  apply (xm (0 :e X)).
  + assume H0: 0 :e X.
    claim L2: X = 1.
    { apply set_ext.
      - exact L1.
      - let y.
        assume Hy: y :e 1.
        claim Ly: y = 0.
        { exact (SingE 0 y (Subq_1_Sing0 y Hy)). }
        rewrite Ly.
        exact H0.
    }
    rewrite L2.
    exact In_1_2.
  + assume H0: 0 /:e X.
    claim L2: X = 0.
    { apply Empty_eq.
      let y.
      assume Hy: y :e X.
      apply H0.
      claim Ly: y = 0.
      { exact (SingE 0 y (Subq_1_Sing0 y (L1 y Hy))). }
      rewrite <- Ly.
      exact Hy.
    }
    rewrite L2.
    exact In_0_2.
- let X.
  assume HX: X :e 2.
  apply (cases_2 X HX (fun i:set => i :e Power 1)).
  + exact (Empty_In_Power 1).
  + exact (Self_In_Power 1).
Qed.

(** A truth value with a member is the truth value 1. No Lean counterpart:
    a step of the proofs below. **)
Theorem truth_value_inhabited_eq_1 : forall p :e 2, forall z :e p, p = 1.
let p.
assume Hp: p :e 2.
let z.
apply (cases_2 p Hp (fun i:set => z :e i -> i = 1)).
- assume H0: z :e 0.
  prove False.
  exact (EmptyE z H0).
- assume _: z :e 1.
  reflexivity.
Qed.

(** Mirrors truthCode_mem_truthValues: the truth value of a statement is a
    member of 2. **)
Theorem truth_value_In_2 : forall q:prop, {y :e 1|q} :e 2.
let q.
rewrite <- Power_1_eq_2.
exact (Sep_In_Power 1 (fun _ => q)).
Qed.

(** Mirrors mem_truthCode. **)
Theorem truth_value_mem_iff : forall q:prop, forall x:set,
  x :e {y :e 1|q} <-> x = 0 /\ q.
let q x.
apply iffI.
- assume H: x :e {y :e 1|q}.
  apply andI.
  + exact (SingE 0 x (Subq_1_Sing0 x (SepE1 1 (fun _ => q) x H))).
  + exact (SepE2 1 (fun _ => q) x H).
- assume H: x = 0 /\ q.
  apply H.
  assume H1: x = 0.
  assume H2: q.
  rewrite H1.
  exact (SepI 1 (fun _ => q) 0 In_0_1 H2).
Qed.

(** A statement that holds has the truth value 1. No Lean counterpart: a
    step of the proofs below. **)
Theorem truth_value_eq_1 : forall q:prop, q -> {y :e 1|q} = 1.
let q.
assume Hq: q.
exact (truth_value_inhabited_eq_1 {y :e 1|q} (truth_value_In_2 q) 0
        (SepI 1 (fun _ => q) 0 In_0_1 Hq)).
Qed.

(** Mirrors tracePiSet_mem_truthValues: a quantification over a set of any
    size is a proposition. **)
Theorem Pi_In_2 : forall A:set, forall P:set->set,
  (forall x :e A, P x :e 2) -> (Pi_ x :e A, P x) :e 2.
let A P.
assume H: forall x :e A, P x :e 2.
rewrite <- Power_1_eq_2.
apply PowerI.
let f.
assume Hf: f :e Pi_ x :e A, P x.
prove f :e 1.
claim Lf0: f = 0.
{ apply Empty_eq.
  let z.
  assume Hz: z :e f.
  claim Lsub: f c= Sigma_ x :e A, Union (P x).
  { exact (PowerE (Sigma_ x :e A, Union (P x)) f
            (SepE1 (Power (Sigma_ x :e A, Union (P x)))
                   (fun f => forall x :e A, f x :e P x) f Hf)).
  }
  apply (Sigma_eta_proj0_proj1 A (fun x => Union (P x)) z (Lsub z Hz)).
  assume H12: proj0 z :+: proj1 z = z /\ proj0 z :e A.
  assume _: proj1 z :e Union (P (proj0 z)).
  apply H12.
  assume HE: proj0 z :+: proj1 z = z.
  assume HA: proj0 z :e A.
  claim L1: proj1 z :e f (proj0 z).
  { apply apI.
    prove proj0 z :+: proj1 z :e f.
    rewrite HE.
    exact Hz.
  }
  claim L2: f (proj0 z) :e P (proj0 z).
  { exact (ap_Pi A P f (proj0 z) Hf HA). }
  claim L3: P (proj0 z) c= 1.
  { apply PowerE.
    rewrite Power_1_eq_2.
    exact (H (proj0 z) HA).
  }
  claim L4: f (proj0 z) = 0.
  { exact (SingE 0 (f (proj0 z))
            (Subq_1_Sing0 (f (proj0 z)) (L3 (f (proj0 z)) L2))).
  }
  apply (EmptyE (proj1 z)).
  rewrite <- L4.
  exact L1.
}
rewrite Lf0.
exact In_0_1.
Qed.

(** Mirrors tracePiSet_eq_unit_iff: the quantification is true exactly when
    every instance is true. **)
Theorem Pi_eq_1_iff : forall A:set, forall P:set->set,
  (forall x :e A, P x :e 2) ->
  ((Pi_ x :e A, P x) = 1 <-> forall x :e A, P x = 1).
let A P.
assume H: forall x :e A, P x :e 2.
apply iffI.
- assume H1: (Pi_ x :e A, P x) = 1.
  let x.
  assume Hx: x :e A.
  claim L0: 0 :e Pi_ x :e A, P x.
  { rewrite H1. exact In_0_1. }
  claim L1: 0 x :e P x.
  { exact (ap_Pi A P 0 x L0 Hx). }
  exact (truth_value_inhabited_eq_1 (P x) (H x Hx) (0 x) L1).
- assume H1: forall x :e A, P x = 1.
  claim L0: (fun x :e A => 0) :e Pi_ x :e A, P x.
  { apply (lam_Pi A P (fun _ => 0)).
    let x.
    assume Hx: x :e A.
    prove 0 :e P x.
    rewrite (H1 x Hx).
    exact In_0_1.
  }
  exact (truth_value_inhabited_eq_1 (Pi_ x :e A, P x) (Pi_In_2 A P H)
          (fun x :e A => 0) L0).
Qed.

(** Mirrors traceLam_graph_empty: the function with every value empty is the
    empty set, over any domain. **)
Theorem lam_Empty : forall A:set, (fun x :e A => 0) = 0.
let A.
apply Empty_eq.
let z.
assume Hz: z :e (fun x :e A => 0).
apply (lamE A (fun _ => 0) z Hz).
let x.
assume Hx: x :e A /\ exists y :e 0, z = x :+: y.
apply Hx.
assume _: x :e A.
assume H2: exists y :e 0, z = x :+: y.
apply H2.
let y.
assume Hy: y :e 0 /\ z = x :+: y.
apply Hy.
assume Hy0: y :e 0.
assume _: z = x :+: y.
exact (EmptyE y Hy0).
Qed.

(** Mirrors traceApp_empty: the empty set applied to any set is empty. **)
Theorem ap_Empty : forall x:set, 0 x = 0.
let x.
apply Empty_eq.
let w.
assume Hw: w :e 0 x.
exact (EmptyE (x :+: w) (apE 0 x w Hw)).
Qed.

(** Mirrors empty_mem_tracePiSet: the empty set is a function into every
    family of sets that have the empty set as a member. **)
Theorem Empty_In_Pi : forall A:set, forall B:set->set,
  (forall x :e A, 0 :e B x) -> 0 :e (Pi_ x :e A, B x).
let A B.
assume H: forall x :e A, 0 :e B x.
rewrite <- (lam_Empty A).
exact (lam_Pi A B (fun _ => 0) H).
Qed.

(** Mirrors tracePiSet_eq_truth: a quantification over a set is the truth
    value of the statement that every instance has the member 0. **)
Theorem Pi_eq_truth : forall A:set, forall P:set->set,
  (forall x :e A, P x :e 2) ->
  (Pi_ x :e A, P x) = {y :e 1|forall x :e A, 0 :e P x}.
let A P.
assume H: forall x :e A, P x :e 2.
claim L2: (Pi_ x :e A, P x) :e 2.
{ exact (Pi_In_2 A P H). }
claim L3: (Pi_ x :e A, P x) c= 1.
{ apply PowerE.
  rewrite Power_1_eq_2.
  exact L2.
}
apply set_ext.
- let f.
  assume Hf: f :e Pi_ x :e A, P x.
  claim Lf1: f :e 1.
  { exact (L3 f Hf). }
  claim Lf0: f = 0.
  { exact (SingE 0 f (Subq_1_Sing0 f Lf1)). }
  apply SepI.
  + exact Lf1.
  + prove forall x :e A, 0 :e P x.
    let x.
    assume Hx: x :e A.
    claim L4: f x :e P x.
    { exact (ap_Pi A P f x Hf Hx). }
    claim L5: f x = 0.
    { rewrite Lf0. exact (ap_Empty x). }
    rewrite <- L5.
    exact L4.
- let y.
  assume Hy: y :e {y :e 1|forall x :e A, 0 :e P x}.
  claim L6: 0 :e (Pi_ x :e A, P x).
  { exact (Empty_In_Pi A P (SepE2 1 (fun _ => forall x :e A, 0 :e P x) y Hy)). }
  claim L7: (Pi_ x :e A, P x) = 1.
  { exact (truth_value_inhabited_eq_1 (Pi_ x :e A, P x) L2 0 L6). }
  rewrite L7.
  exact (SepE1 1 (fun _ => forall x :e A, 0 :e P x) y Hy).
Qed.

(** Mirrors tracePiSet_truthCode: the function type of a family of truth
    values of statements is the truth value of the universal statement. **)
Theorem Pi_truth_value : forall A:set, forall Q:set->prop,
  (Pi_ x :e A, {y :e 1|Q x}) = {y :e 1|forall x :e A, Q x}.
let A Q.
claim L2: (Pi_ x :e A, {y :e 1|Q x}) :e 2.
{ apply (Pi_In_2 A (fun x => {y :e 1|Q x})).
  let x.
  assume _: x :e A.
  exact (truth_value_In_2 (Q x)).
}
apply set_ext.
- let f.
  assume Hf: f :e Pi_ x :e A, {y :e 1|Q x}.
  prove f :e {y :e 1|forall x :e A, Q x}.
  apply SepI.
  + prove f :e 1.
    claim L3: (Pi_ x :e A, {y :e 1|Q x}) c= 1.
    { apply PowerE.
      rewrite Power_1_eq_2.
      exact L2.
    }
    exact (L3 f Hf).
  + prove forall x :e A, Q x.
    let x.
    assume Hx: x :e A.
    exact (SepE2 1 (fun _ => Q x) (f x)
            (ap_Pi A (fun x => {y :e 1|Q x}) f x Hf Hx)).
- let y.
  assume Hy: y :e {y :e 1|forall x :e A, Q x}.
  claim LQ: forall x :e A, Q x.
  { exact (SepE2 1 (fun _ => forall x :e A, Q x) y Hy). }
  claim L0: (fun x :e A => 0) :e Pi_ x :e A, {y :e 1|Q x}.
  { apply (lam_Pi A (fun x => {y :e 1|Q x}) (fun _ => 0)).
    let x.
    assume Hx: x :e A.
    exact (SepI 1 (fun _ => Q x) 0 In_0_1 (LQ x Hx)).
  }
  claim L4: (Pi_ x :e A, {y :e 1|Q x}) = 1.
  { exact (truth_value_inhabited_eq_1 (Pi_ x :e A, {y :e 1|Q x}) L2
            (fun x :e A => 0) L0).
  }
  rewrite L4.
  exact (SepE1 1 (fun _ => forall x :e A, Q x) y Hy).
Qed.

(** The set of the truth values and its two members are members of every
    ZF-closed set that has the empty set as a member. The general form of
    omega_mem_universeSet. **)
Theorem closed_2 : forall U:set, ZF_closed U -> 0 :e U ->
  2 :e U /\ 0 :e U /\ 1 :e U.
let U.
assume HC: ZF_closed U.
assume H0: 0 :e U.
claim L1: 1 :e U.
{ exact (ZF_ordsucc_closed U HC 0 H0). }
claim L2: 2 :e U.
{ exact (ZF_ordsucc_closed U HC 1 L1). }
apply and3I.
- exact L2.
- exact H0.
- exact L1.
Qed.

(** The truth value of every statement is a member of a transitive ZF-closed
    set that has the empty set. The general form of
    ClosedChain.truthCode_mem. **)
Theorem closed_truth_value : forall U:set, TransSet U -> ZF_closed U ->
  0 :e U -> forall q:prop, {y :e 1|q} :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
assume H0: 0 :e U.
let q.
claim L2: 2 :e U.
{ exact (ZF_ordsucc_closed U HC 1 (ZF_ordsucc_closed U HC 0 H0)). }
exact (HT 2 L2 {y :e 1|q} (truth_value_In_2 q)).
Qed.

(** A quantification over a set of any size is a member of every transitive
    ZF-closed set that has the empty set. The set quantified over need not
    be a member. The general form of tower_level_truth_impredicative. **)
Theorem closed_Pi_prop : forall U:set, TransSet U -> ZF_closed U -> 0 :e U ->
  forall A:set, forall P:set->set, (forall x :e A, P x :e 2) ->
  (Pi_ x :e A, P x) :e U.
let U.
assume HT: TransSet U.
assume HC: ZF_closed U.
assume H0: 0 :e U.
let A P.
assume H: forall x :e A, P x :e 2.
claim L2: 2 :e U.
{ exact (ZF_ordsucc_closed U HC 1 (ZF_ordsucc_closed U HC 0 H0)). }
exact (HT 2 L2 (Pi_ x :e A, P x) (Pi_In_2 A P H)).
Qed.

(** Mirrors omega_mem_universeSet: the truth values lie in every universe of
    the tower. **)
Theorem universeAt_2 : forall n:set, nat_p n -> 2 :e universeAt n.
let n.
assume Hn: nat_p n.
exact (ZF_ordsucc_closed (universeAt n) (universeAt_ZF_closed n Hn) 1
        (ZF_ordsucc_closed (universeAt n) (universeAt_ZF_closed n Hn) 0
          (universeAt_Empty n Hn))).
Qed.

(** Mirrors identity_mem of chain_universeModel_of, at the tower: the truth
    value of every statement, an equation between two sets included, lies in
    every universe of the tower. **)
Theorem universeAt_truth_value : forall n:set, nat_p n ->
  forall q:prop, {y :e 1|q} :e universeAt n.
let n.
assume Hn: nat_p n.
exact (closed_truth_value (universeAt n) (universeAt_TransSet n Hn)
        (universeAt_ZF_closed n Hn) (universeAt_Empty n Hn)).
Qed.

(** Mirrors tower_level_truth_impredicative: a quantification over a set of
    any size, a universe of the tower included, lies in every universe of
    the tower, the least one included. **)
Theorem universeAt_Pi_prop : forall n:set, nat_p n ->
  forall A:set, forall P:set->set, (forall x :e A, P x :e 2) ->
  (Pi_ x :e A, P x) :e universeAt n.
let n.
assume Hn: nat_p n.
exact (closed_Pi_prop (universeAt n) (universeAt_TransSet n Hn)
        (universeAt_ZF_closed n Hn) (universeAt_Empty n Hn)).
Qed.

(** A statement about all sets is a proposition. Here P is any operation on
    all sets, in particular a predicate with values in 2, and the statement
    is that every P x is true. It is the truth value of Pi_eq_truth with
    the quantifier over all sets in place of the quantifier over a set. No
    Lean counterpart: the Lean rules do not type this quantification in the
    least universe. **)
Theorem all_sets_statement_In_2 : forall P:set->set,
  {y :e 1|forall x:set, 0 :e P x} :e 2.
let P.
exact (truth_value_In_2 (forall x:set, 0 :e P x)).
Qed.

(** The same statement lies in every universe of the tower, the least one
    included. No Lean counterpart. **)
Theorem all_sets_statement_In_universeAt : forall P:set->set,
  forall n:set, nat_p n -> {y :e 1|forall x:set, 0 :e P x} :e universeAt n.
let P n.
assume Hn: nat_p n.
exact (universeAt_truth_value n Hn (forall x:set, 0 :e P x)).
Qed.

(** For a predicate with values in 2, the statement about all sets is true
    exactly when every instance is true. No Lean counterpart. **)
Theorem all_sets_statement_eq_1_iff : forall P:set->set,
  (forall x:set, P x :e 2) ->
  ({y :e 1|forall x:set, 0 :e P x} = 1 <-> forall x:set, P x = 1).
let P.
assume H: forall x:set, P x :e 2.
apply iffI.
- assume H1: {y :e 1|forall x:set, 0 :e P x} = 1.
  claim L0: 0 :e {y :e 1|forall x:set, 0 :e P x}.
  { rewrite H1. exact In_0_1. }
  claim L1: forall x:set, 0 :e P x.
  { exact (SepE2 1 (fun _ => forall x:set, 0 :e P x) 0 L0). }
  let x.
  exact (truth_value_inhabited_eq_1 (P x) (H x) 0 (L1 x)).
- assume H1: forall x:set, P x = 1.
  apply truth_value_eq_1.
  let x.
  prove 0 :e P x.
  rewrite (H1 x).
  exact In_0_1.
Qed.

(** The statement about all sets is the common part of the quantifications
    over every set: its members are the sets that are members of the
    function type over every set. There is no function type over all sets,
    since there is no set of all sets. No Lean counterpart. **)
Theorem all_sets_statement_iff_every_Pi : forall P:set->set, forall y:set,
  y :e {y :e 1|forall x:set, 0 :e P x} <-> forall A:set, y :e Pi_ x :e A, P x.
let P y.
apply iffI.
- assume Hy: y :e {y :e 1|forall x:set, 0 :e P x}.
  let A.
  claim Ly0: y = 0.
  { exact (SingE 0 y (Subq_1_Sing0 y
            (SepE1 1 (fun _ => forall x:set, 0 :e P x) y Hy))).
  }
  claim LQ: forall x:set, 0 :e P x.
  { exact (SepE2 1 (fun _ => forall x:set, 0 :e P x) y Hy). }
  rewrite Ly0.
  prove 0 :e Pi_ x :e A, P x.
  exact (Empty_In_Pi A P (fun x _ => LQ x)).
- assume Hy: forall A:set, y :e Pi_ x :e A, P x.
  claim L1: (Pi_ x :e 0, P x) :e 2.
  { apply (Pi_In_2 0 P).
    let x.
    assume Hx: x :e 0.
    prove False.
    exact (EmptyE x Hx).
  }
  claim L2: (Pi_ x :e 0, P x) c= 1.
  { apply PowerE.
    rewrite Power_1_eq_2.
    exact L1.
  }
  claim Ly1: y :e 1.
  { exact (L2 y (Hy 0)). }
  claim Ly0: y = 0.
  { exact (SingE 0 y (Subq_1_Sing0 y Ly1)). }
  apply SepI.
  + exact Ly1.
  + prove forall x:set, 0 :e P x.
    let x.
    claim L3: y x :e P x.
    { exact (ap_Pi {x} P y x (Hy {x}) (SingI x)). }
    claim L4: y x = 0.
    { rewrite Ly0. exact (ap_Empty x). }
    rewrite <- L4.
    exact L3.
Qed.

(** Mirrors not_mem_tracePiSet_const (Cantor): a transitive set does not
    have as a member the functions from itself into a set with two different
    members. **)
Theorem Pi_const_not_In : forall U B b0 b1:set, TransSet U ->
  b0 :e B -> b1 :e B -> b0 <> b1 -> (Pi_ x :e U, B) /:e U.
let U B b0 b1.
assume HT: TransSet U.
assume H0: b0 :e B.
assume H1: b1 :e B.
assume Hne: b0 <> b1.
assume HPi: (Pi_ x :e U, B) :e U.
set g : set -> set := fun x => if x x = b0 then b1 else b0.
claim Lg: forall x :e U, g x :e B.
{ let x.
  assume _: x :e U.
  apply (xm (x x = b0)).
  - assume H: x x = b0.
    prove (if x x = b0 then b1 else b0) :e B.
    rewrite (If_i_1 (x x = b0) b1 b0 H).
    exact H1.
  - assume H: x x <> b0.
    prove (if x x = b0 then b1 else b0) :e B.
    rewrite (If_i_0 (x x = b0) b1 b0 H).
    exact H0.
}
set d : set := fun x :e U => g x.
claim Ld: d :e Pi_ x :e U, B.
{ exact (lam_Pi U (fun _ => B) g Lg). }
claim LdU: d :e U.
{ exact (HT (Pi_ x :e U, B) HPi d Ld). }
claim Ldd: d d = g d.
{ exact (beta U g d LdU). }
apply (xm (d d = b0)).
- assume H: d d = b0.
  claim L2: g d = b1.
  { exact (If_i_1 (d d = b0) b1 b0 H). }
  apply Hne.
  prove b0 = b1.
  rewrite <- H.
  rewrite Ldd.
  exact L2.
- assume H: d d <> b0.
  claim L2: g d = b0.
  { exact (If_i_0 (d d = b0) b1 b0 H). }
  apply H.
  prove d d = b0.
  rewrite Ldd.
  exact L2.
Qed.

(** Mirrors tower_level_predicative: the functions from a universe of the
    tower into the two truth values are not a member of that universe. They
    are a member of the next one. **)
Theorem universeAt_Pi_2 : forall n:set, nat_p n ->
  (Pi_ x :e universeAt n, 2) /:e universeAt n
  /\ (Pi_ x :e universeAt n, 2) :e universeAt (ordsucc n).
let n.
assume Hn: nat_p n.
apply andI.
- exact (Pi_const_not_In (universeAt n) 2 0 1 (universeAt_TransSet n Hn)
          In_0_2 In_1_2 neq_0_1).
- apply (universeAt_Pi (ordsucc n) (nat_ordsucc n Hn)
          (ordsucc n) (ordsuccI2 (ordsucc n))
          (ordsucc n) (ordsuccI2 (ordsucc n))
          (universeAt n) (universeAt_In_S n Hn) (fun _ => 2)).
  let x.
  assume _: x :e universeAt n.
  exact (universeAt_2 (ordsucc n) (nat_ordsucc n Hn)).
Qed.

(** Part 4. Two function types with different domains are one set. **)

(** Mirrors functions_into_unit: over any set, the functions into the
    one-element set are the one-element set. **)
Theorem functions_into_unit : forall A:set, (Pi_ x :e A, 1) = 1.
let A.
apply (iffER ((Pi_ x :e A, 1) = 1) (forall x :e A, 1 = 1)
        (Pi_eq_1_iff A (fun _ => 1) (fun x _ => In_1_2))).
let x.
assume _: x :e A.
reflexivity.
Qed.

(** Mirrors domains_valid: the functions from 1 to 1 and the functions from
    2 to 1 are one set. **)
Theorem two_domains_one_function_type : (Pi_ x :e 1, 1) = (Pi_ x :e 2, 1).
rewrite (functions_into_unit 1).
rewrite (functions_into_unit 2).
reflexivity.
Qed.

(** The two domains are different sets. Mirrors the last step of
    not_formerFacts. **)
Theorem two_domains_differ : 1 <> 2.
assume H: 1 = 2.
claim L: forall X:set, X = 2 -> 1 :e X.
{ let X.
  assume HX: X = 2.
  rewrite HX.
  exact In_1_2.
}
exact (In_irref 1 (L 1 H)).
Qed.

(** Mirrors identity_fromTwo, read in the sets: the identity on 1 is a
    member of the functions from 2 to 1. **)
Theorem identity_on_1_In_from_2 : (fun x :e 1 => x) :e (Pi_ x :e 2, 1).
rewrite <- two_domains_one_function_type.
apply (lam_Pi 1 (fun _ => 1) (fun x => x)).
let x.
assume Hx: x :e 1.
exact Hx.
Qed.

(** Mirrors redex_value: the identity on 1 applied to the member 1 of 2 is
    the empty set, since 1 is outside the domain 1. **)
Theorem identity_on_1_at_1 : (fun x :e 1 => x) 1 = 0.
exact (function_outside 1 (fun x => x) 1 (In_irref 1)).
Qed.

(** Mirrors distinct_domains. **)
Theorem value_and_argument_differ : 0 <> 1.
exact neq_0_1.
Qed.

(** Mirrors redex_value_ne: the application is not its argument, so the
    computation rule does not hold outside the domain. **)
Theorem identity_on_1_at_1_neq : (fun x :e 1 => x) 1 <> 1.
rewrite identity_on_1_at_1.
exact neq_0_1.
Qed.

(** Mirrors point_not_one: the argument is a member of 2 and not of 1, while
    the application is a member of 1, as the elimination rule says. **)
Theorem argument_In_2_not_In_1 : 1 :e 2 /\ 1 /:e 1 /\ (fun x :e 1 => x) 1 :e 1.
apply and3I.
- exact In_1_2.
- exact (In_irref 1).
- exact (ap_Pi 2 (fun _ => 1) (fun x :e 1 => x) 1 identity_on_1_In_from_2 In_1_2).
Qed.

(** Mirrors value_not_kept, read in the sets: the four facts together. **)
Theorem two_domains_counterexample :
  (Pi_ x :e 1, 1) = (Pi_ x :e 2, 1)
  /\ 1 <> 2
  /\ (fun x :e 1 => x) 1 = 0
  /\ 0 <> 1.
apply and4I.
- exact two_domains_one_function_type.
- exact two_domains_differ.
- exact identity_on_1_at_1.
- exact neq_0_1.
Qed.

(** Mirrors distinct_domains_same_trace: one function over two domains. **)
Theorem two_domains_one_function : (fun x :e 0 => 0) = (fun x :e 1 => 0).
rewrite (lam_Empty 0).
rewrite (lam_Empty 1).
reflexivity.
Qed.

(** Mirrors distinct_domains_distinct_graphs: the sets of the pairs of an
    argument and the whole value there do tell the two domains apart. **)
Theorem two_domains_two_graphs : {x :+: 0|x :e 0} <> {x :+: 0|x :e 1}.
assume H: {x :+: 0|x :e 0} = {x :+: 0|x :e 1}.
claim L1: 0 :+: 0 :e {x :+: 0|x :e 1}.
{ exact (ReplI 1 (fun x => x :+: 0) 0 In_0_1). }
claim L2: 0 :+: 0 :e {x :+: 0|x :e 0}.
{ rewrite H. exact L1. }
claim L3: forall X:set, X = 0 -> 0 :+: 0 /:e X.
{ let X.
  assume HX: X = 0.
  rewrite HX.
  exact (EmptyE (0 :+: 0)).
}
exact (L3 {x :+: 0|x :e 0} (Repl_Empty (fun x => x :+: 0)) L2).
Qed.

(** Mirrors outside_domain_beta_fails. **)
Theorem identity_on_0_at_1_neq : (fun x :e 0 => x) 1 <> 1.
rewrite (function_outside 0 (fun x => x) 1 (EmptyE 1)).
exact neq_0_1.
Qed.

(** Mirrors tracePiSet_empty_of_empty_fibre: a function type with an empty
    fibre is empty. **)
Theorem Pi_Empty_fibre : forall A:set, forall B:set->set,
  forall x :e A, B x = 0 -> (Pi_ x :e A, B x) = 0.
let A B x.
assume Hx: x :e A.
assume HB: B x = 0.
apply Empty_eq.
let f.
assume Hf: f :e Pi_ x :e A, B x.
claim L1: f x :e B x.
{ exact (ap_Pi A B f x Hf Hx). }
apply (EmptyE (f x)).
rewrite <- HB.
exact L1.
Qed.

(** Mirrors missing_trace_product_empty and missing_sum_inhabited: one empty
    fibre makes the function type empty and leaves the type of pairs with a
    member. **)
Theorem empty_fibre_example : (Pi_ x :e 2, x) = 0 /\ (1,0) :e (Sigma_ x :e 2, x).
apply andI.
- apply (Pi_Empty_fibre 2 (fun x => x) 0 In_0_2).
  reflexivity.
- exact (tuple_2_Sigma 2 (fun x => x) 1 In_1_2 0 In_0_1).
Qed.

(** Mirrors varyingTrace with varying_trace_at_empty,
    varying_trace_at_power_empty and varying_trace_nonempty: a function whose
    fibres differ from point to point, with its two values. **)
Theorem varying_function : (fun x :e 2 => x) :e (Pi_ x :e 2, ordsucc x)
  /\ (fun x :e 2 => x) 0 = 0
  /\ (fun x :e 2 => x) 1 = 1
  /\ (fun x :e 2 => x) <> 0.
apply and4I.
- apply (lam_Pi 2 ordsucc (fun x => x)).
  let x.
  assume _: x :e 2.
  exact (ordsuccI2 x).
- exact (beta 2 (fun x => x) 0 In_0_2).
- exact (beta 2 (fun x => x) 1 In_1_2).
- assume H: (fun x :e 2 => x) = 0.
  claim L1: (fun x :e 2 => x) 1 = 0.
  { rewrite H. exact (ap_Empty 1). }
  apply neq_1_0.
  prove 1 = 0.
  apply (eq_i_tra 1 ((fun x :e 2 => x) 1) 0).
  + symmetry.
    exact (beta 2 (fun x => x) 1 In_1_2).
  + exact L1.
Qed.

(** Part 5. No set of all sets, and what the universe operation does to the
    tower. **)

(** Mirrors universalSet_false. **)
Theorem no_set_of_all_sets : ~exists V:set, forall x:set, x :e V.
assume H: exists V:set, forall x:set, x :e V.
apply H.
let V.
assume HV: forall x:set, x :e V.
exact (In_irref V (HV V)).
Qed.

(** Mirrors no_setModel_of_selfTyping: no universe of the tower is a member
    of itself. **)
Theorem universeAt_not_In_self : forall n:set, universeAt n /:e universeAt n.
let n.
exact (In_irref (universeAt n)).
Qed.

(** Mirrors UniverseModel.headTyping_asymm: two sets are not each a member
    of the other, so two universes cannot each be typed by the other. **)
Theorem membership_asymm : forall x y:set, x :e y -> y /:e x.
exact In_no2cycle.
Qed.

(** Mirrors univOf_not_closed_under_univOf: no least closed universe is
    closed under the universe operation. **)
Theorem UnivOf_not_closed_under_UnivOf : forall N:set,
  ~(forall x :e UnivOf N, UnivOf x :e UnivOf N).
let N.
assume H: forall x :e UnivOf N, UnivOf x :e UnivOf N.
exact (In_irref (UnivOf N) (H N (UnivOf_In N))).
Qed.

(** Mirrors univOf_not_closed_under_univOf at every universe of the tower. **)
Theorem universeAt_not_closed_under_UnivOf : forall n:set, nat_p n ->
  ~(forall x :e universeAt n, UnivOf x :e universeAt n).
apply nat_ind.
- prove ~(forall x :e universeAt 0, UnivOf x :e universeAt 0).
  rewrite universeAt_0.
  exact (UnivOf_not_closed_under_UnivOf omega).
- let n.
  assume Hn: nat_p n.
  assume _: ~(forall x :e universeAt n, UnivOf x :e universeAt n).
  prove ~(forall x :e universeAt (ordsucc n), UnivOf x :e universeAt (ordsucc n)).
  rewrite (universeAt_S n Hn).
  exact (UnivOf_not_closed_under_UnivOf (universeAt n)).
Qed.

(** Mirrors univOf_ne_self. **)
Theorem UnivOf_neq_self : forall N:set, UnivOf N <> N.
let N.
assume H: UnivOf N = N.
apply (In_irref (UnivOf N)).
prove UnivOf N :e UnivOf N.
rewrite H at 1.
exact (UnivOf_In N).
Qed.

(** Mirrors univOf_not_idempotent. **)
Theorem UnivOf_not_idempotent : forall N:set, UnivOf (UnivOf N) <> UnivOf N.
let N.
exact (UnivOf_neq_self (UnivOf N)).
Qed.

(** Mirrors univOf_mono. **)
Theorem UnivOf_mono : forall N M:set, N c= M -> UnivOf N c= UnivOf M.
let N M.
assume H: N c= M.
apply (UnivOf_Min N (UnivOf M)).
- prove N :e UnivOf M.
  exact (closed_Subq (UnivOf M) (UnivOf_TransSet M) (UnivOf_ZF_closed M) M
          (UnivOf_In M) N H).
- exact (UnivOf_TransSet M).
- exact (UnivOf_ZF_closed M).
Qed.

(** The universe operation takes a member of a universe of the tower to a
    member of the next universe. This is the form inside the tower of
    lowerSets_univOf_mem, which says that the type of all sets is closed
    under the universe operation. For all sets that is the type of UnivOf,
    an operation on all sets, and needs no theorem here. **)
Theorem UnivOf_In_next_universeAt : forall n:set, nat_p n ->
  forall x :e universeAt n, UnivOf x :e universeAt (ordsucc n).
let n.
assume Hn: nat_p n.
let x.
assume Hx: x :e universeAt n.
claim L1: UnivOf x c= universeAt n.
{ exact (UnivOf_Min x (universeAt n) Hx (universeAt_TransSet n Hn)
          (universeAt_ZF_closed n Hn)).
}
exact (closed_Subq (universeAt (ordsucc n))
        (universeAt_TransSet (ordsucc n) (nat_ordsucc n Hn))
        (universeAt_ZF_closed (ordsucc n) (nat_ordsucc n Hn))
        (universeAt n) (universeAt_In_S n Hn) (UnivOf x) L1).
Qed.

(** Mirrors universeSet_mem_of_closed: a set that has the natural numbers as
    a member and is closed under the universe operation has every universe of
    the tower as a member. **)
Theorem universeAt_In_of_closed_under_UnivOf : forall S:set, omega :e S ->
  (forall x :e S, UnivOf x :e S) -> forall n:set, nat_p n -> universeAt n :e S.
let S.
assume H0: omega :e S.
assume HS: forall x :e S, UnivOf x :e S.
apply nat_ind.
- prove universeAt 0 :e S.
  rewrite universeAt_0.
  exact (HS omega H0).
- let n.
  assume Hn: nat_p n.
  assume IHn: universeAt n :e S.
  prove universeAt (ordsucc n) :e S.
  rewrite (universeAt_S n Hn).
  exact (HS (universeAt n) IHn).
Qed.

(** Part 6. Chains of closed universes. **)

(** Mirrors ClosedChain over the natural numbers: a transitive ZF-closed set
    for every natural number, each a member of every later one. **)
Definition closedChain : (set -> set) -> prop := fun V =>
  (forall n :e omega, TransSet (V n) /\ ZF_closed (V n))
  /\ (forall n :e omega, forall m :e n, V m :e V n).

(** Mirrors universeSet_closedChain: the tower is a chain. **)
Theorem universeAt_closedChain : closedChain universeAt.
prove (forall n :e omega, TransSet (universeAt n) /\ ZF_closed (universeAt n))
  /\ (forall n :e omega, forall m :e n, universeAt m :e universeAt n).
apply andI.
- let n.
  assume Hn: n :e omega.
  apply andI.
  + exact (universeAt_TransSet n (omega_nat_p n Hn)).
  + exact (universeAt_ZF_closed n (omega_nat_p n Hn)).
- let n.
  assume Hn: n :e omega.
  exact (universeAt_In n (omega_nat_p n Hn)).
Qed.

(** Mirrors ClosedChain.mem_succ. **)
Theorem closedChain_In_S : forall V:set->set, closedChain V ->
  forall n :e omega, V n :e V (ordsucc n).
let V.
assume HV: closedChain V.
let n.
assume Hn: n :e omega.
apply HV.
assume _: forall n :e omega, TransSet (V n) /\ ZF_closed (V n).
assume H2: forall n :e omega, forall m :e n, V m :e V n.
exact (H2 (ordsucc n) (omega_ordsucc n Hn) n (ordsuccI2 n)).
Qed.

(** Mirrors ClosedChain.mono. **)
Theorem closedChain_Subq : forall V:set->set, closedChain V ->
  forall n :e omega, forall m :e ordsucc n, V m c= V n.
let V.
assume HV: closedChain V.
let n.
assume Hn: n :e omega.
let m.
assume Hm: m :e ordsucc n.
apply HV.
assume H1: forall n :e omega, TransSet (V n) /\ ZF_closed (V n).
assume H2: forall n :e omega, forall m :e n, V m :e V n.
apply (ordsuccE n m Hm).
- assume H3: m :e n.
  apply (H1 n Hn).
  assume HT: TransSet (V n).
  assume _: ZF_closed (V n).
  exact (HT (V m) (H2 n Hn m H3)).
- assume H3: m = n.
  rewrite H3.
  exact (Subq_ref (V n)).
Qed.

(** Mirrors constant_not_closedChain: one set at every level is not a
    chain. **)
Theorem constant_not_closedChain : forall U:set, ~closedChain (fun _ => U).
let U.
assume H: closedChain (fun _ => U).
apply H.
assume _: forall n :e omega, TransSet U /\ ZF_closed U.
assume H2: forall n :e omega, forall m :e n, U :e U.
exact (In_irref U (H2 1 (nat_p_omega 1 nat_1) 0 In_0_1)).
Qed.

(** Mirrors ClosedChain.empty_mem. **)
Theorem closedChain_Empty : forall V:set->set, closedChain V ->
  forall g :e V 0, forall n :e omega, 0 :e V n.
let V.
assume HV: closedChain V.
let g.
assume Hg: g :e V 0.
let n.
assume Hn: n :e omega.
apply HV.
assume H1: forall n :e omega, TransSet (V n) /\ ZF_closed (V n).
assume _: forall n :e omega, forall m :e n, V m :e V n.
apply (H1 n Hn).
assume HT: TransSet (V n).
assume HC: ZF_closed (V n).
claim L1: V 0 c= V n.
{ exact (closedChain_Subq V HV n Hn 0 (nat_0_in_ordsucc n (omega_nat_p n Hn))). }
exact (closed_Empty (V n) HT HC g (L1 g Hg)).
Qed.

(** Mirrors ClosedChain.truthCode_mem, and identity_mem of
    chain_universeModel_of. **)
Theorem closedChain_truth_value : forall V:set->set, closedChain V ->
  forall g :e V 0, forall n :e omega, forall q:prop, {y :e 1|q} :e V n.
let V.
assume HV: closedChain V.
let g.
assume Hg: g :e V 0.
let n.
assume Hn: n :e omega.
let q.
apply HV.
assume H1: forall n :e omega, TransSet (V n) /\ ZF_closed (V n).
assume _: forall n :e omega, forall m :e n, V m :e V n.
apply (H1 n Hn).
assume HT: TransSet (V n).
assume HC: ZF_closed (V n).
exact (closed_truth_value (V n) HT HC (closedChain_Empty V HV g Hg n Hn) q).
Qed.

(** Mirrors pi_mem of chain_universeModel_of: over every chain, a function
    type with domain at level m and fibres at level n lies at every level
    that bounds both. **)
Theorem closedChain_Pi : forall V:set->set, closedChain V ->
  forall k :e omega, forall m n :e ordsucc k,
  forall A :e V m, forall B:set->set,
  (forall x :e A, B x :e V n) -> (Pi_ x :e A, B x) :e V k.
let V.
assume HV: closedChain V.
let k.
assume Hk: k :e omega.
let m.
assume Hm: m :e ordsucc k.
let n.
assume Hn: n :e ordsucc k.
let A.
assume HA: A :e V m.
let B.
assume HB: forall x :e A, B x :e V n.
apply HV.
assume H1: forall n :e omega, TransSet (V n) /\ ZF_closed (V n).
assume _: forall n :e omega, forall m :e n, V m :e V n.
apply (H1 k Hk).
assume HT: TransSet (V k).
assume HC: ZF_closed (V k).
apply (closed_Pi (V k) HT HC A (closedChain_Subq V HV k Hk m Hm A HA) B).
let x.
assume Hx: x :e A.
exact (closedChain_Subq V HV k Hk n Hn (B x) (HB x Hx)).
Qed.

(** Mirrors sigma_mem of chain_universeModel_of. **)
Theorem closedChain_Sigma : forall V:set->set, closedChain V ->
  forall k :e omega, forall m n :e ordsucc k,
  forall A :e V m, forall B:set->set,
  (forall x :e A, B x :e V n) -> (Sigma_ x :e A, B x) :e V k.
let V.
assume HV: closedChain V.
let k.
assume Hk: k :e omega.
let m.
assume Hm: m :e ordsucc k.
let n.
assume Hn: n :e ordsucc k.
let A.
assume HA: A :e V m.
let B.
assume HB: forall x :e A, B x :e V n.
apply HV.
assume H1: forall n :e omega, TransSet (V n) /\ ZF_closed (V n).
assume _: forall n :e omega, forall m :e n, V m :e V n.
apply (H1 k Hk).
assume HT: TransSet (V k).
assume HC: ZF_closed (V k).
apply (closed_Sigma (V k) HT HC A (closedChain_Subq V HV k Hk m Hm A HA) B).
let x.
assume Hx: x :e A.
exact (closedChain_Subq V HV k Hk n Hn (B x) (HB x Hx)).
Qed.

(** Part 7. The eleven laws of universeTheory: seven laws of sets and four
    laws of the universe operation. Each is stated here in the shape of the
    Lean formula and proved from the corresponding statement of the library.

    law                      library statement      relation
    1  extensionality        set_ext                two inclusions there, one
                                                    equivalence here
    2  empty set             EmptyE                 the same statement
    3  union                 UnionEq                the same, with the two
                                                    conjuncts in the other
                                                    order
    4  power set             PowerEq                the same statement
    5  separation            SepI, SepE             the two directions there,
                                                    one equivalence here
    6  replacement           ReplEq                 the same, with the
                                                    equation turned round
    7  induction on          In_ind                 the same statement
       membership
    8  a set is a member     UnivOf_In              the same statement
       of its universe
    9  the universe is       UnivOf_TransSet        the same statement
       transitive
    10 the universe is       UnivOf_ZF_closed       the same, with the three
       closed                                       conditions grouped the
                                                    other way
    11 the universe is the   UnivOf_Min             the same, with the same
       least such set                               regrouping

    In the foundation ten of the eleven are axioms: set_ext, EmptyAx (of
    which EmptyE is the form used here), UnionEq, PowerEq, ReplEq, In_ind and
    the four about UnivOf. Separation is a theorem there. **)

(** Law 1. Mirrors extensionality. **)
Theorem law_extensionality : forall a b:set,
  (forall x:set, x :e a <-> x :e b) -> a = b.
let a b.
assume H: forall x:set, x :e a <-> x :e b.
apply set_ext.
- let x.
  assume Hx: x :e a.
  exact (iffEL (x :e a) (x :e b) (H x) Hx).
- let x.
  assume Hx: x :e b.
  exact (iffER (x :e a) (x :e b) (H x) Hx).
Qed.

(** Law 2. Mirrors emptyLaw. **)
Theorem law_empty : forall x:set, ~(x :e Empty).
exact EmptyE.
Qed.

(** Law 3. Mirrors unionLaw. **)
Theorem law_union : forall a x:set,
  x :e Union a <-> exists y:set, y :e a /\ x :e y.
let a x.
apply iffI.
- assume H: x :e Union a.
  apply (UnionE_impred a x H).
  let y.
  assume Hxy: x :e y.
  assume Hya: y :e a.
  witness y.
  apply andI.
  + exact Hya.
  + exact Hxy.
- assume H: exists y:set, y :e a /\ x :e y.
  apply H.
  let y.
  assume Hy: y :e a /\ x :e y.
  apply Hy.
  assume Hya: y :e a.
  assume Hxy: x :e y.
  exact (UnionI a x y Hxy Hya).
Qed.

(** Law 4. Mirrors powerLaw. **)
Theorem law_power : forall a b:set,
  b :e Power a <-> forall x:set, x :e b -> x :e a.
exact PowerEq.
Qed.

(** Law 5. Mirrors separationLaw. **)
Theorem law_separation : forall a:set, forall p:set->prop, forall x:set,
  x :e {z :e a|p z} <-> x :e a /\ p x.
let a p x.
apply iffI.
- exact (SepE a p x).
- assume H: x :e a /\ p x.
  apply H.
  assume H1: x :e a.
  assume H2: p x.
  exact (SepI a p x H1 H2).
Qed.

(** Law 6. Mirrors replacementLaw. **)
Theorem law_replacement : forall a:set, forall f:set->set, forall y:set,
  y :e {f x|x :e a} <-> exists x:set, x :e a /\ f x = y.
let a f y.
apply iffI.
- assume H: y :e {f x|x :e a}.
  apply (ReplE_impred a f y H).
  let x.
  assume Hx: x :e a.
  assume Hy: y = f x.
  witness x.
  apply andI.
  + exact Hx.
  + symmetry.
    exact Hy.
- assume H: exists x:set, x :e a /\ f x = y.
  apply H.
  let x.
  assume Hx: x :e a /\ f x = y.
  apply Hx.
  assume Hx1: x :e a.
  assume Hx2: f x = y.
  rewrite <- Hx2.
  exact (ReplI a f x Hx1).
Qed.

(** Law 7. Mirrors setInduction. **)
Theorem law_set_induction : forall p:set->prop,
  (forall a:set, (forall b:set, b :e a -> p b) -> p a) -> forall x:set, p x.
exact In_ind.
Qed.

(** Law 8. Mirrors universeIn. **)
Theorem law_universe_in : forall N:set, N :e UnivOf N.
exact UnivOf_In.
Qed.

(** Law 9. Mirrors universeTransitive. **)
Theorem law_universe_transitive : forall N:set,
  forall x:set, x :e UnivOf N -> forall y:set, y :e x -> y :e UnivOf N.
exact UnivOf_TransSet.
Qed.

(** Law 10. Mirrors universeClosed. **)
Theorem law_universe_closed : forall N:set,
  (forall a:set, a :e UnivOf N -> Union a :e UnivOf N)
  /\ ((forall a:set, a :e UnivOf N -> Power a :e UnivOf N)
      /\ (forall a:set, a :e UnivOf N -> forall f:set->set,
            (forall x:set, x :e a -> f x :e UnivOf N) ->
            {f x|x :e a} :e UnivOf N)).
let N.
apply andI.
- exact (ZF_Union_closed (UnivOf N) (UnivOf_ZF_closed N)).
- apply andI.
  + exact (ZF_Power_closed (UnivOf N) (UnivOf_ZF_closed N)).
  + exact (ZF_Repl_closed (UnivOf N) (UnivOf_ZF_closed N)).
Qed.

(** Law 11. Mirrors universeMinimal. **)
Theorem law_universe_minimal : forall N U:set, N :e U ->
  (forall x:set, x :e U -> forall y:set, y :e x -> y :e U) ->
  ((forall a:set, a :e U -> Union a :e U)
   /\ ((forall a:set, a :e U -> Power a :e U)
       /\ (forall a:set, a :e U -> forall f:set->set,
             (forall x:set, x :e a -> f x :e U) -> {f x|x :e a} :e U))) ->
  forall x:set, x :e UnivOf N -> x :e U.
let N U.
assume HN: N :e U.
assume HT: forall x:set, x :e U -> forall y:set, y :e x -> y :e U.
assume HC: (forall a:set, a :e U -> Union a :e U)
   /\ ((forall a:set, a :e U -> Power a :e U)
       /\ (forall a:set, a :e U -> forall f:set->set,
             (forall x:set, x :e a -> f x :e U) -> {f x|x :e a} :e U)).
apply HC.
assume HC1: forall a:set, a :e U -> Union a :e U.
assume HC23: (forall a:set, a :e U -> Power a :e U)
       /\ (forall a:set, a :e U -> forall f:set->set,
             (forall x:set, x :e a -> f x :e U) -> {f x|x :e a} :e U).
apply HC23.
assume HC2: forall a:set, a :e U -> Power a :e U.
assume HC3: forall a:set, a :e U -> forall f:set->set,
             (forall x:set, x :e a -> f x :e U) -> {f x|x :e a} :e U.
claim LC: ZF_closed U.
{ prove Union_closed U /\ Power_closed U /\ Repl_closed U.
  apply and3I.
  - exact HC1.
  - exact HC2.
  - exact HC3.
}
exact (UnivOf_Min N U HN HT LC).
Qed.
