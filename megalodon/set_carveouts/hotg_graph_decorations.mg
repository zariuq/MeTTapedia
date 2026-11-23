(** Graph decorations inside higher-order Tarski-Grothendieck set theory.

    A graph has a set of nodes n and an edge relation E: E u w says that w is a child of u.
    A decoration assigns a set to each node so that the members of the set at u are the sets
    at the children of u. Aczel's anti-foundation axiom says that every graph has exactly one
    decoration. This foundation has induction on membership instead, and here the answer is:

    - a graph has a decoration exactly when it is well-founded, and then only one
      (decoration_iff_wf, wf_decoration_unique);
    - pointed: the part reachable from a point has a decoration exactly when the point is
      accessible (decoration_from_iff_acc, pointed_decoration_unique); a cycle reachable from
      the point rules out every decoration (reachable_cycle_no_decoration);
    - no set is a member of itself, and no set is its own singleton (no_self_member,
      no_quine_atom).

    Induction on membership is used in exactly two places: decoration_from_acc and
    no_self_member. The decoration is built without picking witnesses: decorate n E v is the
    union of the members of the least universe around n that the least relation closed under
    the decoration step relates to v (decorate, decorate_In_UnivOf). Separation, which the
    library derives with its choice operator, is used.

    Graphs coded as sets carry Aczel's interpreted membership: a code is an interpreted member
    of another when it is bisimilar to the other re-pointed at a child of its point. Native
    membership has no Quine atom; interpreted membership has one, up to bisimilarity
    (native_vs_interpreted). The loop and the two-node cycle are bisimilar, and their codes are
    different sets.

    Part 1  reachability and accessibility
    Part 2  decorations
    Part 3  no set is a member of itself
    Part 4  instances
    Part 5  bisimilarity
    Part 6  graphs as sets and interpreted membership **)

(** Part 1. Reachability and accessibility.

    GraphReach n E p v: v is reached from p along edges into n.
    AccNode n E v: v is accessible, that is, v has every property P such that a node of n has
    P whenever all of its children in n have P. WFGraph n E: every node of n is accessible.
    OnCycle n E c: c reaches itself in one or more steps. **)

Definition GraphReach : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun n E p v => forall R:set -> prop, R p ->
    (forall u w:set, R u -> w :e n -> E u w -> R w) -> R v.

Definition AccNode : set -> (set -> set -> prop) -> set -> prop :=
  fun n E v => forall P:set -> prop,
    (forall u :e n, (forall w :e n, E u w -> P w) -> P u) -> P v.

Definition WFGraph : set -> (set -> set -> prop) -> prop :=
  fun n E => forall v :e n, AccNode n E v.

Definition OnCycle : set -> (set -> set -> prop) -> set -> prop :=
  fun n E c => exists w:set, w :e n /\ E c w /\ GraphReach n E w c.

Theorem GraphReach_refl : forall n:set, forall E:set -> set -> prop, forall p:set,
  GraphReach n E p p.
let n E p.
let R.
assume H0: R p.
assume HS: forall u w:set, R u -> w :e n -> E u w -> R w.
exact H0.
Qed.

Theorem GraphReach_step : forall n:set, forall E:set -> set -> prop, forall p u w:set,
  GraphReach n E p u -> w :e n -> E u w -> GraphReach n E p w.
let n E p u w.
assume Hu: GraphReach n E p u.
assume Hw: w :e n.
assume Huw: E u w.
let R.
assume H0: R p.
assume HS: forall u w:set, R u -> w :e n -> E u w -> R w.
exact (HS u w (Hu R H0 HS) Hw Huw).
Qed.

Theorem GraphReach_head : forall n:set, forall E:set -> set -> prop, forall p v:set,
  GraphReach n E p v ->
  v = p \/ exists w:set, w :e n /\ E p w /\ GraphReach n E w v.
let n E p v.
assume Hv: GraphReach n E p v.
apply (Hv (fun v => v = p \/ exists w:set, w :e n /\ E p w /\ GraphReach n E w v)).
- prove p = p \/ exists w:set, w :e n /\ E p w /\ GraphReach n E w p.
  apply orIL.
  reflexivity.
- let u w.
  assume Hu: u = p \/ exists w:set, w :e n /\ E p w /\ GraphReach n E w u.
  assume Hw: w :e n.
  assume Huw: E u w.
  prove w = p \/ exists w1:set, w1 :e n /\ E p w1 /\ GraphReach n E w1 w.
  apply orIR.
  apply Hu.
  + assume Hup: u = p.
    witness w.
    apply and3I.
    * exact Hw.
    * rewrite <- Hup. exact Huw.
    * exact (GraphReach_refl n E w).
  + assume H1: exists w1:set, w1 :e n /\ E p w1 /\ GraphReach n E w1 u.
    apply H1.
    let w1.
    assume H2: w1 :e n /\ E p w1 /\ GraphReach n E w1 u.
    apply and3E (w1 :e n) (E p w1) (GraphReach n E w1 u) H2.
    assume Hw1: w1 :e n.
    assume Hpw1: E p w1.
    assume Hr: GraphReach n E w1 u.
    witness w1.
    apply and3I.
    * exact Hw1.
    * exact Hpw1.
    * exact (GraphReach_step n E w1 u w Hr Hw Huw).
Qed.

Theorem AccNode_In : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> v :e n.
let n E v.
assume Hv: AccNode n E v.
apply (Hv (fun v => v :e n)).
let u.
assume Hu: u :e n.
assume _: forall w :e n, E u w -> w :e n.
exact Hu.
Qed.

Theorem AccNode_intro : forall n:set, forall E:set -> set -> prop, forall v:set,
  v :e n -> (forall w :e n, E v w -> AccNode n E w) -> AccNode n E v.
let n E v.
assume Hv: v :e n.
assume Hc: forall w :e n, E v w -> AccNode n E w.
let P.
assume HP: forall u :e n, (forall w :e n, E u w -> P w) -> P u.
apply (HP v Hv).
let w.
assume Hw: w :e n.
assume Hvw: E v w.
exact (Hc w Hw Hvw P HP).
Qed.

Theorem AccNode_child : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> forall w :e n, E v w -> AccNode n E w.
let n E v.
assume Hv: AccNode n E v.
claim L: AccNode n E v /\ (forall w :e n, E v w -> AccNode n E w).
{ apply (Hv (fun v => AccNode n E v /\ (forall w :e n, E v w -> AccNode n E w))).
  let u.
  assume Hu: u :e n.
  assume IH: forall w :e n, E u w -> AccNode n E w /\ (forall w' :e n, E w w' -> AccNode n E w').
  claim Lc: forall w :e n, E u w -> AccNode n E w.
  { let w.
    assume Hw: w :e n.
    assume Huw: E u w.
    exact (andEL (AccNode n E w) (forall w' :e n, E w w' -> AccNode n E w') (IH w Hw Huw)).
  }
  prove AccNode n E u /\ (forall w :e n, E u w -> AccNode n E w).
  apply andI.
  - exact (AccNode_intro n E u Hu Lc).
  - exact Lc.
}
exact (andER (AccNode n E v) (forall w :e n, E v w -> AccNode n E w) L).
Qed.

Theorem AccNode_not_OnCycle : forall n:set, forall E:set -> set -> prop, forall c:set,
  AccNode n E c -> ~OnCycle n E c.
let n E c.
assume Hc: AccNode n E c.
apply (Hc (fun c => ~OnCycle n E c)).
let u.
assume Hu: u :e n.
assume IH: forall w :e n, E u w -> ~OnCycle n E w.
prove ~OnCycle n E u.
assume Hcyc: OnCycle n E u.
apply Hcyc.
let w0.
assume H1: w0 :e n /\ E u w0 /\ GraphReach n E w0 u.
apply and3E (w0 :e n) (E u w0) (GraphReach n E w0 u) H1.
assume Hw0: w0 :e n.
assume Huw0: E u w0.
assume Hr: GraphReach n E w0 u.
apply (IH w0 Hw0 Huw0).
prove exists w:set, w :e n /\ E w0 w /\ GraphReach n E w w0.
apply (GraphReach_head n E w0 u Hr).
- assume Heq: u = w0.
  witness w0.
  apply and3I.
  + exact Hw0.
  + rewrite <- Heq at 1. exact Huw0.
  + exact (GraphReach_refl n E w0).
- assume H2: exists w:set, w :e n /\ E w0 w /\ GraphReach n E w u.
  apply H2.
  let w1.
  assume H3: w1 :e n /\ E w0 w1 /\ GraphReach n E w1 u.
  apply and3E (w1 :e n) (E w0 w1) (GraphReach n E w1 u) H3.
  assume Hw1: w1 :e n.
  assume Hw0w1: E w0 w1.
  assume Hr1: GraphReach n E w1 u.
  witness w1.
  apply and3I.
  + exact Hw1.
  + exact Hw0w1.
  + exact (GraphReach_step n E w1 u w0 Hr1 Hw0 Huw0).
Qed.

(** Part 2. Decorations.

    IsDecoration n E d: for every node v of n, the members of d v are the d w for the
    children w of v in n. IsDecorationFrom n E p d: the same, for the nodes reached from p.
    DecRel n E is the least relation closed under the decoration step DecStep. **)
Definition IsDecoration : set -> (set -> set -> prop) -> (set -> set) -> prop :=
  fun n E d => forall v :e n, forall y:set,
    y :e d v <-> exists w:set, w :e n /\ E v w /\ d w = y.

Definition IsDecorationFrom : set -> (set -> set -> prop) -> set -> (set -> set) -> prop :=
  fun n E p d => forall v :e n, GraphReach n E p v -> forall y:set,
    y :e d v <-> exists w:set, w :e n /\ E v w /\ d w = y.

Definition Children : set -> (set -> set -> prop) -> set -> set :=
  fun n E v => {w :e n | E v w}.

Definition DecSet : set -> (set -> set -> prop) -> (set -> set) -> set -> set :=
  fun n E f v => {f w | w :e Children n E v}.

Definition DecStep : set -> (set -> set -> prop) -> (set -> set -> prop) -> prop :=
  fun n E R => forall v :e n, forall f:set -> set,
    (forall w :e n, E v w -> R w (f w)) -> R v (DecSet n E f v).

Definition DecRel : set -> (set -> set -> prop) -> set -> set -> prop :=
  fun n E v y => forall R:set -> set -> prop, DecStep n E R -> R v y.

Definition decorate : set -> (set -> set -> prop) -> set -> set :=
  fun n E v => Union {y :e UnivOf n | DecRel n E v y}.

Theorem DecSet_mem : forall n:set, forall E:set -> set -> prop, forall f:set -> set,
  forall v y:set,
  y :e DecSet n E f v <-> exists w:set, w :e n /\ E v w /\ f w = y.
let n E f v y.
apply iffI.
- assume Hy: y :e DecSet n E f v.
  apply (ReplE_impred (Children n E v) f y Hy).
  let w.
  assume Hw: w :e Children n E v.
  assume Hyw: y = f w.
  apply (SepE n (fun w => E v w) w Hw).
  assume Hwn: w :e n.
  assume Hvw: E v w.
  witness w.
  apply and3I.
  + exact Hwn.
  + exact Hvw.
  + symmetry. exact Hyw.
- assume H: exists w:set, w :e n /\ E v w /\ f w = y.
  apply H.
  let w.
  assume H1: w :e n /\ E v w /\ f w = y.
  apply and3E (w :e n) (E v w) (f w = y) H1.
  assume Hwn: w :e n.
  assume Hvw: E v w.
  assume Hfw: f w = y.
  rewrite <- Hfw.
  exact (ReplI (Children n E v) f w (SepI n (fun w => E v w) w Hwn Hvw)).
Qed.

Theorem DecRel_closed : forall n:set, forall E:set -> set -> prop, DecStep n E (DecRel n E).
let n E v.
assume Hv: v :e n.
let f.
assume Hf: forall w :e n, E v w -> DecRel n E w (f w).
prove DecRel n E v (DecSet n E f v).
let R.
assume HR: DecStep n E R.
exact (HR v Hv f (fun w Hw Hvw => Hf w Hw Hvw R HR)).
Qed.

Theorem DecRel_inv : forall n:set, forall E:set -> set -> prop, forall v y:set,
  DecRel n E v y ->
  v :e n /\ exists f:set -> set, (forall w :e n, E v w -> DecRel n E w (f w))
                              /\ y = DecSet n E f v.
let n E v y.
assume Hy: DecRel n E v y.
claim L: DecRel n E v y /\ (v :e n /\ exists f:set -> set,
            (forall w :e n, E v w -> DecRel n E w (f w)) /\ y = DecSet n E f v).
{ apply (Hy (fun v y => DecRel n E v y /\ (v :e n /\ exists f:set -> set,
            (forall w :e n, E v w -> DecRel n E w (f w)) /\ y = DecSet n E f v))).
  let u.
  assume Hu: u :e n.
  let f.
  assume Hf: forall w :e n, E u w -> DecRel n E w (f w) /\ (w :e n /\ exists g:set -> set,
            (forall w' :e n, E w w' -> DecRel n E w' (g w')) /\ f w = DecSet n E g w).
  prove DecRel n E u (DecSet n E f u) /\ (u :e n /\ exists g:set -> set,
            (forall w :e n, E u w -> DecRel n E w (g w)) /\ DecSet n E f u = DecSet n E g u).
  claim Lc: forall w :e n, E u w -> DecRel n E w (f w).
  { let w.
    assume Hw: w :e n.
    assume Huw: E u w.
    exact (andEL (DecRel n E w (f w)) (w :e n /\ exists g:set -> set,
            (forall w' :e n, E w w' -> DecRel n E w' (g w')) /\ f w = DecSet n E g w)
            (Hf w Hw Huw)).
  }
  apply andI.
  - exact (DecRel_closed n E u Hu f Lc).
  - apply andI.
    + exact Hu.
    + witness f.
      apply andI.
      * exact Lc.
      * reflexivity.
}
exact (andER (DecRel n E v y) (v :e n /\ exists f:set -> set,
            (forall w :e n, E v w -> DecRel n E w (f w)) /\ y = DecSet n E f v) L).
Qed.

Theorem Union_Sep_unique : forall X:set, forall P:set -> prop, forall y0:set,
  y0 :e X -> P y0 -> (forall y :e X, P y -> y = y0) -> Union {y :e X | P y} = y0.
let X P y0.
assume H0: y0 :e X.
assume HP: P y0.
assume Hu: forall y :e X, P y -> y = y0.
apply set_ext.
- let z.
  assume Hz: z :e Union {y :e X | P y}.
  apply (UnionE_impred {y :e X | P y} z Hz).
  let Y.
  assume HzY: z :e Y.
  assume HY: Y :e {y :e X | P y}.
  apply (SepE X P Y HY).
  assume HYX: Y :e X.
  assume HPY: P Y.
  rewrite <- (Hu Y HYX HPY).
  exact HzY.
- let z.
  assume Hz: z :e y0.
  exact (UnionI {y :e X | P y} z y0 Hz (SepI X P y0 H0 HP)).
Qed.

Theorem DecRel_functional : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> forall y y':set, DecRel n E v y -> DecRel n E v y' -> y = y'.
let n E v.
assume Hv: AccNode n E v.
apply (Hv (fun v => forall y y':set, DecRel n E v y -> DecRel n E v y' -> y = y')).
let u.
assume Hu: u :e n.
assume IH: forall w :e n, E u w ->
  forall y y':set, DecRel n E w y -> DecRel n E w y' -> y = y'.
prove forall y y':set, DecRel n E u y -> DecRel n E u y' -> y = y'.
let y y'.
assume Hy: DecRel n E u y.
assume Hy': DecRel n E u y'.
apply (DecRel_inv n E u y Hy).
assume _: u :e n.
assume Hex: exists f:set -> set, (forall w :e n, E u w -> DecRel n E w (f w))
                              /\ y = DecSet n E f u.
apply (DecRel_inv n E u y' Hy').
assume _: u :e n.
assume Hex': exists f:set -> set, (forall w :e n, E u w -> DecRel n E w (f w))
                              /\ y' = DecSet n E f u.
apply Hex.
let f.
assume Hf: (forall w :e n, E u w -> DecRel n E w (f w)) /\ y = DecSet n E f u.
apply Hf.
assume Hf1: forall w :e n, E u w -> DecRel n E w (f w).
assume Hf2: y = DecSet n E f u.
apply Hex'.
let f'.
assume Hf': (forall w :e n, E u w -> DecRel n E w (f' w)) /\ y' = DecSet n E f' u.
apply Hf'.
assume Hf1': forall w :e n, E u w -> DecRel n E w (f' w).
assume Hf2': y' = DecSet n E f' u.
rewrite Hf2.
rewrite Hf2'.
prove {f w | w :e Children n E u} = {f' w | w :e Children n E u}.
apply ReplEq_ext.
let w.
assume Hw: w :e Children n E u.
apply (SepE n (fun w => E u w) w Hw).
assume Hwn: w :e n.
assume Huw: E u w.
exact (IH w Hwn Huw (f w) (f' w) (Hf1 w Hwn Huw) (Hf1' w Hwn Huw)).
Qed.

Theorem Children_In_UnivOf : forall n:set, forall E:set -> set -> prop, forall v:set,
  Children n E v :e UnivOf n.
let n E v.
claim LP: Power n :e UnivOf n.
{ exact (ZF_Power_closed (UnivOf n) (UnivOf_ZF_closed n) n (UnivOf_In n)). }
exact (UnivOf_TransSet n (Power n) LP (Children n E v) (Sep_In_Power n (fun w => E v w))).
Qed.

Theorem DecSet_In_UnivOf : forall n:set, forall E:set -> set -> prop, forall f:set -> set,
  forall v:set, (forall w :e n, E v w -> f w :e UnivOf n) -> DecSet n E f v :e UnivOf n.
let n E f v.
assume Hf: forall w :e n, E v w -> f w :e UnivOf n.
prove {f w | w :e Children n E v} :e UnivOf n.
apply (ZF_Repl_closed (UnivOf n) (UnivOf_ZF_closed n) (Children n E v)
         (Children_In_UnivOf n E v) f).
let w.
assume Hw: w :e Children n E v.
apply (SepE n (fun w => E v w) w Hw).
assume Hwn: w :e n.
assume Hvw: E v w.
exact (Hf w Hwn Hvw).
Qed.

Theorem decorate_acc : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v ->
  AccNode n E v /\ DecRel n E v (decorate n E v) /\ decorate n E v :e UnivOf n.
let n E v.
assume Hv: AccNode n E v.
apply (Hv (fun v => AccNode n E v /\ DecRel n E v (decorate n E v)
                    /\ decorate n E v :e UnivOf n)).
let u.
assume Hu: u :e n.
assume IH: forall w :e n, E u w ->
  AccNode n E w /\ DecRel n E w (decorate n E w) /\ decorate n E w :e UnivOf n.
prove AccNode n E u /\ DecRel n E u (decorate n E u) /\ decorate n E u :e UnivOf n.
claim LA: AccNode n E u.
{ apply (AccNode_intro n E u Hu).
  let w.
  assume Hw: w :e n.
  assume Huw: E u w.
  apply and3E (AccNode n E w) (DecRel n E w (decorate n E w)) (decorate n E w :e UnivOf n)
    (IH w Hw Huw).
  assume H1: AccNode n E w.
  assume _: DecRel n E w (decorate n E w).
  assume _: decorate n E w :e UnivOf n.
  exact H1.
}
claim LR: DecRel n E u (DecSet n E (decorate n E) u).
{ apply (DecRel_closed n E u Hu (decorate n E)).
  let w.
  assume Hw: w :e n.
  assume Huw: E u w.
  apply and3E (AccNode n E w) (DecRel n E w (decorate n E w)) (decorate n E w :e UnivOf n)
    (IH w Hw Huw).
  assume _: AccNode n E w.
  assume H2: DecRel n E w (decorate n E w).
  assume _: decorate n E w :e UnivOf n.
  exact H2.
}
claim LU: DecSet n E (decorate n E) u :e UnivOf n.
{ apply (DecSet_In_UnivOf n E (decorate n E) u).
  let w.
  assume Hw: w :e n.
  assume Huw: E u w.
  apply and3E (AccNode n E w) (DecRel n E w (decorate n E w)) (decorate n E w :e UnivOf n)
    (IH w Hw Huw).
  assume _: AccNode n E w.
  assume _: DecRel n E w (decorate n E w).
  assume H3: decorate n E w :e UnivOf n.
  exact H3.
}
claim LE: decorate n E u = DecSet n E (decorate n E) u.
{ prove Union {y :e UnivOf n | DecRel n E u y} = DecSet n E (decorate n E) u.
  apply (Union_Sep_unique (UnivOf n) (DecRel n E u) (DecSet n E (decorate n E) u) LU LR).
  let y.
  assume _: y :e UnivOf n.
  assume Hy: DecRel n E u y.
  exact (DecRel_functional n E u LA y (DecSet n E (decorate n E) u) Hy LR).
}
apply and3I.
- exact LA.
- rewrite LE. exact LR.
- rewrite LE. exact LU.
Qed.

Theorem decorate_DecRel : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> DecRel n E v (decorate n E v).
let n E v.
assume Hv: AccNode n E v.
apply and3E (AccNode n E v) (DecRel n E v (decorate n E v)) (decorate n E v :e UnivOf n)
  (decorate_acc n E v Hv).
assume _: AccNode n E v.
assume H2: DecRel n E v (decorate n E v).
assume _: decorate n E v :e UnivOf n.
exact H2.
Qed.

(** The decoration of an accessible node lies in the least universe around the nodes. **)
Theorem decorate_In_UnivOf : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> decorate n E v :e UnivOf n.
let n E v.
assume Hv: AccNode n E v.
apply and3E (AccNode n E v) (DecRel n E v (decorate n E v)) (decorate n E v :e UnivOf n)
  (decorate_acc n E v Hv).
assume _: AccNode n E v.
assume _: DecRel n E v (decorate n E v).
assume H3: decorate n E v :e UnivOf n.
exact H3.
Qed.

Theorem decorate_eq : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> decorate n E v = DecSet n E (decorate n E) v.
let n E v.
assume Hv: AccNode n E v.
apply (DecRel_functional n E v Hv (decorate n E v) (DecSet n E (decorate n E) v)
         (decorate_DecRel n E v Hv)).
apply (DecRel_closed n E v (AccNode_In n E v Hv) (decorate n E)).
let w.
assume Hw: w :e n.
assume Hvw: E v w.
exact (decorate_DecRel n E w (AccNode_child n E v Hv w Hw Hvw)).
Qed.

Theorem decorate_mem : forall n:set, forall E:set -> set -> prop, forall v:set,
  AccNode n E v -> forall y:set,
  y :e decorate n E v <-> exists w:set, w :e n /\ E v w /\ decorate n E w = y.
let n E v.
assume Hv: AccNode n E v.
let y.
rewrite (decorate_eq n E v Hv) at 1.
exact (DecSet_mem n E (decorate n E) v y).
Qed.

Theorem GraphReach_AccNode : forall n:set, forall E:set -> set -> prop, forall p v:set,
  AccNode n E p -> GraphReach n E p v -> AccNode n E v.
let n E p v.
assume Hp: AccNode n E p.
assume Hv: GraphReach n E p v.
apply (Hv (fun v => AccNode n E v)).
- exact Hp.
- let u w.
  assume Hu: AccNode n E u.
  assume Hw: w :e n.
  assume Huw: E u w.
  exact (AccNode_child n E u Hu w Hw Huw).
Qed.

Theorem IsDecoration_From : forall n:set, forall E:set -> set -> prop, forall p:set,
  forall d:set -> set, IsDecoration n E d -> IsDecorationFrom n E p d.
let n E p d.
assume Hd: IsDecoration n E d.
let v.
assume Hv: v :e n.
assume _: GraphReach n E p v.
exact (Hd v Hv).
Qed.

(** Existence, pointed form: an accessible point has a decoration of the part reachable
    from it. **)
Theorem acc_point_decorates : forall n:set, forall E:set -> set -> prop, forall p:set,
  AccNode n E p -> IsDecorationFrom n E p (decorate n E).
let n E p.
assume Hp: AccNode n E p.
let v.
assume Hv: v :e n.
assume Hr: GraphReach n E p v.
exact (decorate_mem n E v (GraphReach_AccNode n E p v Hp Hr)).
Qed.

(** Existence: a well-founded graph has a decoration. **)
Theorem wf_graph_decorates : forall n:set, forall E:set -> set -> prop,
  WFGraph n E -> IsDecoration n E (decorate n E).
let n E.
assume HW: WFGraph n E.
let v.
assume Hv: v :e n.
exact (decorate_mem n E v (HW v Hv)).
Qed.

(** Uniqueness, pointed form. **)
Theorem decoration_from_unique : forall n:set, forall E:set -> set -> prop, forall p:set,
  forall d d':set -> set, IsDecorationFrom n E p d -> IsDecorationFrom n E p d' ->
  forall v:set, AccNode n E v -> GraphReach n E p v -> d v = d' v.
let n E p d d'.
assume Hd: IsDecorationFrom n E p d.
assume Hd': IsDecorationFrom n E p d'.
let v.
assume Hv: AccNode n E v.
apply (Hv (fun v => GraphReach n E p v -> d v = d' v)).
let u.
assume Hu: u :e n.
assume IH: forall w :e n, E u w -> GraphReach n E p w -> d w = d' w.
prove GraphReach n E p u -> d u = d' u.
assume Hr: GraphReach n E p u.
apply set_ext.
- let y.
  assume Hy: y :e d u.
  apply (iffEL (y :e d u) (exists w:set, w :e n /\ E u w /\ d w = y) (Hd u Hu Hr y) Hy).
  let w.
  assume H1: w :e n /\ E u w /\ d w = y.
  apply and3E (w :e n) (E u w) (d w = y) H1.
  assume Hw: w :e n.
  assume Huw: E u w.
  assume Hdw: d w = y.
  apply (iffER (y :e d' u) (exists w:set, w :e n /\ E u w /\ d' w = y) (Hd' u Hu Hr y)).
  witness w.
  apply and3I.
  + exact Hw.
  + exact Huw.
  + rewrite <- (IH w Hw Huw (GraphReach_step n E p u w Hr Hw Huw)).
    exact Hdw.
- let y.
  assume Hy: y :e d' u.
  apply (iffEL (y :e d' u) (exists w:set, w :e n /\ E u w /\ d' w = y) (Hd' u Hu Hr y) Hy).
  let w.
  assume H1: w :e n /\ E u w /\ d' w = y.
  apply and3E (w :e n) (E u w) (d' w = y) H1.
  assume Hw: w :e n.
  assume Huw: E u w.
  assume Hdw: d' w = y.
  apply (iffER (y :e d u) (exists w:set, w :e n /\ E u w /\ d w = y) (Hd u Hu Hr y)).
  witness w.
  apply and3I.
  + exact Hw.
  + exact Huw.
  + rewrite (IH w Hw Huw (GraphReach_step n E p u w Hr Hw Huw)).
    exact Hdw.
Qed.

(** The step that uses induction on membership: every node reachable from the point of a
    decorated graph is accessible. **)
Theorem decoration_from_acc : forall n:set, forall E:set -> set -> prop, forall p:set,
  forall d:set -> set, IsDecorationFrom n E p d ->
  forall v :e n, GraphReach n E p v -> AccNode n E v.
let n E p d.
assume Hd: IsDecorationFrom n E p d.
claim L: forall x:set, forall v :e n, GraphReach n E p v -> d v = x -> AccNode n E v.
{ apply In_ind.
  let x.
  assume IH: forall z :e x, forall v :e n, GraphReach n E p v -> d v = z -> AccNode n E v.
  let v.
  assume Hv: v :e n.
  assume Hr: GraphReach n E p v.
  assume Hdv: d v = x.
  apply (AccNode_intro n E v Hv).
  let w.
  assume Hw: w :e n.
  assume Hvw: E v w.
  claim Lm: d w :e x.
  { rewrite <- Hdv.
    apply (iffER (d w :e d v) (exists w':set, w' :e n /\ E v w' /\ d w' = d w) (Hd v Hv Hr (d w))).
    witness w.
    apply and3I.
    - exact Hw.
    - exact Hvw.
    - reflexivity.
  }
  apply (IH (d w) Lm w Hw (GraphReach_step n E p v w Hr Hw Hvw)).
  reflexivity.
}
let v.
assume Hv: v :e n.
assume Hr: GraphReach n E p v.
apply (L (d v) v Hv Hr).
reflexivity.
Qed.

(** Uniqueness, pointed form, without an accessibility hypothesis: two decorations of the part
    reachable from the point agree on that part. **)
Theorem pointed_decoration_unique : forall n:set, forall E:set -> set -> prop, forall p:set,
  forall d d':set -> set, IsDecorationFrom n E p d -> IsDecorationFrom n E p d' ->
  forall v :e n, GraphReach n E p v -> d v = d' v.
let n E p d d'.
assume Hd: IsDecorationFrom n E p d.
assume Hd': IsDecorationFrom n E p d'.
let v.
assume Hv: v :e n.
assume Hr: GraphReach n E p v.
exact (decoration_from_unique n E p d d' Hd Hd' v (decoration_from_acc n E p d Hd v Hv Hr) Hr).
Qed.

(** A pointed graph has a decoration of the part reachable from its point exactly when
    the point is accessible. **)
Theorem decoration_from_iff_acc : forall n:set, forall E:set -> set -> prop, forall p :e n,
  (exists d:set -> set, IsDecorationFrom n E p d) <-> AccNode n E p.
let n E p.
assume Hp: p :e n.
apply iffI.
- assume H: exists d:set -> set, IsDecorationFrom n E p d.
  apply H.
  let d.
  assume Hd: IsDecorationFrom n E p d.
  exact (decoration_from_acc n E p d Hd p Hp (GraphReach_refl n E p)).
- assume Hacc: AccNode n E p.
  witness (decorate n E).
  exact (acc_point_decorates n E p Hacc).
Qed.

(** A graph has a decoration exactly when it is well-founded. **)
Theorem decoration_iff_wf : forall n:set, forall E:set -> set -> prop,
  (exists d:set -> set, IsDecoration n E d) <-> WFGraph n E.
let n E.
apply iffI.
- assume H: exists d:set -> set, IsDecoration n E d.
  apply H.
  let d.
  assume Hd: IsDecoration n E d.
  let v.
  assume Hv: v :e n.
  exact (decoration_from_acc n E v d (IsDecoration_From n E v d Hd) v Hv (GraphReach_refl n E v)).
- assume HW: WFGraph n E.
  witness (decorate n E).
  exact (wf_graph_decorates n E HW).
Qed.

(** Uniqueness: a graph has at most one decoration. **)
Theorem wf_decoration_unique : forall n:set, forall E:set -> set -> prop,
  forall d d':set -> set, IsDecoration n E d -> IsDecoration n E d' ->
  forall v :e n, d v = d' v.
let n E d d'.
assume Hd: IsDecoration n E d.
assume Hd': IsDecoration n E d'.
let v.
assume Hv: v :e n.
exact (decoration_from_unique n E v d d' (IsDecoration_From n E v d Hd)
         (IsDecoration_From n E v d' Hd')
         v (decoration_from_acc n E v d (IsDecoration_From n E v d Hd) v Hv (GraphReach_refl n E v))
         (GraphReach_refl n E v)).
Qed.

(** A graph in which a cycle is reachable from the point has no decoration, not even of the
    part reachable from the point. **)
Theorem reachable_cycle_no_decoration : forall n:set, forall E:set -> set -> prop, forall p:set,
  forall c :e n, GraphReach n E p c -> OnCycle n E c ->
  ~exists d:set -> set, IsDecorationFrom n E p d.
let n E p c.
assume Hc: c :e n.
assume Hr: GraphReach n E p c.
assume Hcyc: OnCycle n E c.
assume H: exists d:set -> set, IsDecorationFrom n E p d.
apply H.
let d.
assume Hd: IsDecorationFrom n E p d.
exact (AccNode_not_OnCycle n E c (decoration_from_acc n E p d Hd c Hc Hr) Hcyc).
Qed.

Theorem cycle_no_decoration : forall n:set, forall E:set -> set -> prop,
  forall c :e n, OnCycle n E c -> ~exists d:set -> set, IsDecoration n E d.
let n E c.
assume Hc: c :e n.
assume Hcyc: OnCycle n E c.
assume H: exists d:set -> set, IsDecoration n E d.
apply H.
let d.
assume Hd: IsDecoration n E d.
apply (reachable_cycle_no_decoration n E c c Hc (GraphReach_refl n E c) Hcyc).
witness d.
exact (IsDecoration_From n E c d Hd).
Qed.

(** Part 3. No set is a member of itself. **)

(** No set is a member of itself, and no set is its own singleton. **)
Theorem no_self_member : forall x:set, ~(x :e x).
apply In_ind.
let x.
assume IH: forall z :e x, ~(z :e z).
assume Hx: x :e x.
exact (IH x Hx Hx).
Qed.

Theorem no_quine_atom : ~exists x:set, x = {x}.
assume H: exists x:set, x = {x}.
apply H.
let x.
assume Hx: x = {x}.
apply (no_self_member x).
prove x :e x.
rewrite Hx at 2.
exact (SingI x).
Qed.

(** Part 4. Instances. **)

(** Nodes are the natural numbers below the number of nodes. **)

(** The one-node loop. **)
Definition LoopEdge : set -> set -> prop := fun u w => True.

Theorem loop_OnCycle : OnCycle 1 LoopEdge 0.
prove exists w:set, w :e 1 /\ LoopEdge 0 w /\ GraphReach 1 LoopEdge w 0.
witness 0.
apply and3I.
- exact In_0_1.
- exact TrueI.
- exact (GraphReach_refl 1 LoopEdge 0).
Qed.

Theorem loop_no_decoration : ~exists d:set -> set, IsDecoration 1 LoopEdge d.
exact (cycle_no_decoration 1 LoopEdge 0 In_0_1 loop_OnCycle).
Qed.

Theorem loop_point_no_decoration : ~exists d:set -> set, IsDecorationFrom 1 LoopEdge 0 d.
exact (reachable_cycle_no_decoration 1 LoopEdge 0 0 In_0_1 (GraphReach_refl 1 LoopEdge 0)
         loop_OnCycle).
Qed.

Theorem loop_not_wf : ~WFGraph 1 LoopEdge.
assume HW: WFGraph 1 LoopEdge.
exact (AccNode_not_OnCycle 1 LoopEdge 0 (HW 0 In_0_1) loop_OnCycle).
Qed.

(** The same, through the loop: a set equal to its own singleton would decorate the loop. **)
Theorem no_quine_atom_via_loop : ~exists x:set, x = {x}.
assume H: exists x:set, x = {x}.
apply H.
let x.
assume Hx: x = {x}.
apply loop_no_decoration.
witness (fun _:set => x).
let v.
assume Hv: v :e 1.
let y.
prove y :e x <-> exists w:set, w :e 1 /\ LoopEdge v w /\ x = y.
apply iffI.
- assume Hy: y :e x.
  witness 0.
  apply and3I.
  + exact In_0_1.
  + exact TrueI.
  + symmetry.
    apply SingE.
    rewrite <- Hx.
    exact Hy.
- assume H1: exists w:set, w :e 1 /\ LoopEdge v w /\ x = y.
  apply H1.
  let w.
  assume H2: w :e 1 /\ LoopEdge v w /\ x = y.
  apply and3E (w :e 1) (LoopEdge v w) (x = y) H2.
  assume _: w :e 1.
  assume _: LoopEdge v w.
  assume Hxy: x = y.
  rewrite <- Hxy.
  rewrite Hx at 2.
  exact (SingI x).
Qed.

(** The two-node cycle. **)
Definition CycleEdge : set -> set -> prop := fun u w => (u = 0 /\ w = 1) \/ (u = 1 /\ w = 0).

Theorem CycleEdge_0_1 : CycleEdge 0 1.
prove (0 = 0 /\ 1 = 1) \/ (0 = 1 /\ 1 = 0).
apply orIL.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem CycleEdge_1_0 : CycleEdge 1 0.
prove (1 = 0 /\ 0 = 1) \/ (1 = 1 /\ 0 = 0).
apply orIR.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem cycle_OnCycle : OnCycle 2 CycleEdge 0.
prove exists w:set, w :e 2 /\ CycleEdge 0 w /\ GraphReach 2 CycleEdge w 0.
witness 1.
apply and3I.
- exact In_1_2.
- exact CycleEdge_0_1.
- exact (GraphReach_step 2 CycleEdge 1 1 0 (GraphReach_refl 2 CycleEdge 1) In_0_2 CycleEdge_1_0).
Qed.

Theorem cycle_no_decoration_inst : ~exists d:set -> set, IsDecoration 2 CycleEdge d.
exact (cycle_no_decoration 2 CycleEdge 0 In_0_2 cycle_OnCycle).
Qed.

Theorem cycle_point_no_decoration : ~exists d:set -> set, IsDecorationFrom 2 CycleEdge 0 d.
exact (reachable_cycle_no_decoration 2 CycleEdge 0 0 In_0_2 (GraphReach_refl 2 CycleEdge 0)
         cycle_OnCycle).
Qed.

Theorem cycle_not_wf : ~WFGraph 2 CycleEdge.
assume HW: WFGraph 2 CycleEdge.
exact (AccNode_not_OnCycle 2 CycleEdge 0 (HW 0 In_0_2) cycle_OnCycle).
Qed.

(** The Scott pair: node 0 is a loop; node 1 has both nodes as children. **)
Definition ScottEdge : set -> set -> prop :=
  fun u w => (u = 0 /\ w = 0) \/ (u = 1 /\ w = 0) \/ (u = 1 /\ w = 1).

Theorem ScottEdge_0_0 : ScottEdge 0 0.
prove (0 = 0 /\ 0 = 0) \/ (0 = 1 /\ 0 = 0) \/ (0 = 1 /\ 0 = 1).
apply or3I1.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem ScottEdge_1_0 : ScottEdge 1 0.
prove (1 = 0 /\ 0 = 0) \/ (1 = 1 /\ 0 = 0) \/ (1 = 1 /\ 0 = 1).
apply or3I2.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem scott_OnCycle : OnCycle 2 ScottEdge 0.
prove exists w:set, w :e 2 /\ ScottEdge 0 w /\ GraphReach 2 ScottEdge w 0.
witness 0.
apply and3I.
- exact In_0_2.
- exact ScottEdge_0_0.
- exact (GraphReach_refl 2 ScottEdge 0).
Qed.

Theorem scott_point_no_decoration : ~exists d:set -> set, IsDecorationFrom 2 ScottEdge 1 d.
exact (reachable_cycle_no_decoration 2 ScottEdge 1 0 In_0_2
         (GraphReach_step 2 ScottEdge 1 1 0 (GraphReach_refl 2 ScottEdge 1) In_0_2 ScottEdge_1_0)
         scott_OnCycle).
Qed.

Theorem scott_no_decoration : ~exists d:set -> set, IsDecoration 2 ScottEdge d.
exact (cycle_no_decoration 2 ScottEdge 0 In_0_2 scott_OnCycle).
Qed.

(** The Finsler triple: 0 has child 1; 1 has children 0 and 2; 2 has children 0 and 1. **)
Definition FinslerEdge : set -> set -> prop :=
  fun u w => (u = 0 /\ w = 1) \/ (u = 1 /\ w = 0) \/ (u = 1 /\ w = 2)
             \/ (u = 2 /\ w = 0) \/ (u = 2 /\ w = 1).

Theorem FinslerEdge_0_1 : FinslerEdge 0 1.
prove (0 = 0 /\ 1 = 1) \/ (0 = 1 /\ 1 = 0) \/ (0 = 1 /\ 1 = 2)
      \/ (0 = 2 /\ 1 = 0) \/ (0 = 2 /\ 1 = 1).
apply or5I1.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem FinslerEdge_1_0 : FinslerEdge 1 0.
prove (1 = 0 /\ 0 = 1) \/ (1 = 1 /\ 0 = 0) \/ (1 = 1 /\ 0 = 2)
      \/ (1 = 2 /\ 0 = 0) \/ (1 = 2 /\ 0 = 1).
apply or5I2.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem finsler_OnCycle : OnCycle 3 FinslerEdge 0.
prove exists w:set, w :e 3 /\ FinslerEdge 0 w /\ GraphReach 3 FinslerEdge w 0.
witness 1.
apply and3I.
- exact In_1_3.
- exact FinslerEdge_0_1.
- exact (GraphReach_step 3 FinslerEdge 1 1 0 (GraphReach_refl 3 FinslerEdge 1) In_0_3
           FinslerEdge_1_0).
Qed.

Theorem finsler_point_no_decoration : ~exists d:set -> set, IsDecorationFrom 3 FinslerEdge 0 d.
exact (reachable_cycle_no_decoration 3 FinslerEdge 0 0 In_0_3 (GraphReach_refl 3 FinslerEdge 0)
         finsler_OnCycle).
Qed.

Theorem finsler_no_decoration : ~exists d:set -> set, IsDecoration 3 FinslerEdge d.
exact (cycle_no_decoration 3 FinslerEdge 0 In_0_3 finsler_OnCycle).
Qed.

(** The nest: node 0 is childless; node 1 has children 0 and 1. **)
Definition NestEdge : set -> set -> prop := fun u w => (u = 1 /\ w = 0) \/ (u = 1 /\ w = 1).

Theorem NestEdge_1_1 : NestEdge 1 1.
prove (1 = 1 /\ 1 = 0) \/ (1 = 1 /\ 1 = 1).
apply orIR.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem NestEdge_not_from_0 : forall w:set, ~NestEdge 0 w.
let w.
assume H: (0 = 1 /\ w = 0) \/ (0 = 1 /\ w = 1).
apply H.
- assume H1: 0 = 1 /\ w = 0.
  exact (neq_0_1 (andEL (0 = 1) (w = 0) H1)).
- assume H1: 0 = 1 /\ w = 1.
  exact (neq_0_1 (andEL (0 = 1) (w = 1) H1)).
Qed.

Theorem nest_OnCycle : OnCycle 2 NestEdge 1.
prove exists w:set, w :e 2 /\ NestEdge 1 w /\ GraphReach 2 NestEdge w 1.
witness 1.
apply and3I.
- exact In_1_2.
- exact NestEdge_1_1.
- exact (GraphReach_refl 2 NestEdge 1).
Qed.

Theorem nest_point_no_decoration : ~exists d:set -> set, IsDecorationFrom 2 NestEdge 1 d.
exact (reachable_cycle_no_decoration 2 NestEdge 1 1 In_1_2 (GraphReach_refl 2 NestEdge 1)
         nest_OnCycle).
Qed.

Theorem nest_no_decoration : ~exists d:set -> set, IsDecoration 2 NestEdge d.
exact (cycle_no_decoration 2 NestEdge 1 In_1_2 nest_OnCycle).
Qed.

Theorem nest_blank_acc : AccNode 2 NestEdge 0.
apply (AccNode_intro 2 NestEdge 0 In_0_2).
let w.
assume _: w :e 2.
assume H: NestEdge 0 w.
apply (NestEdge_not_from_0 w H).
Qed.

(** Pointed at its childless node, the nest decorates, to the empty set. **)
Theorem nest_blank_decorates : IsDecorationFrom 2 NestEdge 0 (decorate 2 NestEdge).
exact (acc_point_decorates 2 NestEdge 0 nest_blank_acc).
Qed.

Theorem nest_blank_decoration_empty : forall d:set -> set,
  IsDecorationFrom 2 NestEdge 0 d -> d 0 = 0.
let d.
assume Hd: IsDecorationFrom 2 NestEdge 0 d.
apply Empty_eq.
let y.
assume Hy: y :e d 0.
apply (iffEL (y :e d 0) (exists w:set, w :e 2 /\ NestEdge 0 w /\ d w = y)
         (Hd 0 In_0_2 (GraphReach_refl 2 NestEdge 0) y) Hy).
let w.
assume H1: w :e 2 /\ NestEdge 0 w /\ d w = y.
apply and3E (w :e 2) (NestEdge 0 w) (d w = y) H1.
assume _: w :e 2.
assume H2: NestEdge 0 w.
assume _: d w = y.
exact (NestEdge_not_from_0 w H2).
Qed.

(** The graph with one node and no edges decorates to the empty set. **)
Definition EmptyEdge : set -> set -> prop := fun u w => False.

Theorem empty_graph_wf : WFGraph 1 EmptyEdge.
let v.
assume Hv: v :e 1.
apply (AccNode_intro 1 EmptyEdge v Hv).
let w.
assume _: w :e 1.
assume H: EmptyEdge v w.
exact (FalseE H (AccNode 1 EmptyEdge w)).
Qed.

Theorem empty_graph_decorates : IsDecoration 1 EmptyEdge (decorate 1 EmptyEdge).
exact (wf_graph_decorates 1 EmptyEdge empty_graph_wf).
Qed.

Theorem empty_graph_decoration_empty : forall d:set -> set,
  IsDecoration 1 EmptyEdge d -> d 0 = 0.
let d.
assume Hd: IsDecoration 1 EmptyEdge d.
apply Empty_eq.
let y.
assume Hy: y :e d 0.
apply (iffEL (y :e d 0) (exists w:set, w :e 1 /\ EmptyEdge 0 w /\ d w = y) (Hd 0 In_0_1 y) Hy).
let w.
assume H1: w :e 1 /\ EmptyEdge 0 w /\ d w = y.
apply and3E (w :e 1) (EmptyEdge 0 w) (d w = y) H1.
assume _: w :e 1.
assume H2: EmptyEdge 0 w.
assume _: d w = y.
exact H2.
Qed.

(** A three-node acyclic graph: 1 has child 0; 2 has children 0 and 1. **)
Definition OrdTwoEdge : set -> set -> prop :=
  fun u w => (u = 1 /\ w = 0) \/ (u = 2 /\ w = 0) \/ (u = 2 /\ w = 1).

Theorem OrdTwoEdge_1_0 : OrdTwoEdge 1 0.
prove (1 = 1 /\ 0 = 0) \/ (1 = 2 /\ 0 = 0) \/ (1 = 2 /\ 0 = 1).
apply or3I1.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem OrdTwoEdge_2_0 : OrdTwoEdge 2 0.
prove (2 = 1 /\ 0 = 0) \/ (2 = 2 /\ 0 = 0) \/ (2 = 2 /\ 0 = 1).
apply or3I2.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem OrdTwoEdge_2_1 : OrdTwoEdge 2 1.
prove (2 = 1 /\ 1 = 0) \/ (2 = 2 /\ 1 = 0) \/ (2 = 2 /\ 1 = 1).
apply or3I3.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem OrdTwoEdge_from_0 : forall w:set, ~OrdTwoEdge 0 w.
let w.
assume H: (0 = 1 /\ w = 0) \/ (0 = 2 /\ w = 0) \/ (0 = 2 /\ w = 1).
apply (or3E (0 = 1 /\ w = 0) (0 = 2 /\ w = 0) (0 = 2 /\ w = 1) H).
- assume H1: 0 = 1 /\ w = 0.
  exact (neq_0_1 (andEL (0 = 1) (w = 0) H1)).
- assume H1: 0 = 2 /\ w = 0.
  exact (neq_0_2 (andEL (0 = 2) (w = 0) H1)).
- assume H1: 0 = 2 /\ w = 1.
  exact (neq_0_2 (andEL (0 = 2) (w = 1) H1)).
Qed.

Theorem OrdTwoEdge_from_1 : forall w:set, OrdTwoEdge 1 w -> w = 0.
let w.
assume H: (1 = 1 /\ w = 0) \/ (1 = 2 /\ w = 0) \/ (1 = 2 /\ w = 1).
apply (or3E (1 = 1 /\ w = 0) (1 = 2 /\ w = 0) (1 = 2 /\ w = 1) H).
- assume H1: 1 = 1 /\ w = 0.
  exact (andER (1 = 1) (w = 0) H1).
- assume H1: 1 = 2 /\ w = 0.
  exact (FalseE (neq_1_2 (andEL (1 = 2) (w = 0) H1)) (w = 0)).
- assume H1: 1 = 2 /\ w = 1.
  exact (FalseE (neq_1_2 (andEL (1 = 2) (w = 1) H1)) (w = 0)).
Qed.

Theorem OrdTwoEdge_from_2 : forall w:set, OrdTwoEdge 2 w -> w = 0 \/ w = 1.
let w.
assume H: (2 = 1 /\ w = 0) \/ (2 = 2 /\ w = 0) \/ (2 = 2 /\ w = 1).
apply (or3E (2 = 1 /\ w = 0) (2 = 2 /\ w = 0) (2 = 2 /\ w = 1) H).
- assume H1: 2 = 1 /\ w = 0.
  exact (FalseE (neq_2_1 (andEL (2 = 1) (w = 0) H1)) (w = 0 \/ w = 1)).
- assume H1: 2 = 2 /\ w = 0.
  apply orIL.
  exact (andER (2 = 2) (w = 0) H1).
- assume H1: 2 = 2 /\ w = 1.
  apply orIR.
  exact (andER (2 = 2) (w = 1) H1).
Qed.

Theorem ordTwo_acc_0 : AccNode 3 OrdTwoEdge 0.
apply (AccNode_intro 3 OrdTwoEdge 0 In_0_3).
let w.
assume _: w :e 3.
assume H: OrdTwoEdge 0 w.
exact (FalseE (OrdTwoEdge_from_0 w H) (AccNode 3 OrdTwoEdge w)).
Qed.

Theorem ordTwo_acc_1 : AccNode 3 OrdTwoEdge 1.
apply (AccNode_intro 3 OrdTwoEdge 1 In_1_3).
let w.
assume _: w :e 3.
assume H: OrdTwoEdge 1 w.
rewrite (OrdTwoEdge_from_1 w H).
exact ordTwo_acc_0.
Qed.

Theorem ordTwo_acc_2 : AccNode 3 OrdTwoEdge 2.
apply (AccNode_intro 3 OrdTwoEdge 2 In_2_3).
let w.
assume _: w :e 3.
assume H: OrdTwoEdge 2 w.
apply (OrdTwoEdge_from_2 w H).
- assume Hw: w = 0.
  rewrite Hw.
  exact ordTwo_acc_0.
- assume Hw: w = 1.
  rewrite Hw.
  exact ordTwo_acc_1.
Qed.

Theorem ordTwo_wf : WFGraph 3 OrdTwoEdge.
let v.
assume Hv: v :e 3.
exact (cases_3 v Hv (fun v => AccNode 3 OrdTwoEdge v) ordTwo_acc_0 ordTwo_acc_1 ordTwo_acc_2).
Qed.

Theorem ordTwo_decorates : IsDecoration 3 OrdTwoEdge (decorate 3 OrdTwoEdge).
exact (wf_graph_decorates 3 OrdTwoEdge ordTwo_wf).
Qed.

(** Every decoration of the three-node graph sends 0, 1 and 2 to the ordinals 0, 1 and 2. **)
Theorem ordTwo_decoration_values : forall d:set -> set, IsDecoration 3 OrdTwoEdge d ->
  d 0 = 0 /\ d 1 = 1 /\ d 2 = 2.
let d.
assume Hd: IsDecoration 3 OrdTwoEdge d.
claim L0: d 0 = 0.
{ apply Empty_eq.
  let y.
  assume Hy: y :e d 0.
  apply (iffEL (y :e d 0) (exists w:set, w :e 3 /\ OrdTwoEdge 0 w /\ d w = y)
           (Hd 0 In_0_3 y) Hy).
  let w.
  assume H1: w :e 3 /\ OrdTwoEdge 0 w /\ d w = y.
  apply and3E (w :e 3) (OrdTwoEdge 0 w) (d w = y) H1.
  assume _: w :e 3.
  assume H2: OrdTwoEdge 0 w.
  assume _: d w = y.
  exact (OrdTwoEdge_from_0 w H2).
}
claim L1s: d 1 = {0}.
{ apply set_ext.
  - let y.
    assume Hy: y :e d 1.
    apply (iffEL (y :e d 1) (exists w:set, w :e 3 /\ OrdTwoEdge 1 w /\ d w = y)
             (Hd 1 In_1_3 y) Hy).
    let w.
    assume H1: w :e 3 /\ OrdTwoEdge 1 w /\ d w = y.
    apply and3E (w :e 3) (OrdTwoEdge 1 w) (d w = y) H1.
    assume _: w :e 3.
    assume H2: OrdTwoEdge 1 w.
    assume H3: d w = y.
    rewrite <- H3.
    rewrite (OrdTwoEdge_from_1 w H2).
    rewrite L0.
    exact (SingI 0).
  - let y.
    assume Hy: y :e {0}.
    apply (iffER (y :e d 1) (exists w:set, w :e 3 /\ OrdTwoEdge 1 w /\ d w = y)
             (Hd 1 In_1_3 y)).
    witness 0.
    apply and3I.
    + exact In_0_3.
    + exact OrdTwoEdge_1_0.
    + rewrite L0.
      symmetry.
      exact (SingE 0 y Hy).
}
claim L1: d 1 = 1.
{ apply (eq_i_tra (d 1) {0} 1 L1s).
  symmetry.
  exact eq_1_Sing0.
}
claim L2s: d 2 = {0,1}.
{ apply set_ext.
  - let y.
    assume Hy: y :e d 2.
    apply (iffEL (y :e d 2) (exists w:set, w :e 3 /\ OrdTwoEdge 2 w /\ d w = y)
             (Hd 2 In_2_3 y) Hy).
    let w.
    assume H1: w :e 3 /\ OrdTwoEdge 2 w /\ d w = y.
    apply and3E (w :e 3) (OrdTwoEdge 2 w) (d w = y) H1.
    assume _: w :e 3.
    assume H2: OrdTwoEdge 2 w.
    assume H3: d w = y.
    rewrite <- H3.
    apply (OrdTwoEdge_from_2 w H2).
    + assume Hw: w = 0.
      rewrite Hw.
      rewrite L0.
      exact (UPairI1 0 1).
    + assume Hw: w = 1.
      rewrite Hw.
      rewrite L1.
      exact (UPairI2 0 1).
  - let y.
    assume Hy: y :e {0,1}.
    apply (iffER (y :e d 2) (exists w:set, w :e 3 /\ OrdTwoEdge 2 w /\ d w = y)
             (Hd 2 In_2_3 y)).
    apply (UPairE y 0 1 Hy).
    + assume Hy0: y = 0.
      witness 0.
      apply and3I.
      * exact In_0_3.
      * exact OrdTwoEdge_2_0.
      * rewrite L0. symmetry. exact Hy0.
    + assume Hy1: y = 1.
      witness 1.
      apply and3I.
      * exact In_1_3.
      * exact OrdTwoEdge_2_1.
      * rewrite L1. symmetry. exact Hy1.
}
claim L2: d 2 = 2.
{ apply (eq_i_tra (d 2) {0,1} 2 L2s).
  symmetry.
  exact eq_2_UPair01.
}
apply and3I.
- exact L0.
- exact L1.
- exact L2.
Qed.

(** The point 2 of the three-node graph decorates to the set {0, {0}}. **)
Theorem ordTwo_point_decoration : decorate 3 OrdTwoEdge 2 = {0, {0}}.
rewrite <- eq_1_Sing0.
rewrite <- eq_2_UPair01.
apply and3E (decorate 3 OrdTwoEdge 0 = 0) (decorate 3 OrdTwoEdge 1 = 1)
  (decorate 3 OrdTwoEdge 2 = 2) (ordTwo_decoration_values (decorate 3 OrdTwoEdge) ordTwo_decorates).
assume _: decorate 3 OrdTwoEdge 0 = 0.
assume _: decorate 3 OrdTwoEdge 1 = 1.
assume H2: decorate 3 OrdTwoEdge 2 = 2.
exact H2.
Qed.

(** Part 5. Bisimilarity. **)

(** Bisimilarity of pointed graphs. **)
Definition IsBisim : set -> (set -> set -> prop) -> set -> (set -> set -> prop) ->
  (set -> set -> prop) -> prop :=
  fun n E m F R => forall u :e n, forall v :e m, R u v ->
     (forall u' :e n, E u u' -> exists v':set, v' :e m /\ F v v' /\ R u' v')
  /\ (forall v' :e m, F v v' -> exists u':set, u' :e n /\ E u u' /\ R u' v').

Definition Bisimilar : set -> (set -> set -> prop) -> set -> set -> (set -> set -> prop) -> set ->
  prop :=
  fun n E p m F q => p :e n /\ q :e m /\ exists R:set -> set -> prop, IsBisim n E m F R /\ R p q.

Theorem Bisimilar_I : forall n:set, forall E:set -> set -> prop, forall p m:set,
  forall F:set -> set -> prop, forall q:set, forall R:set -> set -> prop,
  p :e n -> q :e m -> IsBisim n E m F R -> R p q -> Bisimilar n E p m F q.
let n E p m F q R.
assume Hp: p :e n.
assume Hq: q :e m.
assume HR: IsBisim n E m F R.
assume Hpq: R p q.
prove p :e n /\ q :e m /\ exists R:set -> set -> prop, IsBisim n E m F R /\ R p q.
apply and3I.
- exact Hp.
- exact Hq.
- witness R.
  apply andI.
  + exact HR.
  + exact Hpq.
Qed.

Theorem Bisimilar_E : forall n:set, forall E:set -> set -> prop, forall p m:set,
  forall F:set -> set -> prop, forall q:set, Bisimilar n E p m F q ->
  forall P:prop, (p :e n -> q :e m -> forall R:set -> set -> prop,
                  IsBisim n E m F R -> R p q -> P) -> P.
let n E p m F q.
assume H: p :e n /\ q :e m /\ exists R:set -> set -> prop, IsBisim n E m F R /\ R p q.
let P.
assume HP: p :e n -> q :e m -> forall R:set -> set -> prop, IsBisim n E m F R -> R p q -> P.
apply and3E (p :e n) (q :e m) (exists R:set -> set -> prop, IsBisim n E m F R /\ R p q) H.
assume Hp: p :e n.
assume Hq: q :e m.
assume HR: exists R:set -> set -> prop, IsBisim n E m F R /\ R p q.
apply HR.
let R.
assume HR2: IsBisim n E m F R /\ R p q.
apply HR2.
assume HB: IsBisim n E m F R.
assume Hpq: R p q.
exact (HP Hp Hq R HB Hpq).
Qed.

Theorem Bisimilar_refl : forall n:set, forall E:set -> set -> prop, forall p :e n,
  Bisimilar n E p n E p.
let n E p.
assume Hp: p :e n.
apply (Bisimilar_I n E p n E p (fun u v => u = v) Hp Hp).
- let u.
  assume Hu: u :e n.
  let v.
  assume Hv: v :e n.
  assume Huv: u = v.
  apply andI.
  + let u'.
    assume Hu': u' :e n.
    assume Huu': E u u'.
    witness u'.
    apply and3I.
    * exact Hu'.
    * rewrite <- Huv. exact Huu'.
    * reflexivity.
  + let v'.
    assume Hv': v' :e n.
    assume Hvv': E v v'.
    witness v'.
    apply and3I.
    * exact Hv'.
    * rewrite Huv. exact Hvv'.
    * reflexivity.
- prove p = p.
  reflexivity.
Qed.

Theorem Bisimilar_sym : forall n:set, forall E:set -> set -> prop, forall p m:set,
  forall F:set -> set -> prop, forall q:set,
  Bisimilar n E p m F q -> Bisimilar m F q n E p.
let n E p m F q.
assume H: Bisimilar n E p m F q.
apply (Bisimilar_E n E p m F q H).
assume Hp: p :e n.
assume Hq: q :e m.
let R.
assume HR: IsBisim n E m F R.
assume Hpq: R p q.
apply (Bisimilar_I m F q n E p (fun v u => R u v) Hq Hp).
- let v.
  assume Hv: v :e m.
  let u.
  assume Hu: u :e n.
  assume Hvu: R u v.
  apply (HR u Hu v Hv Hvu).
  assume Hforth: forall u' :e n, E u u' -> exists v':set, v' :e m /\ F v v' /\ R u' v'.
  assume Hback: forall v' :e m, F v v' -> exists u':set, u' :e n /\ E u u' /\ R u' v'.
  apply andI.
  + exact Hback.
  + exact Hforth.
- exact Hpq.
Qed.

Theorem Bisimilar_trans : forall n:set, forall E:set -> set -> prop, forall p m:set,
  forall F:set -> set -> prop, forall q k:set, forall G:set -> set -> prop, forall r:set,
  Bisimilar n E p m F q -> Bisimilar m F q k G r -> Bisimilar n E p k G r.
let n E p m F q k G r.
assume H1: Bisimilar n E p m F q.
assume H2: Bisimilar m F q k G r.
apply (Bisimilar_E n E p m F q H1).
assume Hp: p :e n.
assume Hq: q :e m.
let R.
assume HR: IsBisim n E m F R.
assume Hpq: R p q.
apply (Bisimilar_E m F q k G r H2).
assume _: q :e m.
assume Hr: r :e k.
let S.
assume HS: IsBisim m F k G S.
assume Hqr: S q r.
apply (Bisimilar_I n E p k G r (fun u w => exists v:set, v :e m /\ R u v /\ S v w) Hp Hr).
- let u.
  assume Hu: u :e n.
  let w.
  assume Hw: w :e k.
  assume Huw: exists v:set, v :e m /\ R u v /\ S v w.
  apply Huw.
  let v.
  assume Hv3: v :e m /\ R u v /\ S v w.
  apply and3E (v :e m) (R u v) (S v w) Hv3.
  assume Hv: v :e m.
  assume Huv: R u v.
  assume Hvw: S v w.
  apply (HR u Hu v Hv Huv).
  assume HRf: forall u' :e n, E u u' -> exists v':set, v' :e m /\ F v v' /\ R u' v'.
  assume HRb: forall v' :e m, F v v' -> exists u':set, u' :e n /\ E u u' /\ R u' v'.
  apply (HS v Hv w Hw Hvw).
  assume HSf: forall v' :e m, F v v' -> exists w':set, w' :e k /\ G w w' /\ S v' w'.
  assume HSb: forall w' :e k, G w w' -> exists v':set, v' :e m /\ F v v' /\ S v' w'.
  apply andI.
  + let u'.
    assume Hu': u' :e n.
    assume Huu': E u u'.
    apply (HRf u' Hu' Huu').
    let v'.
    assume H3: v' :e m /\ F v v' /\ R u' v'.
    apply and3E (v' :e m) (F v v') (R u' v') H3.
    assume Hv': v' :e m.
    assume Hvv': F v v'.
    assume Hu'v': R u' v'.
    apply (HSf v' Hv' Hvv').
    let w'.
    assume H4: w' :e k /\ G w w' /\ S v' w'.
    apply and3E (w' :e k) (G w w') (S v' w') H4.
    assume Hw': w' :e k.
    assume Hww': G w w'.
    assume Hv'w': S v' w'.
    witness w'.
    apply and3I.
    * exact Hw'.
    * exact Hww'.
    * witness v'.
      apply and3I.
      { exact Hv'. }
      { exact Hu'v'. }
      { exact Hv'w'. }
  + let w'.
    assume Hw': w' :e k.
    assume Hww': G w w'.
    apply (HSb w' Hw' Hww').
    let v'.
    assume H3: v' :e m /\ F v v' /\ S v' w'.
    apply and3E (v' :e m) (F v v') (S v' w') H3.
    assume Hv': v' :e m.
    assume Hvv': F v v'.
    assume Hv'w': S v' w'.
    apply (HRb v' Hv' Hvv').
    let u'.
    assume H4: u' :e n /\ E u u' /\ R u' v'.
    apply and3E (u' :e n) (E u u') (R u' v') H4.
    assume Hu': u' :e n.
    assume Huu': E u u'.
    assume Hu'v': R u' v'.
    witness u'.
    apply and3I.
    * exact Hu'.
    * exact Huu'.
    * witness v'.
      apply and3I.
      { exact Hv'. }
      { exact Hu'v'. }
      { exact Hv'w'. }
- prove exists v:set, v :e m /\ R p v /\ S v r.
  witness q.
  apply and3I.
  + exact Hq.
  + exact Hpq.
  + exact Hqr.
Qed.

(** When every node of either graph has a child, the total relation is a bisimulation. **)
Theorem total_IsBisim : forall n:set, forall E:set -> set -> prop, forall m:set,
  forall F:set -> set -> prop,
  (forall u :e n, exists u':set, u' :e n /\ E u u') ->
  (forall v :e m, exists v':set, v' :e m /\ F v v') ->
  IsBisim n E m F (fun _ _ => True).
let n E m F.
assume HE: forall u :e n, exists u':set, u' :e n /\ E u u'.
assume HF: forall v :e m, exists v':set, v' :e m /\ F v v'.
let u.
assume Hu: u :e n.
let v.
assume Hv: v :e m.
assume _: True.
apply andI.
- let u'.
  assume _: u' :e n.
  assume _: E u u'.
  apply (HF v Hv).
  let v'.
  assume H1: v' :e m /\ F v v'.
  apply H1.
  assume Hv': v' :e m.
  assume Hvv': F v v'.
  witness v'.
  apply and3I.
  + exact Hv'.
  + exact Hvv'.
  + exact TrueI.
- let v'.
  assume _: v' :e m.
  assume _: F v v'.
  apply (HE u Hu).
  let u'.
  assume H1: u' :e n /\ E u u'.
  apply H1.
  assume Hu': u' :e n.
  assume Huu': E u u'.
  witness u'.
  apply and3I.
  + exact Hu'.
  + exact Huu'.
  + exact TrueI.
Qed.

Theorem loop_has_child : forall u :e 1, exists u':set, u' :e 1 /\ LoopEdge u u'.
let u.
assume _: u :e 1.
witness 0.
apply andI.
- exact In_0_1.
- exact TrueI.
Qed.

Theorem cycle_has_child : forall v :e 2, exists v':set, v' :e 2 /\ CycleEdge v v'.
let v.
assume Hv: v :e 2.
apply (cases_2 v Hv (fun v => exists v':set, v' :e 2 /\ CycleEdge v v')).
- prove exists v':set, v' :e 2 /\ CycleEdge 0 v'.
  witness 1.
  apply andI.
  + exact In_1_2.
  + exact CycleEdge_0_1.
- prove exists v':set, v' :e 2 /\ CycleEdge 1 v'.
  witness 0.
  apply andI.
  + exact In_0_2.
  + exact CycleEdge_1_0.
Qed.

(** The one-node loop and the two-node cycle are bisimilar, at every node of the cycle. **)
Theorem loop_bisim_cycle : forall v :e 2, Bisimilar 1 LoopEdge 0 2 CycleEdge v.
let v.
assume Hv: v :e 2.
exact (Bisimilar_I 1 LoopEdge 0 2 CycleEdge v (fun _ _ => True) In_0_1 Hv
         (total_IsBisim 1 LoopEdge 2 CycleEdge loop_has_child cycle_has_child) TrueI).
Qed.

Theorem cycle_nodes_bisim : Bisimilar 2 CycleEdge 0 2 CycleEdge 1.
exact (Bisimilar_I 2 CycleEdge 0 2 CycleEdge 1 (fun _ _ => True) In_0_2 In_1_2
         (total_IsBisim 2 CycleEdge 2 CycleEdge cycle_has_child cycle_has_child) TrueI).
Qed.

(** Part 6. Graphs as sets and interpreted membership. **)

(** Graphs as sets. A code packs the nodes, the set of edge pairs and the point. Pairs are the
    library's setsum pairs, with projections proj0 and proj1. **)
Definition GraphCode : set -> (set -> set -> prop) -> set -> set :=
  fun n E p => setsum (setsum n {z :e n :*: n | E (proj0 z) (proj1 z)}) p.

Definition GNodes : set -> set := fun g => proj0 (proj0 g).
Definition GEdges : set -> set := fun g => proj1 (proj0 g).
Definition GPoint : set -> set := fun g => proj1 g.
Definition GEdge : set -> set -> set -> prop := fun g u w => setsum u w :e GEdges g.

Theorem GNodes_code : forall n:set, forall E:set -> set -> prop, forall p:set,
  GNodes (GraphCode n E p) = n.
let n E p.
prove proj0 (proj0 (setsum (setsum n {z :e n :*: n | E (proj0 z) (proj1 z)}) p)) = n.
rewrite proj0_pair_eq.
exact (proj0_pair_eq n {z :e n :*: n | E (proj0 z) (proj1 z)}).
Qed.

Theorem GPoint_code : forall n:set, forall E:set -> set -> prop, forall p:set,
  GPoint (GraphCode n E p) = p.
let n E p.
exact (proj1_pair_eq (setsum n {z :e n :*: n | E (proj0 z) (proj1 z)}) p).
Qed.

Theorem GEdge_code : forall n:set, forall E:set -> set -> prop, forall p:set,
  forall u :e n, forall w :e n, GEdge (GraphCode n E p) u w <-> E u w.
let n E p u.
assume Hu: u :e n.
let w.
assume Hw: w :e n.
claim LE: GEdges (GraphCode n E p) = {z :e n :*: n | E (proj0 z) (proj1 z)}.
{ prove proj1 (proj0 (setsum (setsum n {z :e n :*: n | E (proj0 z) (proj1 z)}) p))
        = {z :e n :*: n | E (proj0 z) (proj1 z)}.
  rewrite proj0_pair_eq.
  exact (proj1_pair_eq n {z :e n :*: n | E (proj0 z) (proj1 z)}).
}
prove setsum u w :e GEdges (GraphCode n E p) <-> E u w.
rewrite LE.
apply iffI.
- assume H: setsum u w :e {z :e n :*: n | E (proj0 z) (proj1 z)}.
  claim L2: E (proj0 (setsum u w)) (proj1 (setsum u w)).
  { exact (SepE2 (n :*: n) (fun z => E (proj0 z) (proj1 z)) (setsum u w) H). }
  rewrite <- (proj0_pair_eq u w).
  rewrite <- (proj1_pair_eq u w) at 2.
  exact L2.
- assume H: E u w.
  apply (SepI (n :*: n) (fun z => E (proj0 z) (proj1 z)) (setsum u w) (pair_setprod n n u Hu w Hw)).
  prove E (proj0 (setsum u w)) (proj1 (setsum u w)).
  rewrite (proj0_pair_eq u w).
  rewrite (proj1_pair_eq u w).
  exact H.
Qed.

(** A code and the graph it packs are bisimilar at every node. **)
Theorem code_bisim_graph : forall n:set, forall E:set -> set -> prop, forall p v:set,
  v :e n -> Bisimilar (GNodes (GraphCode n E p)) (GEdge (GraphCode n E p)) v n E v.
let n E p v.
assume Hv: v :e n.
rewrite (GNodes_code n E p).
apply (Bisimilar_I n (GEdge (GraphCode n E p)) v n E v (fun u w => u = w) Hv Hv).
- let u.
  assume Hu: u :e n.
  let w.
  assume Hw: w :e n.
  assume Huw: u = w.
  apply andI.
  + let u'.
    assume Hu': u' :e n.
    assume Huu': GEdge (GraphCode n E p) u u'.
    witness u'.
    apply and3I.
    * exact Hu'.
    * rewrite <- Huw.
      exact (iffEL (GEdge (GraphCode n E p) u u') (E u u') (GEdge_code n E p u Hu u' Hu') Huu').
    * reflexivity.
  + let w'.
    assume Hw': w' :e n.
    assume Hww': E w w'.
    witness w'.
    apply and3I.
    * exact Hw'.
    * apply (iffER (GEdge (GraphCode n E p) u w') (E u w') (GEdge_code n E p u Hu w' Hw')).
      rewrite Huw.
      exact Hww'.
    * reflexivity.
- prove v = v.
  reflexivity.
Qed.

(** Bisimilarity of codes, and Aczel's interpreted membership: h is an interpreted member of
    g when h is bisimilar to g re-pointed at a child of its point. **)
Definition BisimCode : set -> set -> prop :=
  fun h g => Bisimilar (GNodes h) (GEdge h) (GPoint h) (GNodes g) (GEdge g) (GPoint g).

Definition InStar : set -> set -> prop :=
  fun h g => exists q:set, q :e GNodes g /\ GEdge g (GPoint g) q
             /\ Bisimilar (GNodes h) (GEdge h) (GPoint h) (GNodes g) (GEdge g) q.

Theorem InStar_bisim_left : forall z z' g:set, BisimCode z z' -> InStar z g -> InStar z' g.
let z z' g.
assume Hzz': BisimCode z z'.
assume H: InStar z g.
apply H.
let q.
assume H1: q :e GNodes g /\ GEdge g (GPoint g) q
           /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q.
apply and3E (q :e GNodes g) (GEdge g (GPoint g) q)
  (Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q) H1.
assume Hq: q :e GNodes g.
assume Hpq: GEdge g (GPoint g) q.
assume Hb: Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q.
prove exists q:set, q :e GNodes g /\ GEdge g (GPoint g) q
             /\ Bisimilar (GNodes z') (GEdge z') (GPoint z') (GNodes g) (GEdge g) q.
witness q.
apply and3I.
- exact Hq.
- exact Hpq.
- exact (Bisimilar_trans (GNodes z') (GEdge z') (GPoint z') (GNodes z) (GEdge z) (GPoint z)
           (GNodes g) (GEdge g) q
           (Bisimilar_sym (GNodes z) (GEdge z) (GPoint z) (GNodes z') (GEdge z') (GPoint z') Hzz')
           Hb).
Qed.

Theorem InStar_bisim_right : forall z g g':set, BisimCode g g' -> InStar z g -> InStar z g'.
let z g g'.
assume Hgg': BisimCode g g'.
assume H: InStar z g.
apply H.
let q.
assume H1: q :e GNodes g /\ GEdge g (GPoint g) q
           /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q.
apply and3E (q :e GNodes g) (GEdge g (GPoint g) q)
  (Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q) H1.
assume Hq: q :e GNodes g.
assume Hpq: GEdge g (GPoint g) q.
assume Hb: Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q.
apply (Bisimilar_E (GNodes g) (GEdge g) (GPoint g) (GNodes g') (GEdge g') (GPoint g') Hgg').
assume Hp: GPoint g :e GNodes g.
assume Hp': GPoint g' :e GNodes g'.
let R.
assume HR: IsBisim (GNodes g) (GEdge g) (GNodes g') (GEdge g') R.
assume Hpp': R (GPoint g) (GPoint g').
apply (HR (GPoint g) Hp (GPoint g') Hp' Hpp').
assume Hforth: forall u' :e GNodes g, GEdge g (GPoint g) u' ->
  exists v':set, v' :e GNodes g' /\ GEdge g' (GPoint g') v' /\ R u' v'.
assume _: forall v' :e GNodes g', GEdge g' (GPoint g') v' ->
  exists u':set, u' :e GNodes g /\ GEdge g (GPoint g) u' /\ R u' v'.
apply (Hforth q Hq Hpq).
let q'.
assume H2: q' :e GNodes g' /\ GEdge g' (GPoint g') q' /\ R q q'.
apply and3E (q' :e GNodes g') (GEdge g' (GPoint g') q') (R q q') H2.
assume Hq': q' :e GNodes g'.
assume Hpq': GEdge g' (GPoint g') q'.
assume Hqq': R q q'.
prove exists q:set, q :e GNodes g' /\ GEdge g' (GPoint g') q
             /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes g') (GEdge g') q.
witness q'.
apply and3I.
- exact Hq'.
- exact Hpq'.
- exact (Bisimilar_trans (GNodes z) (GEdge z) (GPoint z) (GNodes g) (GEdge g) q
           (GNodes g') (GEdge g') q' Hb
           (Bisimilar_I (GNodes g) (GEdge g) q (GNodes g') (GEdge g') q' R Hq Hq' HR Hqq')).
Qed.

(** The code of the one-node loop. **)
Definition OmegaCode : set := GraphCode 1 LoopEdge 0.

Theorem OmegaCode_nodes : GNodes OmegaCode = 1.
exact (GNodes_code 1 LoopEdge 0).
Qed.

Theorem OmegaCode_point : GPoint OmegaCode = 0.
exact (GPoint_code 1 LoopEdge 0).
Qed.

Theorem OmegaCode_edge : GEdge OmegaCode 0 0.
exact (iffER (GEdge (GraphCode 1 LoopEdge 0) 0 0) (LoopEdge 0 0)
         (GEdge_code 1 LoopEdge 0 0 In_0_1 0 In_0_1) TrueI).
Qed.

Theorem In_1_eq_0 : forall q :e 1, q = 0.
let q.
assume Hq: q :e 1.
apply (cases_1 q Hq (fun q => q = 0)).
prove 0 = 0.
reflexivity.
Qed.

(** The loop is a Quine atom for interpreted membership: its interpreted members are exactly
    the codes bisimilar to it, and it is one of them. **)
Theorem OmegaCode_members : forall z:set, InStar z OmegaCode <-> BisimCode z OmegaCode.
let z.
apply iffI.
- assume H: InStar z OmegaCode.
  apply H.
  let q.
  assume H1: q :e GNodes OmegaCode /\ GEdge OmegaCode (GPoint OmegaCode) q
             /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes OmegaCode) (GEdge OmegaCode) q.
  apply and3E (q :e GNodes OmegaCode) (GEdge OmegaCode (GPoint OmegaCode) q)
    (Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes OmegaCode) (GEdge OmegaCode) q) H1.
  assume Hq: q :e GNodes OmegaCode.
  assume _: GEdge OmegaCode (GPoint OmegaCode) q.
  assume Hb: Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes OmegaCode) (GEdge OmegaCode) q.
  claim Lq: q = GPoint OmegaCode.
  { rewrite OmegaCode_point.
    apply In_1_eq_0.
    rewrite <- OmegaCode_nodes.
    exact Hq.
  }
  prove Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes OmegaCode) (GEdge OmegaCode)
          (GPoint OmegaCode).
  rewrite <- Lq.
  exact Hb.
- assume H: BisimCode z OmegaCode.
  prove exists q:set, q :e GNodes OmegaCode /\ GEdge OmegaCode (GPoint OmegaCode) q
             /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes OmegaCode) (GEdge OmegaCode) q.
  witness (GPoint OmegaCode).
  apply and3I.
  + rewrite OmegaCode_point.
    rewrite OmegaCode_nodes.
    exact In_0_1.
  + rewrite OmegaCode_point.
    exact OmegaCode_edge.
  + exact H.
Qed.

Theorem OmegaCode_InStar_self : InStar OmegaCode OmegaCode.
apply (iffER (InStar OmegaCode OmegaCode) (BisimCode OmegaCode OmegaCode)
         (OmegaCode_members OmegaCode)).
prove Bisimilar (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode)
        (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode).
apply Bisimilar_refl.
rewrite OmegaCode_point.
rewrite OmegaCode_nodes.
exact In_0_1.
Qed.

(** Native membership against interpreted membership, in one checker and on one carrier:
    native membership has no Quine atom; interpreted membership has one, up to bisimilarity. **)
Theorem native_no_quine_atom : ~exists q:set, forall z:set, z :e q <-> z = q.
assume H: exists q:set, forall z:set, z :e q <-> z = q.
apply H.
let q.
assume Hq: forall z:set, z :e q <-> z = q.
apply (no_self_member q).
apply (iffER (q :e q) (q = q) (Hq q)).
reflexivity.
Qed.

Theorem interpreted_quine_atom : exists q:set, forall z:set, InStar z q <-> BisimCode z q.
witness OmegaCode.
exact OmegaCode_members.
Qed.

Theorem native_vs_interpreted :
  (~exists q:set, forall z:set, z :e q <-> z = q)
  /\ (exists q:set, InStar q q /\ forall z:set, InStar z q <-> BisimCode z q).
apply andI.
- exact native_no_quine_atom.
- witness OmegaCode.
  apply andI.
  + exact OmegaCode_InStar_self.
  + exact OmegaCode_members.
Qed.

(** The code of the two-node cycle: bisimilar to the loop's code, a different set, and also a
    Quine atom of interpreted membership up to bisimilarity. **)
Definition CycleCode : set := GraphCode 2 CycleEdge 0.

Theorem CycleCode_nodes : GNodes CycleCode = 2.
exact (GNodes_code 2 CycleEdge 0).
Qed.

Theorem CycleCode_point : GPoint CycleCode = 0.
exact (GPoint_code 2 CycleEdge 0).
Qed.

Theorem CycleCode_at_bisim_Omega : forall v :e 2,
  Bisimilar (GNodes CycleCode) (GEdge CycleCode) v
            (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode).
let v.
assume Hv: v :e 2.
claim L1: Bisimilar (GNodes CycleCode) (GEdge CycleCode) v 2 CycleEdge v.
{ exact (code_bisim_graph 2 CycleEdge 0 v Hv). }
claim L2: Bisimilar 2 CycleEdge v 1 LoopEdge 0.
{ exact (Bisimilar_sym 1 LoopEdge 0 2 CycleEdge v (loop_bisim_cycle v Hv)). }
claim L3: Bisimilar 1 LoopEdge 0 (GNodes OmegaCode) (GEdge OmegaCode) 0.
{ exact (Bisimilar_sym (GNodes OmegaCode) (GEdge OmegaCode) 0 1 LoopEdge 0
           (code_bisim_graph 1 LoopEdge 0 0 In_0_1)). }
rewrite OmegaCode_point.
exact (Bisimilar_trans (GNodes CycleCode) (GEdge CycleCode) v 2 CycleEdge v
         (GNodes OmegaCode) (GEdge OmegaCode) 0 L1
         (Bisimilar_trans 2 CycleEdge v 1 LoopEdge 0 (GNodes OmegaCode) (GEdge OmegaCode) 0 L2 L3)).
Qed.

Theorem CycleCode_bisim_OmegaCode : BisimCode CycleCode OmegaCode.
prove Bisimilar (GNodes CycleCode) (GEdge CycleCode) (GPoint CycleCode)
        (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode).
rewrite CycleCode_point.
exact (CycleCode_at_bisim_Omega 0 In_0_2).
Qed.

Theorem CycleCode_neq_OmegaCode : CycleCode <> OmegaCode.
assume H: CycleCode = OmegaCode.
apply neq_2_1.
rewrite <- CycleCode_nodes.
rewrite <- OmegaCode_nodes.
rewrite H.
reflexivity.
Qed.

Theorem CycleCode_members : forall z:set, InStar z CycleCode <-> BisimCode z OmegaCode.
let z.
apply iffI.
- assume H: InStar z CycleCode.
  apply H.
  let q.
  assume H1: q :e GNodes CycleCode /\ GEdge CycleCode (GPoint CycleCode) q
             /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes CycleCode) (GEdge CycleCode) q.
  apply and3E (q :e GNodes CycleCode) (GEdge CycleCode (GPoint CycleCode) q)
    (Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes CycleCode) (GEdge CycleCode) q) H1.
  assume Hq: q :e GNodes CycleCode.
  assume _: GEdge CycleCode (GPoint CycleCode) q.
  assume Hb: Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes CycleCode) (GEdge CycleCode) q.
  claim Hq2: q :e 2.
  { rewrite <- CycleCode_nodes. exact Hq. }
  exact (Bisimilar_trans (GNodes z) (GEdge z) (GPoint z) (GNodes CycleCode) (GEdge CycleCode) q
           (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode) Hb
           (CycleCode_at_bisim_Omega q Hq2)).
- assume H: BisimCode z OmegaCode.
  prove exists q:set, q :e GNodes CycleCode /\ GEdge CycleCode (GPoint CycleCode) q
             /\ Bisimilar (GNodes z) (GEdge z) (GPoint z) (GNodes CycleCode) (GEdge CycleCode) q.
  witness 1.
  apply and3I.
  + rewrite CycleCode_nodes. exact In_1_2.
  + rewrite CycleCode_point.
    exact (iffER (GEdge (GraphCode 2 CycleEdge 0) 0 1) (CycleEdge 0 1)
             (GEdge_code 2 CycleEdge 0 0 In_0_2 1 In_1_2) CycleEdge_0_1).
  + exact (Bisimilar_trans (GNodes z) (GEdge z) (GPoint z)
             (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode)
             (GNodes CycleCode) (GEdge CycleCode) 1 H
             (Bisimilar_sym (GNodes CycleCode) (GEdge CycleCode) 1
                (GNodes OmegaCode) (GEdge OmegaCode) (GPoint OmegaCode)
                (CycleCode_at_bisim_Omega 1 In_1_2))).
Qed.

(** The other cyclic graphs of the menu, against the loop. Every node of the Scott pair and of
    the Finsler triple is bisimilar to the loop; the two nodes of the nest are not bisimilar. **)
Theorem scott_has_child : forall v :e 2, exists v':set, v' :e 2 /\ ScottEdge v v'.
let v.
assume Hv: v :e 2.
apply (cases_2 v Hv (fun v => exists v':set, v' :e 2 /\ ScottEdge v v')).
- prove exists v':set, v' :e 2 /\ ScottEdge 0 v'.
  witness 0.
  apply andI.
  + exact In_0_2.
  + exact ScottEdge_0_0.
- prove exists v':set, v' :e 2 /\ ScottEdge 1 v'.
  witness 0.
  apply andI.
  + exact In_0_2.
  + exact ScottEdge_1_0.
Qed.

Theorem scott_bisim_loop : forall v :e 2, Bisimilar 2 ScottEdge v 1 LoopEdge 0.
let v.
assume Hv: v :e 2.
exact (Bisimilar_I 2 ScottEdge v 1 LoopEdge 0 (fun _ _ => True) Hv In_0_1
         (total_IsBisim 2 ScottEdge 1 LoopEdge scott_has_child loop_has_child) TrueI).
Qed.

Theorem scott_nodes_bisim : Bisimilar 2 ScottEdge 0 2 ScottEdge 1.
exact (Bisimilar_trans 2 ScottEdge 0 1 LoopEdge 0 2 ScottEdge 1 (scott_bisim_loop 0 In_0_2)
         (Bisimilar_sym 2 ScottEdge 1 1 LoopEdge 0 (scott_bisim_loop 1 In_1_2))).
Qed.

Theorem FinslerEdge_2_0 : FinslerEdge 2 0.
prove (2 = 0 /\ 0 = 1) \/ (2 = 1 /\ 0 = 0) \/ (2 = 1 /\ 0 = 2)
      \/ (2 = 2 /\ 0 = 0) \/ (2 = 2 /\ 0 = 1).
apply or5I4.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem finsler_has_child : forall v :e 3, exists v':set, v' :e 3 /\ FinslerEdge v v'.
let v.
assume Hv: v :e 3.
apply (cases_3 v Hv (fun v => exists v':set, v' :e 3 /\ FinslerEdge v v')).
- prove exists v':set, v' :e 3 /\ FinslerEdge 0 v'.
  witness 1.
  apply andI.
  + exact In_1_3.
  + exact FinslerEdge_0_1.
- prove exists v':set, v' :e 3 /\ FinslerEdge 1 v'.
  witness 0.
  apply andI.
  + exact In_0_3.
  + exact FinslerEdge_1_0.
- prove exists v':set, v' :e 3 /\ FinslerEdge 2 v'.
  witness 0.
  apply andI.
  + exact In_0_3.
  + exact FinslerEdge_2_0.
Qed.

Theorem finsler_bisim_loop : forall v :e 3, Bisimilar 3 FinslerEdge v 1 LoopEdge 0.
let v.
assume Hv: v :e 3.
exact (Bisimilar_I 3 FinslerEdge v 1 LoopEdge 0 (fun _ _ => True) Hv In_0_1
         (total_IsBisim 3 FinslerEdge 1 LoopEdge finsler_has_child loop_has_child) TrueI).
Qed.

Theorem finsler_nodes_bisim : Bisimilar 3 FinslerEdge 1 3 FinslerEdge 2.
exact (Bisimilar_trans 3 FinslerEdge 1 1 LoopEdge 0 3 FinslerEdge 2 (finsler_bisim_loop 1 In_1_3)
         (Bisimilar_sym 3 FinslerEdge 2 1 LoopEdge 0 (finsler_bisim_loop 2 In_2_3))).
Qed.

Theorem NestEdge_1_0 : NestEdge 1 0.
prove (1 = 1 /\ 0 = 0) \/ (1 = 1 /\ 0 = 1).
apply orIL.
apply andI.
- reflexivity.
- reflexivity.
Qed.

Theorem nest_point_not_bisim_blank : ~Bisimilar 2 NestEdge 1 2 NestEdge 0.
assume H: Bisimilar 2 NestEdge 1 2 NestEdge 0.
apply (Bisimilar_E 2 NestEdge 1 2 NestEdge 0 H).
assume _: 1 :e 2.
assume _: 0 :e 2.
let R.
assume HR: IsBisim 2 NestEdge 2 NestEdge R.
assume H10: R 1 0.
apply (HR 1 In_1_2 0 In_0_2 H10).
assume Hforth: forall u' :e 2, NestEdge 1 u' -> exists v':set, v' :e 2 /\ NestEdge 0 v' /\ R u' v'.
assume _: forall v' :e 2, NestEdge 0 v' -> exists u':set, u' :e 2 /\ NestEdge 1 u' /\ R u' v'.
apply (Hforth 0 In_0_2 NestEdge_1_0).
let v'.
assume H1: v' :e 2 /\ NestEdge 0 v' /\ R 0 v'.
apply and3E (v' :e 2) (NestEdge 0 v') (R 0 v') H1.
assume _: v' :e 2.
assume H2: NestEdge 0 v'.
assume _: R 0 v'.
exact (NestEdge_not_from_0 v' H2).
Qed.

Theorem nest_point_not_bisim_loop : ~Bisimilar 2 NestEdge 1 1 LoopEdge 0.
assume H: Bisimilar 2 NestEdge 1 1 LoopEdge 0.
apply (Bisimilar_E 2 NestEdge 1 1 LoopEdge 0 H).
assume _: 1 :e 2.
assume _: 0 :e 1.
let R.
assume HR: IsBisim 2 NestEdge 1 LoopEdge R.
assume H10: R 1 0.
apply (HR 1 In_1_2 0 In_0_1 H10).
assume Hforth: forall u' :e 2, NestEdge 1 u' -> exists v':set, v' :e 1 /\ LoopEdge 0 v' /\ R u' v'.
assume _: forall v' :e 1, LoopEdge 0 v' -> exists u':set, u' :e 2 /\ NestEdge 1 u' /\ R u' v'.
apply (Hforth 0 In_0_2 NestEdge_1_0).
let v'.
assume H1: v' :e 1 /\ LoopEdge 0 v' /\ R 0 v'.
apply and3E (v' :e 1) (LoopEdge 0 v') (R 0 v') H1.
assume Hv': v' :e 1.
assume _: LoopEdge 0 v'.
assume H0v': R 0 v'.
apply (HR 0 In_0_2 v' Hv' H0v').
assume _: forall u' :e 2, NestEdge 0 u' -> exists w:set, w :e 1 /\ LoopEdge v' w /\ R u' w.
assume Hback: forall w :e 1, LoopEdge v' w -> exists u':set, u' :e 2 /\ NestEdge 0 u' /\ R u' w.
apply (Hback 0 In_0_1 TrueI).
let u'.
assume H3: u' :e 2 /\ NestEdge 0 u' /\ R u' 0.
apply and3E (u' :e 2) (NestEdge 0 u') (R u' 0) H3.
assume _: u' :e 2.
assume H4: NestEdge 0 u'.
assume _: R u' 0.
exact (NestEdge_not_from_0 u' H4).
Qed.
