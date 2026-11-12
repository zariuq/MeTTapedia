(** The addition of an additive commutative monoid, read from its instance.

    Lean's structures are the generated families; a parent or a field is the
    first component of an instance's record, which the generated projection
    functions return.  The laws are the instance's proof fields. **)

Theorem LeanAdd_field : forall G, forall s :e Lean_Add G, proj1 s 0 = Lean_Add_add G s.
let G.
exact Lean_Add_ind G (fun s => proj1 s 0 = Lean_Add_add G s)
  (fun x0 H0 => eq_i_tra (proj1 (Lean_Add_mk_node G x0) 0) x0 (Lean_Add_add G (Lean_Add_mk_node G x0))
    (Lean_Add_mk_field0 G x0)
    (eq_sym_i (Lean_Add_add G (Lean_Add_mk_node G x0)) x0 (Lean_Add_add_mk G x0 H0))).
Qed.

Theorem LeanAddSemigroup_field : forall G, forall s :e Lean_AddSemigroup G,
  proj1 s 0 = Lean_AddSemigroup_toAdd G s.
let G.
exact Lean_AddSemigroup_ind G (fun s => proj1 s 0 = Lean_AddSemigroup_toAdd G s)
  (fun x0 H0 x1 H1 =>
    eq_i_tra (proj1 (Lean_AddSemigroup_mk_node G x0 x1) 0) x0
      (Lean_AddSemigroup_toAdd G (Lean_AddSemigroup_mk_node G x0 x1))
      (Lean_AddSemigroup_mk_field0 G x0 x1)
      (eq_sym_i (Lean_AddSemigroup_toAdd G (Lean_AddSemigroup_mk_node G x0 x1)) x0
        (Lean_AddSemigroup_toAdd_mk G x0 H0 x1 H1))).
Qed.

Theorem LeanAddMonoid_field : forall G, forall s :e Lean_AddMonoid G,
  proj1 s 0 = Lean_AddMonoid_toAddSemigroup G s.
let G.
exact Lean_AddMonoid_ind G (fun s => proj1 s 0 = Lean_AddMonoid_toAddSemigroup G s)
  (fun x0 H0 x1 H1 x2 H2 x3 H3 x4 H4 x5 H5 x6 H6 =>
    eq_i_tra (proj1 (Lean_AddMonoid_mk_node G x0 x1 x2 x3 x4 x5 x6) 0) x0
      (Lean_AddMonoid_toAddSemigroup G (Lean_AddMonoid_mk_node G x0 x1 x2 x3 x4 x5 x6))
      (Lean_AddMonoid_mk_field0 G x0 x1 x2 x3 x4 x5 x6)
      (eq_sym_i (Lean_AddMonoid_toAddSemigroup G (Lean_AddMonoid_mk_node G x0 x1 x2 x3 x4 x5 x6)) x0
        (Lean_AddMonoid_toAddSemigroup_mk G x0 H0 x1 H1 x2 H2 x3 H3 x4 H4 x5 H5 x6 H6))).
Qed.

Theorem LeanAddCommMonoid_field : forall G, forall s :e Lean_AddCommMonoid G,
  proj1 s 0 = Lean_AddCommMonoid_toAddMonoid G s.
let G.
exact Lean_AddCommMonoid_ind G (fun s => proj1 s 0 = Lean_AddCommMonoid_toAddMonoid G s)
  (fun x0 H0 x1 H1 =>
    eq_i_tra (proj1 (Lean_AddCommMonoid_mk_node G x0 x1) 0) x0
      (Lean_AddCommMonoid_toAddMonoid G (Lean_AddCommMonoid_mk_node G x0 x1))
      (Lean_AddCommMonoid_mk_field0 G x0 x1)
      (eq_sym_i (Lean_AddCommMonoid_toAddMonoid G (Lean_AddCommMonoid_mk_node G x0 x1)) x0
        (Lean_AddCommMonoid_toAddMonoid_mk G x0 H0 x1 H1))).
Qed.

(** An instance's addition, as Lean's terms reach it. **)
Definition LeanAddOf : set -> set -> set :=
  fun G s => Lean_Add_add G (Lean_AddSemigroup_toAdd G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s))).

Theorem LeanAddOf_typed : forall G, forall s :e Lean_AddCommMonoid G,
  LeanAddOf G s :e (Pi_ ux :e G, (Pi_ ux :e G, G)).
let G s. assume Hs: s :e Lean_AddCommMonoid G.
exact Lean_Add_add_In G (Lean_AddSemigroup_toAdd G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s)))
  (Lean_AddSemigroup_toAdd_In G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s))
    (Lean_AddMonoid_toAddSemigroup_In G (Lean_AddCommMonoid_toAddMonoid G s)
      (Lean_AddCommMonoid_toAddMonoid_In G s Hs))).
Qed.

Theorem LeanAddOf_closed : forall G, forall s :e Lean_AddCommMonoid G, forall x y :e G, LeanAddOf G s x y :e G.
let G s. assume Hs: s :e Lean_AddCommMonoid G. let x. assume Hx: x :e G. let y. assume Hy: y :e G.
exact ap_Pi G (fun _ => G) (LeanAddOf G s x) y
  (ap_Pi G (fun _ => (Pi_ ux :e G, G)) (LeanAddOf G s) x (LeanAddOf_typed G s Hs) Hx) Hy.
Qed.

Theorem LeanAddSemigroup_raw : forall G, forall sg :e Lean_AddSemigroup G,
  proj1 (proj1 sg 0) 0 = Lean_Add_add G (Lean_AddSemigroup_toAdd G sg).
let G sg. assume Hsg: sg :e Lean_AddSemigroup G.
rewrite LeanAddSemigroup_field G sg Hsg.
exact LeanAdd_field G (Lean_AddSemigroup_toAdd G sg) (Lean_AddSemigroup_toAdd_In G sg Hsg).
Qed.

Theorem LeanAddOf_raw : forall G, forall s :e Lean_AddCommMonoid G,
  proj1 (proj1 (proj1 (proj1 s 0) 0) 0) 0 = LeanAddOf G s.
let G s. assume Hs: s :e Lean_AddCommMonoid G.
rewrite LeanAddCommMonoid_field G s Hs.
rewrite LeanAddMonoid_field G (Lean_AddCommMonoid_toAddMonoid G s) (Lean_AddCommMonoid_toAddMonoid_In G s Hs).
exact LeanAddSemigroup_raw G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s))
  (Lean_AddMonoid_toAddSemigroup_In G (Lean_AddCommMonoid_toAddMonoid G s) (Lean_AddCommMonoid_toAddMonoid_In G s Hs)).
Qed.

Theorem LeanAddSemigroup_assoc_raw : forall G, forall sg :e Lean_AddSemigroup G,
  forall x y z :e G, (proj1 (proj1 sg 0) 0) ((proj1 (proj1 sg 0) 0) x y) z =
    (proj1 (proj1 sg 0) 0) x ((proj1 (proj1 sg 0) 0) y z).
let G.
claim L: forall x0 :e Lean_Add G,
  forall x1 :e {z :e 1 | z :e (Pi_ q0 :e G, (Pi_ q1 :e G, (Pi_ q2 :e G,
    Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) q0 q1) q2) ((proj1 x0 0) q0 ((proj1 x0 0) q1 q2)))))},
  forall x y z :e G,
    (proj1 (proj1 (Lean_AddSemigroup_mk_node G x0 x1) 0) 0) ((proj1 (proj1 (Lean_AddSemigroup_mk_node G x0 x1) 0) 0) x y) z =
    (proj1 (proj1 (Lean_AddSemigroup_mk_node G x0 x1) 0) 0) x ((proj1 (proj1 (Lean_AddSemigroup_mk_node G x0 x1) 0) 0) y z).
{ let x0. assume H0: x0 :e Lean_Add G.
  let x1. assume H1: x1 :e {z :e 1 | z :e (Pi_ q0 :e G, (Pi_ q1 :e G, (Pi_ q2 :e G,
    Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) q0 q1) q2) ((proj1 x0 0) q0 ((proj1 x0 0) q1 q2)))))}.
  let x. assume Hx: x :e G. let y. assume Hy: y :e G. let z. assume Hz: z :e G.
  rewrite Lean_AddSemigroup_mk_field0 G x0 x1.
  claim Hg: x1 :e (Pi_ q0 :e G, (Pi_ q1 :e G, (Pi_ q2 :e G,
    Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) q0 q1) q2) ((proj1 x0 0) q0 ((proj1 x0 0) q1 q2))))).
  { exact SepE2 1 (fun z => z :e (Pi_ q0 :e G, (Pi_ q1 :e G, (Pi_ q2 :e G,
      Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) q0 q1) q2) ((proj1 x0 0) q0 ((proj1 x0 0) q1 q2)))))) x1 H1. }
  claim Hgx: x1 x :e (Pi_ q1 :e G, (Pi_ q2 :e G,
    Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) x q1) q2) ((proj1 x0 0) x ((proj1 x0 0) q1 q2)))).
  { exact ap_Pi G (fun q0 => (Pi_ q1 :e G, (Pi_ q2 :e G,
      Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) q0 q1) q2) ((proj1 x0 0) q0 ((proj1 x0 0) q1 q2))))) x1 x Hg Hx. }
  claim Hgxy: x1 x y :e (Pi_ q2 :e G,
    Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) x y) q2) ((proj1 x0 0) x ((proj1 x0 0) y q2))).
  { exact ap_Pi G (fun q1 => (Pi_ q2 :e G,
      Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) x q1) q2) ((proj1 x0 0) x ((proj1 x0 0) q1 q2)))) (x1 x) y Hgx Hy. }
  exact LeanEq_sound G ((proj1 x0 0) ((proj1 x0 0) x y) z) ((proj1 x0 0) x ((proj1 x0 0) y z)) (x1 x y z)
    (ap_Pi G (fun q2 => Lean_Eq_Prop G ((proj1 x0 0) ((proj1 x0 0) x y) q2) ((proj1 x0 0) x ((proj1 x0 0) y q2)))
      (x1 x y) z Hgxy Hz). }
exact Lean_AddSemigroup_ind G
  (fun sg => forall x y z :e G, (proj1 (proj1 sg 0) 0) ((proj1 (proj1 sg 0) 0) x y) z =
    (proj1 (proj1 sg 0) 0) x ((proj1 (proj1 sg 0) 0) y z)) L.
Qed.

Theorem LeanAddCommMonoid_comm_raw : forall G, forall s :e Lean_AddCommMonoid G,
  forall x y :e G, (proj1 (proj1 (proj1 (proj1 s 0) 0) 0) 0) x y = (proj1 (proj1 (proj1 (proj1 s 0) 0) 0) 0) y x.
let G.
claim L: forall x0 :e Lean_AddMonoid G,
  forall x1 :e {z :e 1 | z :e (Pi_ q0 :e G, (Pi_ q1 :e G,
    Lean_Eq_Prop G ((proj1 (proj1 (proj1 x0 0) 0) 0) q0 q1) ((proj1 (proj1 (proj1 x0 0) 0) 0) q1 q0)))},
  forall x y :e G,
    (proj1 (proj1 (proj1 (proj1 (Lean_AddCommMonoid_mk_node G x0 x1) 0) 0) 0) 0) x y =
    (proj1 (proj1 (proj1 (proj1 (Lean_AddCommMonoid_mk_node G x0 x1) 0) 0) 0) 0) y x.
{ let x0. assume H0: x0 :e Lean_AddMonoid G.
  let x1. assume H1: x1 :e {z :e 1 | z :e (Pi_ q0 :e G, (Pi_ q1 :e G,
    Lean_Eq_Prop G ((proj1 (proj1 (proj1 x0 0) 0) 0) q0 q1) ((proj1 (proj1 (proj1 x0 0) 0) 0) q1 q0)))}.
  let x. assume Hx: x :e G. let y. assume Hy: y :e G.
  rewrite Lean_AddCommMonoid_mk_field0 G x0 x1.
  claim Hg: x1 :e (Pi_ q0 :e G, (Pi_ q1 :e G,
    Lean_Eq_Prop G ((proj1 (proj1 (proj1 x0 0) 0) 0) q0 q1) ((proj1 (proj1 (proj1 x0 0) 0) 0) q1 q0))).
  { exact SepE2 1 (fun z => z :e (Pi_ q0 :e G, (Pi_ q1 :e G,
      Lean_Eq_Prop G ((proj1 (proj1 (proj1 x0 0) 0) 0) q0 q1) ((proj1 (proj1 (proj1 x0 0) 0) 0) q1 q0)))) x1 H1. }
  exact LeanEq_sound G ((proj1 (proj1 (proj1 x0 0) 0) 0) x y) ((proj1 (proj1 (proj1 x0 0) 0) 0) y x) (x1 x y)
    (ap_Pi G (fun q1 => Lean_Eq_Prop G ((proj1 (proj1 (proj1 x0 0) 0) 0) x q1) ((proj1 (proj1 (proj1 x0 0) 0) 0) q1 x))
      (x1 x) y
      (ap_Pi G (fun q0 => (Pi_ q1 :e G,
        Lean_Eq_Prop G ((proj1 (proj1 (proj1 x0 0) 0) 0) q0 q1) ((proj1 (proj1 (proj1 x0 0) 0) 0) q1 q0))) x1 x Hg Hx) Hy). }
exact Lean_AddCommMonoid_ind G
  (fun s => forall x y :e G, (proj1 (proj1 (proj1 (proj1 s 0) 0) 0) 0) x y = (proj1 (proj1 (proj1 (proj1 s 0) 0) 0) 0) y x) L.
Qed.

Theorem LeanAddOf_comm : forall G, forall s :e Lean_AddCommMonoid G, forall x y :e G,
  LeanAddOf G s x y = LeanAddOf G s y x.
let G s. assume Hs: s :e Lean_AddCommMonoid G.
rewrite <- LeanAddOf_raw G s Hs.
exact LeanAddCommMonoid_comm_raw G s Hs.
Qed.

Theorem LeanAddOf_assoc : forall G, forall s :e Lean_AddCommMonoid G, forall x y z :e G,
  LeanAddOf G s (LeanAddOf G s x y) z = LeanAddOf G s x (LeanAddOf G s y z).
let G s. assume Hs: s :e Lean_AddCommMonoid G.
claim Hsg: Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s) :e Lean_AddSemigroup G.
{ exact Lean_AddMonoid_toAddSemigroup_In G (Lean_AddCommMonoid_toAddMonoid G s) (Lean_AddCommMonoid_toAddMonoid_In G s Hs). }
prove forall x y z :e G,
  (Lean_Add_add G (Lean_AddSemigroup_toAdd G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s))))
    ((Lean_Add_add G (Lean_AddSemigroup_toAdd G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s)))) x y) z =
  (Lean_Add_add G (Lean_AddSemigroup_toAdd G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s))))
    x ((Lean_Add_add G (Lean_AddSemigroup_toAdd G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s)))) y z).
rewrite <- LeanAddSemigroup_raw G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s)) Hsg.
exact LeanAddSemigroup_assoc_raw G (Lean_AddMonoid_toAddSemigroup G (Lean_AddCommMonoid_toAddMonoid G s)) Hsg.
Qed.

Theorem LeanAddOf_left_comm : forall G, forall s :e Lean_AddCommMonoid G, forall x y v :e G,
  LeanAddOf G s x (LeanAddOf G s y v) = LeanAddOf G s y (LeanAddOf G s x v).
let G s. assume Hs: s :e Lean_AddCommMonoid G.
let x. assume Hx: x :e G. let y. assume Hy: y :e G. let v. assume Hv: v :e G.
rewrite <- LeanAddOf_assoc G s Hs x Hx y Hy v Hv.
rewrite <- LeanAddOf_assoc G s Hs y Hy x Hx v Hv.
rewrite LeanAddOf_comm G s Hs x Hx y Hy.
reflexivity.
Qed.
