Theorem equip_refl : forall X:set, equip X X.
let X.
exact equip_ref X.
Qed.

Theorem set_eq_refl : forall x:set, x = x.
let x.
reflexivity.
Qed.

Theorem equip_singleton : forall v:set, equip 1 {v}.
let v.
apply equip_sym {v} 1.
prove exists f:set -> set, bij {v} 1 f.
set f := fun z:set => 0.
witness f.
apply bijI {v} 1 f.
- prove forall u :e {v}, f u :e 1.
  let u. assume Hu: u :e {v}.
  prove 0 :e 1.
  exact In_0_1.
- prove forall u w :e {v}, f u = f w -> u = w.
  let u. assume Hu: u :e {v}.
  let w. assume Hw: w :e {v}.
  assume _: f u = f w.
  claim Hux: u = v.
    exact SingE v u Hu.
  claim Hwx: w = v.
    exact SingE v w Hw.
  rewrite Hux. rewrite Hwx. reflexivity.
- prove forall w :e 1, exists u :e {v}, f u = w.
  let w. assume Hw: w :e 1.
  claim Hw0: w = 0.
    exact cases_1 w Hw (fun z => z = 0) (set_eq_refl 0).
  witness v.
  apply andI.
  + exact SingI v.
  + rewrite Hw0.
    reflexivity.
Qed.

Theorem nat_p_12 : nat_p 12.
exact nat_ordsucc 11 (nat_ordsucc 10 (nat_ordsucc 9 (nat_ordsucc 8 (nat_ordsucc 7
      (nat_ordsucc 6 (nat_ordsucc 5 (nat_ordsucc 4 (nat_ordsucc 3 (nat_ordsucc 2 nat_2))))))))).
Qed.

Theorem nat_p_13 : nat_p 13.
exact nat_ordsucc 12 nat_p_12.
Qed.

Theorem nat_p_17 : nat_p 17.
exact nat_ordsucc 16 (nat_ordsucc 15 (nat_ordsucc 14 (nat_ordsucc 13 nat_p_13))).
Qed.

Theorem nat_p_18 : nat_p 18.
exact nat_ordsucc 17 nat_p_17.
Qed.

Theorem in_13_18 : 13 :e 18.
prove 13 :e ordsucc 17.
apply ordsuccI1 17.
prove 13 :e 17.
apply ordsuccI1 16.
prove 13 :e 16.
apply ordsuccI1 15.
prove 13 :e 15.
apply ordsuccI1 14.
prove 13 :e 14.
exact ordsuccI2 13.
Qed.

Theorem Subq_13_18 : 13 c= 18.
prove forall x :e 13, x :e 18.
let x. assume Hx: x :e 13.
exact nat_trans 18 nat_p_18 13 in_13_18 x Hx.
Qed.

Theorem equip_18_self : equip 18 18.
exact equip_refl 18.
Qed.
