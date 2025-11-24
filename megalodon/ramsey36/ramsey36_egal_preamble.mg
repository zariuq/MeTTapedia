Theorem equip_bij : forall X Y, equip X Y -> exists f:set -> set, bij X Y f.
let X Y.
assume H: equip X Y.
exact H.
Qed.

Theorem bij_equip : forall X Y, forall f:set -> set, bij X Y f -> equip X Y.
let X Y f.
assume H: bij X Y f.
prove equip X Y.
prove exists g:set -> set, bij X Y g.
witness f.
exact H.
Qed.
