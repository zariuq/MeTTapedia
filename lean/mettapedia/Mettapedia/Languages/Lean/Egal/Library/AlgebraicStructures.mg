(** Assemble the generated structure representations from operations and
    their laws. Natural-number instances discharge these premises with the
    recursor-equation library; these are not new assumptions about Nat. **)

Definition Lean_SemigroupOf : set -> set -> set := fun A operation =>
  Lean_Semigroup_mk_node A (Lean_Mul_mk_node A operation) 0.

Theorem Lean_SemigroupOf_typed : forall A,
  forall operation :e (Pi_ x :e A, (Pi_ y :e A, A)),
  (forall x y z :e A, operation (operation x y) z = operation x (operation y z)) ->
  Lean_SemigroupOf A operation :e Lean_Semigroup A.
let A operation. assume Hoperation: operation :e (Pi_ x :e A, (Pi_ y :e A, A)).
assume Hassoc: forall x y z :e A, operation (operation x y) z = operation x (operation y z).
prove Lean_Semigroup_mk_node A (Lean_Mul_mk_node A operation) 0 :e Lean_Semigroup A.
apply Lean_Semigroup_mk_typed A (Lean_Mul_mk_node A operation)
  (Lean_Mul_mk_typed A operation Hoperation) 0.
rewrite Lean_Mul_mk_field0 A operation.
apply SepI 1 (fun z => z :e (Pi_ x :e A, (Pi_ y :e A, (Pi_ z :e A,
  Lean_Eq_Prop A (operation (operation x y) z) (operation x (operation y z)))))) 0 In_0_1.
exact Lean_Eq_Pi3 A A A A (fun x y z => operation (operation x y) z)
  (fun x y z => operation x (operation y z)) Hassoc.
Qed.

Theorem Lean_SemigroupOf_operation : forall A operation,
  (proj1 ((proj1 (Lean_SemigroupOf A operation)) 0)) 0 = operation.
let A operation.
prove (proj1 ((proj1 (Lean_Semigroup_mk_node A (Lean_Mul_mk_node A operation) 0)) 0)) 0 = operation.
rewrite Lean_Semigroup_mk_field0 A (Lean_Mul_mk_node A operation) 0.
exact Lean_Mul_mk_field0 A operation.
Qed.

Definition Lean_MonoidOf : set -> set -> set -> set -> set := fun A operation unit power =>
  Lean_Monoid_mk_node A (Lean_SemigroupOf A operation) (Lean_One_mk_node A unit)
    0 0 (Lean_NPow_mk_node A power) 0 0.

Theorem Lean_MonoidOf_typed : forall A,
  forall operation :e (Pi_ x :e A, (Pi_ y :e A, A)), forall unit :e A,
  forall power :e (Pi_ n :e Lean_Nat, (Pi_ x :e A, A)),
  (forall x y z :e A, operation (operation x y) z = operation x (operation y z)) ->
  (forall x :e A, operation unit x = x) ->
  (forall x :e A, operation x unit = x) ->
  (forall x :e A, power (LeanNum 0) x = unit) ->
  (forall n :e Lean_Nat, forall x :e A,
    power (Lean_Nat_succ_node n) x = operation (power n x) x) ->
  Lean_MonoidOf A operation unit power :e Lean_Monoid A.
let A operation. assume Hoperation: operation :e (Pi_ x :e A, (Pi_ y :e A, A)).
let unit. assume Hunit: unit :e A.
let power. assume Hpower: power :e (Pi_ n :e Lean_Nat, (Pi_ x :e A, A)).
assume Hassoc: forall x y z :e A, operation (operation x y) z = operation x (operation y z).
assume Hleft: forall x :e A, operation unit x = x.
assume Hright: forall x :e A, operation x unit = x.
assume Hzero: forall x :e A, power (LeanNum 0) x = unit.
assume Hsucc: forall n :e Lean_Nat, forall x :e A,
  power (Lean_Nat_succ_node n) x = operation (power n x) x.
claim HleftField: 0 :e {z :e 1 | z :e (Pi_ x :e A,
  Lean_Eq_Prop A ((proj1 ((proj1 (Lean_SemigroupOf A operation)) 0)) 0 ((proj1 (Lean_One_mk_node A unit)) 0) x) x)}.
{ rewrite Lean_SemigroupOf_operation A operation.
  rewrite Lean_One_mk_field0 A unit.
  apply SepI 1 (fun z => z :e (Pi_ x :e A, Lean_Eq_Prop A (operation unit x) x)) 0 In_0_1.
  exact Lean_Eq_Pi1 A A (fun x => operation unit x) (fun x => x) Hleft. }
claim HrightField: 0 :e {z :e 1 | z :e (Pi_ x :e A,
  Lean_Eq_Prop A ((proj1 ((proj1 (Lean_SemigroupOf A operation)) 0)) 0 x ((proj1 (Lean_One_mk_node A unit)) 0)) x)}.
{ rewrite Lean_SemigroupOf_operation A operation.
  rewrite Lean_One_mk_field0 A unit.
  apply SepI 1 (fun z => z :e (Pi_ x :e A, Lean_Eq_Prop A (operation x unit) x)) 0 In_0_1.
  exact Lean_Eq_Pi1 A A (fun x => operation x unit) (fun x => x) Hright. }
claim HzeroField: 0 :e {z :e 1 | z :e (Pi_ x :e A,
  Lean_Eq_Prop A ((proj1 (Lean_NPow_mk_node A power)) 0 (LeanNum 0) x) ((proj1 (Lean_One_mk_node A unit)) 0))}.
{ rewrite Lean_NPow_mk_field0 A power.
  rewrite Lean_One_mk_field0 A unit.
  apply SepI 1 (fun z => z :e (Pi_ x :e A, Lean_Eq_Prop A (power (LeanNum 0) x) unit)) 0 In_0_1.
  exact Lean_Eq_Pi1 A A (fun x => power (LeanNum 0) x) (fun _ => unit) Hzero. }
claim HsuccField: 0 :e {z :e 1 | z :e (Pi_ n :e Lean_Nat, (Pi_ x :e A,
  Lean_Eq_Prop A ((proj1 (Lean_NPow_mk_node A power)) 0 (Lean_Nat_succ_node n) x)
    ((proj1 ((proj1 (Lean_SemigroupOf A operation)) 0)) 0 ((proj1 (Lean_NPow_mk_node A power)) 0 n x) x)))}.
{ rewrite Lean_SemigroupOf_operation A operation.
  rewrite Lean_NPow_mk_field0 A power.
  apply SepI 1 (fun z => z :e (Pi_ n :e Lean_Nat, (Pi_ x :e A,
    Lean_Eq_Prop A (power (Lean_Nat_succ_node n) x) (operation (power n x) x)))) 0 In_0_1.
  exact Lean_Eq_Pi2 Lean_Nat A A (fun n x => power (Lean_Nat_succ_node n) x)
    (fun n x => operation (power n x) x) Hsucc. }
exact Lean_Monoid_mk_typed A (Lean_SemigroupOf A operation)
  (Lean_SemigroupOf_typed A operation Hoperation Hassoc)
  (Lean_One_mk_node A unit) (Lean_One_mk_typed A unit Hunit)
  0 HleftField 0 HrightField (Lean_NPow_mk_node A power) (Lean_NPow_mk_typed A power Hpower)
  0 HzeroField 0 HsuccField.
Qed.

(** These separately generated source structures have the same set
    representation after renaming their operations and laws. **)
Theorem AddMonoid_representation : forall A, Lean_AddMonoid A = Lean_Monoid A.
let A. reflexivity.
Qed.

Theorem AddMonoid_constructor_representation : forall A s u left right power zero succ,
  Lean_AddMonoid_mk_node A s u left right power zero succ =
    Lean_Monoid_mk_node A s u left right power zero succ.
let A s u left right power zero succ. reflexivity.
Qed.

Theorem Lean_MonoidOf_operation : forall A operation unit power,
  (proj1 ((proj1 ((proj1 (Lean_MonoidOf A operation unit power)) 0)) 0)) 0 = operation.
let A operation unit power.
prove (proj1 ((proj1 ((proj1 (Lean_Monoid_mk_node A (Lean_SemigroupOf A operation)
  (Lean_One_mk_node A unit) 0 0 (Lean_NPow_mk_node A power) 0 0)) 0)) 0)) 0 = operation.
rewrite Lean_Monoid_mk_field0 A (Lean_SemigroupOf A operation)
  (Lean_One_mk_node A unit) 0 0 (Lean_NPow_mk_node A power) 0 0.
exact Lean_SemigroupOf_operation A operation.
Qed.

Definition Lean_AddMonoidOf : set -> set -> set -> set -> set := fun A operation zero scale =>
  Lean_AddMonoid_mk_node A (Lean_AddSemigroup_mk_node A (Lean_Add_mk_node A operation) 0)
    (Lean_Zero_mk_node A zero) 0 0 (Lean_NSMul_mk_node A scale) 0 0.

Theorem Lean_AddMonoidOf_representation : forall A operation zero scale,
  Lean_AddMonoidOf A operation zero scale = Lean_MonoidOf A operation zero scale.
let A operation zero scale. reflexivity.
Qed.

Theorem Lean_AddMonoidOf_typed : forall A,
  forall operation :e (Pi_ x :e A, (Pi_ y :e A, A)), forall zero :e A,
  forall scale :e (Pi_ n :e Lean_Nat, (Pi_ x :e A, A)),
  (forall x y z :e A, operation (operation x y) z = operation x (operation y z)) ->
  (forall x :e A, operation zero x = x) ->
  (forall x :e A, operation x zero = x) ->
  (forall x :e A, scale (LeanNum 0) x = zero) ->
  (forall n :e Lean_Nat, forall x :e A,
    scale (Lean_Nat_succ_node n) x = operation (scale n x) x) ->
  Lean_AddMonoidOf A operation zero scale :e Lean_AddMonoid A.
let A operation. assume Hop: operation :e (Pi_ x :e A, (Pi_ y :e A, A)).
let zero. assume Hz: zero :e A.
let scale. assume Hscale: scale :e (Pi_ n :e Lean_Nat, (Pi_ x :e A, A)).
assume Hassoc: forall x y z :e A, operation (operation x y) z = operation x (operation y z).
assume Hleft: forall x :e A, operation zero x = x.
assume Hright: forall x :e A, operation x zero = x.
assume Hzero: forall x :e A, scale (LeanNum 0) x = zero.
assume Hsucc: forall n :e Lean_Nat, forall x :e A,
  scale (Lean_Nat_succ_node n) x = operation (scale n x) x.
rewrite Lean_AddMonoidOf_representation A operation zero scale.
rewrite AddMonoid_representation A.
exact Lean_MonoidOf_typed A operation Hop zero Hz scale Hscale Hassoc Hleft Hright Hzero Hsucc.
Qed.

Definition Lean_AddCommMonoidOf : set -> set -> set -> set -> set := fun A operation zero scale =>
  Lean_AddCommMonoid_mk_node A (Lean_AddMonoidOf A operation zero scale) 0.

Theorem Lean_AddCommMonoidOf_typed : forall A operation zero scale,
  Lean_AddMonoidOf A operation zero scale :e Lean_AddMonoid A ->
  (forall x y :e A, operation x y = operation y x) ->
  Lean_AddCommMonoidOf A operation zero scale :e Lean_AddCommMonoid A.
let A operation zero scale.
assume Hparent: Lean_AddMonoidOf A operation zero scale :e Lean_AddMonoid A.
assume Hcomm: forall x y :e A, operation x y = operation y x.
prove Lean_AddCommMonoid_mk_node A (Lean_AddMonoidOf A operation zero scale) 0 :e Lean_AddCommMonoid A.
apply Lean_AddCommMonoid_mk_typed A (Lean_AddMonoidOf A operation zero scale) Hparent 0.
rewrite Lean_AddMonoidOf_representation A operation zero scale.
rewrite Lean_MonoidOf_operation A operation zero scale.
apply SepI 1 (fun z => z :e (Pi_ x :e A, (Pi_ y :e A,
  Lean_Eq_Prop A (operation x y) (operation y x)))) 0 In_0_1.
exact Lean_Eq_Pi2 A A A (fun x y => operation x y) (fun x y => operation y x) Hcomm.
Qed.
