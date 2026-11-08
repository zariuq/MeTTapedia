(** Deterministic machines.  A step function F on a set A of states returns
    an element of Lean_Option A: some next state, or none when the machine
    stops.  Its step relation relates x to y when F x is some y, and a run is
    the reflexive-transitive closure of that relation.  The lemmas hold for
    every A and F. **)

Definition Lean_StepRel : set -> (set -> set) -> set :=
  fun A F => fun x :e A => fun y :e A => Lean_Eq_Prop (Lean_Option A) (F x) (Lean_Option_some_node A y).

Theorem Lean_StepRel_eq : forall A:set, forall F:set -> set, forall x :e A, forall y :e A,
  Lean_StepRel A F x y = Lean_Eq_Prop (Lean_Option A) (F x) (Lean_Option_some_node A y).
let A F x. assume Hx: x :e A. let y. assume Hy: y :e A.
prove (fun x :e A => fun y :e A => Lean_Eq_Prop (Lean_Option A) (F x) (Lean_Option_some_node A y)) x y
  = Lean_Eq_Prop (Lean_Option A) (F x) (Lean_Option_some_node A y).
rewrite beta A (fun x => fun y :e A => Lean_Eq_Prop (Lean_Option A) (F x) (Lean_Option_some_node A y)) x Hx.
rewrite beta A (fun y => Lean_Eq_Prop (Lean_Option A) (F x) (Lean_Option_some_node A y)) y Hy.
reflexivity.
Qed.

Theorem Lean_StepRel_E : forall A:set, forall F:set -> set, forall x :e A, forall y :e A,
  0 :e Lean_StepRel A F x y -> F x = Lean_Option_some_node A y.
let A F x. assume Hx: x :e A. let y. assume Hy: y :e A. assume H: 0 :e Lean_StepRel A F x y.
apply LeanEq_sound (Lean_Option A) (F x) (Lean_Option_some_node A y) 0.
rewrite <- Lean_StepRel_eq A F x Hx y Hy. exact H.
Qed.

Theorem Lean_StepRel_I : forall A:set, forall F:set -> set, forall x :e A, forall y :e A,
  F x = Lean_Option_some_node A y -> 0 :e Lean_StepRel A F x y.
let A F x. assume Hx: x :e A. let y. assume Hy: y :e A. assume H: F x = Lean_Option_some_node A y.
rewrite Lean_StepRel_eq A F x Hx y Hy. rewrite H.
exact Lean_Eq_refl_proof_ok (Lean_Option A) (Lean_Option_some_node A y).
Qed.

(** One step is a run. **)
Theorem Lean_Machine_single : forall A:set, forall F:set -> set, forall a :e A, forall b :e A,
  F a = Lean_Option_some_node A b -> 0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) a b.
let A F a. assume Ha: a :e A. let b. assume Hb: b :e A. assume H.
exact Lean_RTG_single A (Lean_StepRel A F) a Ha b Hb (Lean_StepRel_I A F a Ha b Hb H).
Qed.

(** A step followed by a run is a run. **)
Theorem Lean_Machine_head : forall A:set, forall F:set -> set, forall a :e A, forall b :e A, forall c,
  F a = Lean_Option_some_node A b -> 0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) b c ->
  0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) a c.
let A F a. assume Ha: a :e A. let b. assume Hb: b :e A. let c. assume H. assume R.
exact Lean_RTG_head A (Lean_StepRel A F) a Ha b Hb c (Lean_StepRel_I A F a Ha b Hb H) R.
Qed.

(** Three steps, each followed by a run, compose into one run. **)
Theorem Lean_Machine_path3 : forall A:set, forall F:set -> set,
  forall s0 :e A, forall s1 :e A, forall s2, forall s3 :e A, forall s4, forall s5 :e A, forall s6,
  F s0 = Lean_Option_some_node A s1 -> 0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) s1 s2 ->
  s2 :e A -> F s2 = Lean_Option_some_node A s3 -> 0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) s3 s4 ->
  s4 :e A -> F s4 = Lean_Option_some_node A s5 -> 0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) s5 s6 ->
  0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) s0 s6.
let A F s0. assume H0: s0 :e A. let s1. assume H1: s1 :e A. let s2 s3. assume H3: s3 :e A.
let s4 s5. assume H5: s5 :e A. let s6.
assume E0. assume R1. assume H2: s2 :e A. assume E2. assume R3. assume H4: s4 :e A. assume E4. assume R5.
apply Lean_Machine_head A F s0 H0 s1 H1 s6 E0.
apply Lean_RTG_trans A (Lean_StepRel A F) s1 s2 s6 R1.
apply Lean_Machine_head A F s2 H2 s3 H3 s6 E2.
apply Lean_RTG_trans A (Lean_StepRel A F) s3 s4 s6 R3.
exact Lean_Machine_head A F s4 H4 s5 H5 s6 E4 R5.
Qed.

(** The step relation of a function is deterministic, and a state where the
    function returns none has no successor; so two runs from one state to
    states where it returns none end at the same state. **)
Theorem Lean_Machine_final_unique : forall A:set, forall F:set -> set,
  forall s :e A, forall f1 :e A, forall f2 :e A,
  0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) s f1 ->
  0 :e Lean_Relation_ReflTransGen_Prop A (Lean_StepRel A F) s f2 ->
  F f1 = Lean_Option_none_node A -> F f2 = Lean_Option_none_node A -> f1 = f2.
let A F s. assume Hs: s :e A. let f1. assume Hf1: f1 :e A. let f2. assume Hf2: f2 :e A.
assume R1. assume R2. assume N1. assume N2.
claim Det: forall x :e A, forall y :e A, forall z :e A,
  0 :e Lean_StepRel A F x y -> 0 :e Lean_StepRel A F x z -> y = z.
{ let x. assume Hx. let y. assume Hy. let z. assume Hz. assume Hxy. assume Hxz.
  apply Lean_Option_some_inj0 A y z.
  rewrite <- Lean_StepRel_E A F x Hx y Hy Hxy. exact Lean_StepRel_E A F x Hx z Hz Hxz. }
claim Stop: forall f :e A, F f = Lean_Option_none_node A -> forall y :e A, 0 /:e Lean_StepRel A F f y.
{ let f. assume Hf. assume N. let y. assume Hy. assume Hr.
  apply Lean_Option_noconf0_1 A y.
  rewrite <- N. exact Lean_StepRel_E A F f Hf y Hy Hr. }
exact Lean_RTG_final_unique A (Lean_StepRel A F) Det s Hs f1 Hf1 f2 Hf2 R1 R2 (Stop f1 Hf1 N1) (Stop f2 Hf2 N2).
Qed.
