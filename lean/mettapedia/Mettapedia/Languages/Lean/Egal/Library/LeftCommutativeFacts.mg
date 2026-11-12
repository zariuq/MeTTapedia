(** Lean's LeftCommutative, the generated reading of the class, as an Egal
    proposition about the operation. **)

Theorem LeanLeftCommutative_intro : forall A B f,
  (forall x y :e A, forall v :e B, f x (f y v) = f y (f x v)) -> 0 :e Lean_LeftCommutative_Prop A B f.
let A B f. assume H: forall x y :e A, forall v :e B, f x (f y v) = f y (f x v).
claim Hproduct: 0 :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2))))).
{ exact Pi_0_In A (fun q0 => (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))
    (fun q0 H0 => Pi_0_In A (fun q1 => (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2))))
      (fun q1 H1 => Pi_0_In B (fun q2 => Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))
        (fun q2 H2 => Lean_Eq_proof_of B (f q0 (f q1 q2)) (f q1 (f q0 q2)) (H q0 H0 q1 H1 q2 H2)))). }
claim Hguard: 0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))}.
{ exact SepI 1 (fun z => z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))) 0 In_0_1 Hproduct. }
exact SepI 1 (fun _ => exists w, w :e Lean_LeftCommutative A B f) 0 In_0_1
  (fun P K => K (Lean_LeftCommutative_mk_node A B f 0) (Lean_LeftCommutative_mk_typed A B f 0 Hguard)).
Qed.

Theorem LeanLeftCommutative_elim : forall A B f, 0 :e Lean_LeftCommutative_Prop A B f ->
  forall x y :e A, forall v :e B, f x (f y v) = f y (f x v).
let A B f. assume H: 0 :e Lean_LeftCommutative_Prop A B f.
claim L: forall x0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))},
  forall x y :e A, forall v :e B, f x (f y v) = f y (f x v).
{ let x0. assume H0: x0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))}.
  let x. assume Hx: x :e A. let y. assume Hy: y :e A. let v. assume Hv: v :e B.
  claim Hg: x0 :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2))))).
  { exact SepE2 1 (fun z => z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))) x0 H0. }
  claim Hgx: x0 x :e (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f x (f q1 q2)) (f q1 (f x q2)))).
  { exact ap_Pi A (fun q0 => (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2))))) x0 x Hg Hx. }
  claim Hgxy: x0 x y :e (Pi_ q2 :e B, Lean_Eq_Prop B (f x (f y q2)) (f y (f x q2))).
  { exact ap_Pi A (fun q1 => (Pi_ q2 :e B, Lean_Eq_Prop B (f x (f q1 q2)) (f q1 (f x q2)))) (x0 x) y Hgx Hy. }
  exact LeanEq_sound B (f x (f y v)) (f y (f x v)) (x0 x y v)
    (ap_Pi B (fun q2 => Lean_Eq_Prop B (f x (f y q2)) (f y (f x q2))) (x0 x y) v Hgxy Hv). }
apply SepE2 1 (fun _ => exists w, w :e Lean_LeftCommutative A B f) 0 H.
let w. assume Hw: w :e Lean_LeftCommutative A B f.
claim Hh0: (fun x0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))} => 0)
  :e (Pi_ x0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))}, {z :e 1 | forall x y :e A, forall v :e B, f x (f y v) = f y (f x v)}).
{ exact lam_Pi {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))}
    (fun _ => {z :e 1 | forall x y :e A, forall v :e B, f x (f y v) = f y (f x v)}) (fun _ => 0)
    (fun x0 H0 => SepI 1 (fun _ => forall x y :e A, forall v :e B, f x (f y v) = f y (f x v)) 0 In_0_1 (L x0 H0)). }
exact SepE2 1 (fun _ => forall x y :e A, forall v :e B, f x (f y v) = f y (f x v))
  (Lean_LeftCommutative_rec A B f (fun x0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))} => 0) w)
  (Lean_LeftCommutative_rec_type A B f (fun _ => {z :e 1 | forall x y :e A, forall v :e B, f x (f y v) = f y (f x v)})
    (fun x0 :e {z :e 1 | z :e (Pi_ q0 :e A, (Pi_ q1 :e A, (Pi_ q2 :e B, Lean_Eq_Prop B (f q0 (f q1 q2)) (f q1 (f q0 q2)))))} => 0) Hh0 w Hw).
Qed.
