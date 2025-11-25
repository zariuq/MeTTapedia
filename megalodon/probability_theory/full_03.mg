Definition DummyStart : prop := True.

Definition MyReal : set := Empty.
Definition R_zero : set := Empty.
Definition R_one : set := Empty.
Definition R_plus : set -> set -> set := fun x y => Empty.
Definition R_mult : set -> set -> set := fun x y => Empty.
Definition R_leq : set -> set -> prop := fun x y => True.
Definition R_minus : set -> set -> set := fun x y => Empty.
Definition R_div : set -> set -> set := fun x y => Empty.

Infix + 360 right := R_plus.
Infix * 355 right := R_mult.
Infix <= 490 := R_leq.
Infix - 361 := R_minus.
Infix :/: 353 := R_div.

Axiom R_div_clos : forall x y :e MyReal, y <> R_zero -> x :/: y :e MyReal.
Axiom R_mult_div : forall x y :e MyReal, y <> R_zero -> (x :/: y) * y = x.

Definition R_lt : set -> set -> prop := fun x y => x <= y /\ x <> y.
Infix < 490 := R_lt.

Axiom R_zero_In : R_zero :e MyReal.
Axiom R_one_In : R_one :e MyReal.
Axiom R_plus_clos : forall x y :e MyReal, x + y :e MyReal.
Axiom R_mult_clos : forall x y :e MyReal, x * y :e MyReal.
Axiom R_minus_clos : forall x y :e MyReal, x - y :e MyReal.

Axiom R_leq_refl : forall x :e MyReal, x <= x.
Axiom R_leq_trans : forall x y z :e MyReal, x <= y -> y <= z -> x <= z.
Axiom R_leq_antisym : forall x y :e MyReal, x <= y -> y <= x -> x = y.
Axiom R_zero_leq_one : R_zero <= R_one.
Axiom R_zero_leq_x_implies_plus_leq : forall x y :e MyReal, R_zero <= y -> x <= x + y.

Axiom R_plus_comm : forall x y :e MyReal, x + y = y + x.
Axiom R_plus_assoc : forall x y z :e MyReal, x + (y + z) = (x + y) + z.
Axiom R_plus_zero : forall x :e MyReal, x + R_zero = x.

Axiom R_mult_comm : forall x y :e MyReal, x * y = y * x.
Axiom R_mult_assoc : forall x y z :e MyReal, x * (y * z) = (x * y) * z.
Axiom R_mult_one : forall x :e MyReal, x * R_one = x.
Axiom R_distrib : forall x y z :e MyReal, x * (y + z) = x * y + x * z.

Axiom R_minus_self : forall x :e MyReal, x - x = R_zero.
Axiom R_plus_minus : forall x y :e MyReal, (x + y) - y = x.
Axiom R_minus_plus_distr : forall x y z :e MyReal, x - (y + z) = (x - y) - z.
Axiom R_minus_eq_iff : forall x y :e MyReal, x = R_one - y <-> x + y = R_one.

Axiom R_leq_plus_r : forall x y z :e MyReal, x <= y -> x + z <= y + z.
Axiom R_leq_plus_cancel : forall x y z :e MyReal, x + z <= y + z -> x <= y.

Definition sum_nat : (set -> set) -> set := fun f => Empty.

Axiom sum_nat_clos : forall f : set -> set, (forall n :e omega, f n :e MyReal /\ R_zero <= f n) -> sum_nat f :e MyReal.

Axiom sum_nat_zero : sum_nat (fun n => R_zero) = R_zero.

Axiom sum_nat_pair : forall a b :e MyReal,
  sum_nat (fun n => if n = 0 then a else if n = 1 then b else R_zero) = a + b.

Definition Disjoint : set -> set -> prop :=
  fun A B => A :/\: B = Empty.

Definition pairwise_disjoint : (set -> set) -> prop :=
  fun f => forall m n :e omega, m <> n -> Disjoint (f m) (f n).

Definition bigcup_nat : (set -> set) -> set :=
  fun f => Union {f n | n :e omega}.

Definition is_field : set -> set -> prop :=
  fun Omega F =>
    (forall A :e F, A c= Omega)
    /\ Omega :e F
    /\ Empty :e F
    /\ (forall A :e F, (Omega :\: A) :e F)
    /\ (forall A B, A :e F -> B :e F -> (A :\/: B) :e F).

Theorem field_has_omega :
  forall Omega F, is_field Omega F -> Omega :e F.
let Omega. let F.
assume H: is_field Omega F.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              H.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
exact andER (forall A :e F, A c= Omega)
            (Omega :e F)
            H12.
Qed.

Theorem field_closed_under_intersection :
  forall Omega F A B,
    is_field Omega F ->
    A :e F -> B :e F ->
    (A :/\: B) :e F.
let Omega. let F. let A. let B.
assume HF: is_field Omega F.
assume HA: A :e F.
assume HB: B :e F.
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H12: (forall A :e F, A c= Omega) /\ Omega :e F.
  exact andEL ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.
claim H_union: forall A B, A :e F -> B :e F -> (A :\/: B) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H_compl: forall A :e F, (Omega :\: A) :e F.
  exact andER (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim H_sub: forall A :e F, A c= Omega.
  exact andEL (forall A :e F, A c= Omega)
              (Omega :e F)
              H12.
claim HA_sub: A c= Omega. exact H_sub A HA.
claim HB_sub: B c= Omega. exact H_sub B HB.
claim HAc: (Omega :\: A) :e F. exact H_compl A HA.
claim HBc: (Omega :\: B) :e F. exact H_compl B HB.
claim HU: (Omega :\: A) :\/: (Omega :\: B) :e F.
  exact H_union (Omega :\: A) (Omega :\: B) HAc HBc.
claim HRes: (Omega :\: ((Omega :\: A) :\/: (Omega :\: B))) :e F.
  exact H_compl ((Omega :\: A) :\/: (Omega :\: B)) HU.
claim Heq: A :/\: B = Omega :\: ((Omega :\: A) :\/: (Omega :\: B)).
  admit.
exact Heq (fun _ X => X :e F) HRes.
Qed.

Definition is_sigma_field : set -> set -> prop :=
  fun Omega F =>
    is_field Omega F
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         bigcup_nat f :e F).

Theorem sigma_field_is_field :
  forall Omega F,
    is_sigma_field Omega F ->
    is_field Omega F.
let Omega. let F.
assume H: is_sigma_field Omega F.
exact andEL (is_field Omega F) (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F) H.
Qed.

Definition DummyReset : prop := True.

Definition is_probability_measure : set -> set -> (set -> set) -> prop :=
  fun Omega F P =>
    is_sigma_field Omega F
    /\ (forall A :e F, P A :e MyReal /\ R_zero <= P A)
    /\ P Omega = R_one
    /\ P Empty = R_zero
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         pairwise_disjoint f ->
         P (bigcup_nat f) = sum_nat (fun n => P (f n))).

Theorem prob_measure_is_sigma_field :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    is_sigma_field Omega F.
let Omega. let F. let P.
assume H: is_probability_measure Omega F P.
admit.
Qed.

Theorem prob_empty_zero :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    P Empty = R_zero.
let Omega. let F. let P.
assume H: is_probability_measure Omega F P.
claim H_rest: (forall A :e F, P A :e MyReal /\ R_zero <= P A) /\ P Omega = R_one /\ P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e MyReal /\ R_zero <= P A) /\ P Omega = R_one /\ P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H.
claim H_rest2: P Omega = R_one /\ P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  exact andER (forall A :e F, P A :e MyReal /\ R_zero <= P A) (P Omega = R_one /\ P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H_rest.
claim H_rest3: P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  exact andER (P Omega = R_one) (P Empty = R_zero /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H_rest2.
exact andEL (P Empty = R_zero) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) H_rest3.
Qed.

Theorem prob_finite_additivity :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    Disjoint A B ->
    P (A :\/: B) = P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hd.
admit.
Qed.

Theorem prob_monotone :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    A c= B ->
    P A <= P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hab.
admit.
Qed.

Theorem prob_complement :
  forall Omega F, forall P: set -> set, forall A,
    is_probability_measure Omega F P ->
    A :e F ->
    P (Omega :\: A) = R_one - P A.
let Omega. let F. let P. let A.
assume H. assume HA.
admit.
Qed.

Theorem prob_union_bound :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    P (A :\/: B) <= P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB.
admit.
Qed.
Definition conditional_prob : set -> (set -> set) -> set -> set -> set :=
  fun Omega P A B =>
    if R_zero < P B
    then (P (A :/\: B)) :/: (P B)
    else R_zero.

Theorem product_rule :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    R_zero < P B ->
    P (A :/\: B) = P B * conditional_prob Omega P A B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hp.
claim Hdef: conditional_prob Omega P A B = (P (A :/\: B)) :/: (P B).
  exact If_i_1 (R_zero < P B) ((P (A :/\: B)) :/: (P B)) R_zero Hp.
rewrite Hdef.
claim Hne: P B <> R_zero.
  exact neq_i_sym R_zero (P B) (andER (R_zero <= P B) (R_zero <> P B) Hp).
claim P_in_R: P B :e MyReal.
  admit.
claim P_int_in_R: P (A :/\: B) :e MyReal.
  admit.

symmetry.
exact R_mult_div (P (A :/\: B)) P_int_in_R (P B) P_in_R Hne.
Qed.

Theorem bayes_theorem :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    R_zero < P A ->
    R_zero < P B ->
    conditional_prob Omega P A B = (conditional_prob Omega P B A * P A) :/: (P B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpA. assume HpB.
admit.
Qed.

Theorem total_probability_binary :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    R_zero < P B ->
    R_zero < P (Omega :\: B) ->
    P A = P (A :/\: B) + P (A :/\: (Omega :\: B)).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpB. assume HpBc.
admit.
Qed.

Theorem total_probability_binary_conditional :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    R_zero < P B ->
    R_zero < P (Omega :\: B) ->
    P A = conditional_prob Omega P A B * P B + conditional_prob Omega P A (Omega :\: B) * P (Omega :\: B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpB. assume HpBc.
admit.
Qed.
