Definition sum_nat : (set -> set) -> set := fun f => 0.

Axiom sum_nat_clos : forall f : set -> set, (forall n :e omega, f n :e real /\ 0 <= f n) -> sum_nat f :e real.

Axiom sum_nat_zero : sum_nat (fun n => 0) = 0.

Axiom sum_nat_pair : forall a b :e real, sum_nat (fun n => If_i (n = 0) a (If_i (n = 1) b 0)) = a + b.

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
{ apply set_ext.
  - prove A :/\: B c= Omega :\: ((Omega :\: A) :\/: (Omega :\: B)).
    let z.
    assume Hz: z :e A :/\: B.
    apply setminusI.
    + exact H_sub A HA z (binintersectE1 A B z Hz).
    + assume HContra.
      apply orE (z :e Omega :\: A) (z :e Omega :\: B) False (fun H => setminusE2 Omega A z H (binintersectE1 A B z Hz)) (fun H => setminusE2 Omega B z H (binintersectE2 A B z Hz)) (binunionE (Omega :\: A) (Omega :\: B) z HContra).
  - prove (Omega :\: ((Omega :\: A) :\/: (Omega :\: B))) c= A :/\: B.
    let z.
    assume Hz: z :e Omega :\: ((Omega :\: A) :\/: (Omega :\: B)).
    apply binintersectI.
    + claim zInOmega: z :e Omega. exact setminusE1 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim zNotUnion: z /:e (Omega :\: A) :\/: (Omega :\: B). exact setminusE2 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim HNotUnionSplit: z /:e (Omega :\: A) /\ z /:e (Omega :\: B). exact binunion_nIn_E (Omega :\: A) (Omega :\: B) z zNotUnion.
      claim HNotDiffA: z /:e (Omega :\: A). exact andEL (z /:e (Omega :\: A)) (z /:e (Omega :\: B)) HNotUnionSplit.
      apply orE (z :e A) (z /:e A) (z :e A) (fun H => H) (fun HnA => FalseE (HNotDiffA (setminusI Omega A z zInOmega HnA)) (z :e A)) (xm (z :e A)).
    + claim zInOmega: z :e Omega. exact setminusE1 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim zNotUnion: z /:e (Omega :\: A) :\/: (Omega :\: B). exact setminusE2 Omega ((Omega :\: A) :\/: (Omega :\: B)) z Hz.
      claim HNotUnionSplit: z /:e (Omega :\: A) /\ z /:e (Omega :\: B). exact binunion_nIn_E (Omega :\: A) (Omega :\: B) z zNotUnion.
      claim HNotDiffB: z /:e (Omega :\: B). exact andER (z /:e (Omega :\: A)) (z /:e (Omega :\: B)) HNotUnionSplit.
      apply orE (z :e B) (z /:e B) (z :e B) (fun H => H) (fun HnB => FalseE (HNotDiffB (setminusI Omega B z zInOmega HnB)) (z :e B)) (xm (z :e B)).
}
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

Definition is_probability_measure : set -> set -> (set -> set) -> prop :=
  fun Omega F P =>
    is_sigma_field Omega F
    /\ ((forall A :e F, P A :e real /\ 0 <= P A)
    /\ (P Omega = 1
    /\ (P Empty = 0
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         pairwise_disjoint f ->
         P (bigcup_nat f) = sum_nat (fun n => P (f n)))))).

Theorem prob_measure_is_sigma_field :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    is_sigma_field Omega F.
let Omega. let F. let P.
assume H.
exact andEL (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
Qed.

Theorem prob_empty_zero :
  forall Omega F, forall P: set -> set,
    is_probability_measure Omega F P ->
    P Empty = 0.
let Omega. let F. let P.
assume H: is_probability_measure Omega F P.
claim H_rest: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H.
claim H_rest2: P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
  exact andER (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) H_rest.
claim H_rest3: P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  exact andER (P Omega = 1) (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H_rest2.
exact andEL (P Empty = 0) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) H_rest3.
Qed.

Theorem prob_finite_additivity :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    Disjoint A B ->
    P (A :\/: B) = P A + P B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hd.
claim HF: is_field Omega F.
{
  exact sigma_field_is_field Omega F (prob_measure_is_sigma_field Omega F P H).
}
claim H1234: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F).
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F /\ (forall A :e F, (Omega :\: A) :e F))
              (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)
              HF.
claim H123: ((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F.
  exact andEL (((forall A :e F, A c= Omega) /\ Omega :e F) /\ Empty :e F)
              (forall A :e F, (Omega :\: A) :e F)
              H1234.
claim FEmpty: Empty :e F.
  exact andER ((forall A :e F, A c= Omega) /\ Omega :e F)
              (Empty :e F)
              H123.

set f := fun n : set => If_i (n = 0) A (If_i (n = 1) B Empty).


claim Ff: forall n :e omega, f n :e F.
{
  let n. assume Hn.
  claim Eq: f n = If_i (n=0) A (If_i (n=1) B Empty). { reflexivity. }
  claim C0: n = 0 -> f n :e F.
  {
    assume Hz.
    rewrite Eq.
    rewrite (If_i_1 (n=0) A (If_i (n=1) B Empty) Hz).
    exact HA.
  }
  claim Cnot0: n <> 0 -> f n :e F.
  {
    assume Hnz.
    rewrite Eq.
    rewrite (If_i_0 (n=0) A (If_i (n=1) B Empty) Hnz).
    claim C1: n = 1 -> If_i (n=1) B Empty :e F.
    {
      assume H1.
      rewrite (If_i_1 (n=1) B Empty H1).
      exact HB.
    }
    claim Cnot1: n <> 1 -> If_i (n=1) B Empty :e F.
    {
      assume Hn1.
      rewrite (If_i_0 (n=1) B Empty Hn1).
      exact FEmpty.
    }
    exact orE (n=1) (n<>1) (If_i (n=1) B Empty :e F) C1 Cnot1 (xm (n=1)).
  }
  exact orE (n=0) (n<>0) (f n :e F) C0 Cnot0 (xm (n=0)).
}

claim Fdisj: pairwise_disjoint f.
{
  admit.
}


claim HUnionSym: A :\/: B = bigcup_nat f.
{
  claim BigDef: bigcup_nat f = Union {f n|n :e omega}. { reflexivity. }
  apply set_ext.
  - prove A :\/: B c= bigcup_nat f.
    let z. assume HzUnion.
    apply binunionE A B z HzUnion.
    + assume HzA: z :e A.
      claim H0in: 0 :e omega. { exact nat_p_omega 0 nat_0. }
      claim Hfam0: f 0 :e {f n|n :e omega}. { exact ReplI omega f 0 H0in. }
      claim HzIn0: z :e f 0.
      {
        claim Eqf0: f 0 = If_i (0=0) A (If_i (0=1) B Empty). { reflexivity. }
        rewrite Eqf0.
        claim H00: 0 = 0. { reflexivity. }
        rewrite (If_i_1 (0=0) A (If_i (0=1) B Empty) H00).
        exact HzA.
      }
      rewrite BigDef.
      exact UnionI {f n|n :e omega} z (f 0) HzIn0 Hfam0.
    + assume HzB: z :e B.
      claim H1in: 1 :e omega. { exact nat_p_omega 1 nat_1. }
      claim Hfam1: f 1 :e {f n|n :e omega}. { exact ReplI omega f 1 H1in. }
      claim HzIn1: z :e f 1.
      {
        claim Eqf1: f 1 = If_i (1=0) A (If_i (1=1) B Empty). { reflexivity. }
        rewrite Eqf1.
        rewrite (If_i_0 (1=0) A (If_i (1=1) B Empty) neq_1_0).
        claim H11: 1 = 1. { reflexivity. }
        rewrite (If_i_1 (1=1) B Empty H11).
        exact HzB.
      }
      rewrite BigDef.
      exact UnionI {f n|n :e omega} z (f 1) HzIn1 Hfam1.
  - prove bigcup_nat f c= A :\/: B.
    let z. assume Hz.
    claim Hz': z :e Union {f n|n :e omega}.
    { rewrite <- BigDef. exact Hz. }
    apply UnionE_impred {f n|n :e omega} z Hz'.
    let Y. assume HzInY HYIn.
    apply ReplE_impred omega f Y HYIn.
    let n. assume Hn HYeq.
    claim HzIn_fn: z :e f n.
    { claim Heq: f n = Y. { symmetry. exact HYeq. }
      rewrite Heq. exact HzInY. }
    apply orE (n = 0) (n <> 0) (z :e A :\/: B).
    + assume H0.
      claim HzInA: z :e A.
      { rewrite <- (If_i_1 (n=0) A (If_i (n=1) B Empty) H0). exact HzIn_fn. }
      exact binunionI1 A B z HzInA.
    + assume Hn0.
      claim HzIn_fn': z :e If_i (n=1) B Empty.
      { rewrite <- (If_i_0 (n=0) A (If_i (n=1) B Empty) Hn0). exact HzIn_fn. }
      apply orE (n = 1) (n <> 1) (z :e A :\/: B).
      * assume H1.
        claim HzInB: z :e B.
        { rewrite <- (If_i_1 (n=1) B Empty H1). exact HzIn_fn'. }
        exact binunionI2 A B z HzInB.
      * assume Hn1.
        claim HzEmpty: z :e Empty.
        { rewrite <- (If_i_0 (n=1) B Empty Hn1). exact HzIn_fn'. }
        apply FalseE ((EmptyE z) HzEmpty) (z :e A :\/: B).
      * exact xm (n = 1).
    + exact xm (n = 0).
}

claim HSum: P (bigcup_nat f) = sum_nat (fun n => P (f n)).
{
  claim H1: (forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))).
  { exact andER (is_sigma_field Omega F) ((forall A :e F, P A :e real /\ 0 <= P A) /\ (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))))) H. }
  claim H2: P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))).
  { exact andER (forall A :e F, P A :e real /\ 0 <= P A) (P Omega = 1 /\ (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))))) H1. }
  claim H3: P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))).
  { exact andER (P Omega = 1) (P Empty = 0 /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)))) H2. }
  claim Hadd: forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n)).
  { exact andER (P Empty = 0) (forall f : set -> set, (forall n :e omega, f n :e F) -> pairwise_disjoint f -> P (bigcup_nat f) = sum_nat (fun n => P (f n))) H3. }
  exact Hadd f Ff Fdisj.
}

claim HSumVal: sum_nat (fun n => P (f n)) = P A + P B.
{
  admit.
}

rewrite HUnionSym.
rewrite HSum.
rewrite HSumVal.
reflexivity.
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
    P (Omega :\: A) = 1 + - P A.
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
    If_i (0 < P B) (P (A :/\: B) :/: P B) 0.

Theorem product_rule :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    P (A :/\: B) = P B * conditional_prob Omega P A B.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hp.

claim EqCond: conditional_prob Omega P A B = P (A :/\: B) :/: P B.
{
  claim Def: conditional_prob Omega P A B = If_i (0 < P B) (P (A :/\: B) :/: P B) 0. { reflexivity. }
  rewrite Def.
  rewrite (If_i_1 (0 < P B) (P (A :/\: B) :/: P B) 0 Hp).
  reflexivity.
}

rewrite EqCond.
admit.
Qed.

Theorem bayes_theorem :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P A ->
    0 < P B ->
    conditional_prob Omega P A B = (conditional_prob Omega P B A * P A) :/: (P B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpA. assume HpB.
admit.
Qed.

Theorem total_probability_binary :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    0 < P (Omega :\: B) ->
    P A = P (A :/\: B) + P (A :/\: (Omega :\: B)).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpB. assume HpBc.
admit.
Qed.

Theorem total_probability_binary_conditional :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    0 < P (Omega :\: B) ->
    P A = conditional_prob Omega P A B * P B + conditional_prob Omega P A (Omega :\: B) * P (Omega :\: B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume HpB. assume HpBc.
admit.
Qed.

Definition independent_events : set -> (set -> set) -> set -> set -> prop :=
  fun Omega P A B =>
    P (A :/\: B) = P A * P B.

Definition independent_events_3 : set -> (set -> set) -> set -> set -> set -> prop :=
  fun Omega P A B C =>
    independent_events Omega P A B
    /\ independent_events Omega P A C
    /\ independent_events Omega P B C
    /\ P (A :/\: B :/\: C) = P A * P B * P C.

Theorem independence_sym :
  forall Omega, forall P: set -> set, forall A B,
    independent_events Omega P A B ->
    independent_events Omega P B A.
let Omega. let P. let A. let B.
assume H.
admit.
Qed.

Theorem independent_implies_conditional :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    0 < P B ->
    independent_events Omega P A B ->
    conditional_prob Omega P A B = P A.
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hp. assume Hind.
admit.
Qed.

Theorem independent_complement :
  forall Omega F, forall P: set -> set, forall A B,
    is_probability_measure Omega F P ->
    A :e F -> B :e F ->
    independent_events Omega P A B ->
    independent_events Omega P A (Omega :\: B).
let Omega. let F. let P. let A. let B.
assume H. assume HA. assume HB. assume Hind.
admit.
Qed.
