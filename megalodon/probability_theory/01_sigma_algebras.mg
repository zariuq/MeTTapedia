Definition bigcup_nat : (set -> set) -> set :=
  fun f => Union {f n | n :e omega}.

Axiom eq_subst_set : forall X Y z:set, X = Y -> z :e X -> z :e Y.

Axiom setminus_inter_compl :
  forall Omega A B,
    A c= Omega ->
    A :\: B = A :/\: (Omega :\: B).

Definition bigcap_nat : set -> (set -> set) -> set :=
  fun Omega f => Omega :\: bigcup_nat (fun n => Omega :\: f n).

Definition is_sigma_algebra : set -> set -> prop :=
  fun Omega F =>
    (forall A :e F, A c= Omega)
    /\ (Empty :e F
    /\ (Omega :e F
    /\ ((forall A :e F, (Omega :\: A) :e F)
    /\ (forall f : set -> set,
         (forall n :e omega, f n :e F) ->
         bigcup_nat f :e F)))).

Definition is_field : set -> set -> prop :=
  fun Omega F =>
    (forall A :e F, A c= Omega)
    /\ (Omega :e F
    /\ (Empty :e F
    /\ ((forall A :e F, (Omega :\: A) :e F)
    /\ (forall A B, A :e F -> B :e F -> (A :\/: B) :e F)))).

Axiom field_closed_under_intersection :
  forall Omega F A B,
    is_field Omega F ->
    A :e F -> B :e F ->
    A :/\: B :e F.

Theorem sigma_algebra_is_field :
  forall Omega F,
    is_sigma_algebra Omega F -> is_field Omega F.
let Omega F. assume Hsigma.
claim Hsub: forall A :e F, A c= Omega.
{ exact andEL (forall A :e F, A c= Omega)
              (Empty :e F /\ (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))))
              Hsigma. }
claim Hrest1: Empty :e F /\ (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))).
{ exact andER (forall A :e F, A c= Omega)
              (Empty :e F /\ (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))))
              Hsigma. }
claim Hempty: Empty :e F.
{ exact andEL (Empty :e F)
              (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F)))
              Hrest1. }
claim Hrest2: Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F)).
{ exact andER (Empty :e F)
              (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F)))
              Hrest1. }
claim Homega: Omega :e F.
{ exact andEL (Omega :e F)
              ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))
              Hrest2. }
claim Hrest3: (forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F).
{ exact andER (Omega :e F)
              ((forall A :e F, (Omega :\: A) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))
              Hrest2. }
claim Hcompl: forall A :e F, (Omega :\: A) :e F.
{ exact andEL (forall A :e F, (Omega :\: A) :e F)
              (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F)
              Hrest3. }
claim Hcount: forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F.
{ exact andER (forall A :e F, (Omega :\: A) :e F)
              (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F)
              Hrest3. }

prove ((forall A :e F, A c= Omega)
       /\ (Omega :e F
       /\ (Empty :e F
       /\ ((forall A :e F, (Omega :\: A) :e F)
       /\ (forall A B, A :e F -> B :e F -> (A :\/: B) :e F))))).
apply andI. { exact Hsub. }
apply andI. { exact Homega. }
apply andI. { exact Hempty. }
apply andI. { exact (fun A HA => Hcompl A HA). }
let A B. assume HA HB.
set f := fun n : set => if n = 0 then A else if n = 1 then B else Empty.
claim Hf: forall n :e omega, f n :e F.
{
  let n. assume Hn.
  claim EqDef: f n = If_i (n = 0) A (If_i (n = 1) B Empty). { reflexivity. }
  rewrite EqDef.
  apply orE (n = 0) (n <> 0) (If_i (n = 0) A (If_i (n = 1) B Empty) :e F).
  - assume H0.
    rewrite (If_i_1 (n = 0) A (If_i (n = 1) B Empty) H0).
    exact HA.
  - assume Hn0.
    rewrite (If_i_0 (n = 0) A (If_i (n = 1) B Empty) Hn0).
    apply orE (n = 1) (n <> 1) (If_i (n = 1) B Empty :e F).
    + assume H1.
      rewrite (If_i_1 (n = 1) B Empty H1).
      exact HB.
    + assume Hn1.
      rewrite (If_i_0 (n = 1) B Empty Hn1).
      exact Hempty.
    + exact xm (n = 1).
  - exact xm (n = 0).
}
claim Hbig: bigcup_nat f :e F.
{ exact Hcount f Hf. }
claim Heq: bigcup_nat f = A :\/: B.
{
  claim BigDef: bigcup_nat f = Union {f n|n :e omega}. { reflexivity. }
  apply set_ext.
  - prove bigcup_nat f c= A :\/: B.
    let z. assume Hz.
    apply UnionE_impred {f n|n :e omega} z Hz.
    let Y. assume HzInY HYIn.
    apply ReplE_impred omega f Y HYIn.
    let n. assume Hn HYeq.
    claim HzInf: z :e f n. { exact eq_subst_set Y (f n) z HYeq HzInY. }
    claim EqFn: f n = If_i (n = 0) A (If_i (n = 1) B Empty). { reflexivity. }
    claim HzInfExp: z :e If_i (n = 0) A (If_i (n = 1) B Empty).
    { exact eq_subst_set (f n) (If_i (n = 0) A (If_i (n = 1) B Empty)) z EqFn HzInf. }
    apply orE (n = 0) (n <> 0) (z :e A :\/: B).
    + assume H0.
      claim HIf0: If_i (n = 0) A (If_i (n = 1) B Empty) = A.
      { exact If_i_1 (n = 0) A (If_i (n = 1) B Empty) H0. }
      claim HzA: z :e A. { exact eq_subst_set (If_i (n = 0) A (If_i (n = 1) B Empty)) A z HIf0 HzInfExp. }
      exact binunionI1 A B z HzA.
    + assume Hn0.
      claim HIfn0: If_i (n = 0) A (If_i (n = 1) B Empty) = If_i (n = 1) B Empty.
      { exact If_i_0 (n = 0) A (If_i (n = 1) B Empty) Hn0. }
      claim HzInf1: z :e If_i (n = 1) B Empty.
      { exact eq_subst_set (If_i (n = 0) A (If_i (n = 1) B Empty)) (If_i (n = 1) B Empty) z HIfn0 HzInfExp. }
      apply orE (n = 1) (n <> 1) (z :e A :\/: B).
      * assume H1.
        claim HIf1: If_i (n = 1) B Empty = B.
        { exact If_i_1 (n = 1) B Empty H1. }
        claim HzB: z :e B. { exact eq_subst_set (If_i (n = 1) B Empty) B z HIf1 HzInf1. }
        exact binunionI2 A B z HzB.
      * assume Hn1.
        claim HIf1c: If_i (n = 1) B Empty = Empty.
        { exact If_i_0 (n = 1) B Empty Hn1. }
        claim HzEmpty: z :e Empty. { exact eq_subst_set (If_i (n = 1) B Empty) Empty z HIf1c HzInf1. }
        apply FalseE ((EmptyE z) HzEmpty) (z :e A :\/: B).
      * exact xm (n = 1).
    + exact xm (n = 0).
  - prove A :\/: B c= bigcup_nat f.
    rewrite BigDef.
    let z. assume HzUnion.
    apply binunionE A B z HzUnion.
    + assume HzA: z :e A.
      claim H0in: 0 :e omega. { exact nat_p_omega 0 nat_0. }
      claim Hfam0: f 0 :e {f n|n :e omega}. { exact ReplI omega f 0 H0in. }
      claim HzIn0: z :e f 0.
      {
        claim Hdef0: f 0 = If_i (0 = 0) A (If_i (0 = 1) B Empty). { reflexivity. }
        rewrite Hdef0.
        claim H00: 0 = 0. { reflexivity. }
        rewrite (If_i_1 (0 = 0) A (If_i (0 = 1) B Empty) H00).
        exact HzA.
      }
      apply UnionI {f n|n :e omega} z (f 0).
      exact HzIn0.
      exact Hfam0.
    + assume HzB: z :e B.
      claim H1in: 1 :e omega. { exact nat_p_omega 1 nat_1. }
      claim Hfam1: f 1 :e {f n|n :e omega}. { exact ReplI omega f 1 H1in. }
      claim HzIn1: z :e f 1.
      {
        claim Hdef1: f 1 = If_i (1 = 0) A (If_i (1 = 1) B Empty). { reflexivity. }
        rewrite Hdef1.
        rewrite (If_i_0 (1 = 0) A (If_i (1 = 1) B Empty) neq_1_0).
        claim H11: 1 = 1. { reflexivity. }
        rewrite (If_i_1 (1 = 1) B Empty H11).
        exact HzB.
      }
      apply UnionI {f n|n :e omega} z (f 1).
      exact HzIn1.
      exact Hfam1.
}
rewrite <- Heq.
exact Hbig.
Qed.

Theorem sigma_algebra_countable_intersection :
  forall Omega F, forall f : set -> set,
    is_sigma_algebra Omega F ->
    (forall n :e omega, f n :e F) ->
    bigcap_nat Omega f :e F.
let Omega F. let f : set -> set. assume Hsigma. assume Hf.
claim Hcore: Empty :e F /\ (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F))).
{ exact andER (forall A :e F, A c= Omega)
              (Empty :e F /\ (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F))))
              Hsigma. }
claim Hrest2: Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)).
{ exact andER (Empty :e F)
              (Omega :e F /\ ((forall A :e F, (Omega :\: A) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)))
              Hcore. }
claim Hcompl: forall A :e F, (Omega :\: A) :e F.
{ exact andEL (forall A :e F, (Omega :\: A) :e F)
              (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)
              (andER (Omega :e F)
                     ((forall A :e F, (Omega :\: A) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F))
                     Hrest2). }
claim Hcount: forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F.
{ exact andER (forall A :e F, (Omega :\: A) :e F)
              (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)
              (andER (Omega :e F)
                     ((forall A :e F, (Omega :\: A) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F))
                     Hrest2). }
set g := fun n : set => Omega :\: f n.
claim Hg: forall n :e omega, g n :e F.
{
  let n. assume Hn.
  claim Hgn: g n = Omega :\: f n. { reflexivity. }
  rewrite Hgn.
  exact Hcompl (f n) (Hf n Hn).
}
claim Hunion: bigcup_nat g :e F.
{ exact Hcount g Hg. }
claim Hcapdef: bigcap_nat Omega f = Omega :\: bigcup_nat g. { reflexivity. }
rewrite Hcapdef.
exact Hcompl (bigcup_nat g) Hunion.
Qed.

Theorem power_set_is_sigma_algebra :
  forall Omega, is_sigma_algebra Omega (Power Omega).
let Omega.
prove ((forall A :e Power Omega, A c= Omega)
       /\ (Empty :e Power Omega
       /\ (Omega :e Power Omega
       /\ ((forall A :e Power Omega, (Omega :\: A) :e Power Omega)
       /\ (forall f : set -> set,
            (forall n :e omega, f n :e Power Omega) ->
            bigcup_nat f :e Power Omega))))).
apply andI.
- let A. assume HA. exact PowerE Omega A HA.
- apply andI.
  + exact Empty_In_Power Omega.
  + apply andI.
    * exact Self_In_Power Omega.
    * apply andI.
      let A. assume HA. apply PowerI. apply setminus_Subq.
      let f. assume Hf.
      apply PowerI.
      let z. assume HzUnion.
      apply UnionE_impred {f n|n :e omega} z HzUnion.
      let Y. assume HzInY HYIn.
      apply ReplE_impred omega f Y HYIn.
      let n. assume Hn HYeq.
      claim HzInf: z :e f n. { exact eq_subst_set Y (f n) z HYeq HzInY. }
      claim Hsub: f n c= Omega. { exact PowerE Omega (f n) (Hf n Hn). }
      exact Hsub z HzInf.
Qed.

Theorem sigma_algebra_finite_union :
  forall Omega F A B,
    is_sigma_algebra Omega F ->
    A :e F -> B :e F ->
    A :\/: B :e F.
let Omega F A B. assume Hsigma HA HB.
claim HF: is_field Omega F. { exact sigma_algebra_is_field Omega F Hsigma. }
claim Hrest1: Omega :e F /\ (Empty :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F))).
{ exact andER (forall A0 :e F, A0 c= Omega)
              (Omega :e F /\ (Empty :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F))))
              HF. }
claim Hrest2: Empty :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F)).
{ exact andER (Omega :e F)
              (Empty :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F)))
              Hrest1. }
claim Hrest3: (forall A0 :e F, (Omega :\: A0) :e F) /\ (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F).
{ exact andER (Empty :e F)
              ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F))
              Hrest2. }
claim Hunion: forall X Y, X :e F -> Y :e F -> (X :\/: Y) :e F.
{ exact andER (forall A0 :e F, (Omega :\: A0) :e F)
              (forall A0 B0, A0 :e F -> B0 :e F -> (A0 :\/: B0) :e F)
              Hrest3. }
exact Hunion A B HA HB.
Qed.

Theorem sigma_algebra_finite_intersection :
  forall Omega F A B,
    is_sigma_algebra Omega F ->
    A :e F -> B :e F ->
    A :/\: B :e F.
let Omega F A B. assume Hsigma HA HB.
claim HF: is_field Omega F. { exact sigma_algebra_is_field Omega F Hsigma. }
exact field_closed_under_intersection Omega F A B HF HA HB.
Qed.

Theorem sigma_algebra_setminus :
  forall Omega F A B,
    is_sigma_algebra Omega F ->
    A :e F -> B :e F ->
    A :\: B :e F.
let Omega F A B. assume Hsigma HA HB.
claim Hcore: Empty :e F /\ (Omega :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))).
{ exact andER (forall A0 :e F, A0 c= Omega)
              (Empty :e F /\ (Omega :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))))
              Hsigma. }
claim Hsub: forall X :e F, X c= Omega.
{ exact andEL (forall A0 :e F, A0 c= Omega)
              (Empty :e F /\ (Omega :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall f : set -> set, (forall n :e omega, f n :e F) -> bigcup_nat f :e F))))
              Hsigma. }
claim Hrest2: Omega :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)).
{ exact andER (Empty :e F)
              (Omega :e F /\ ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)))
              Hcore. }
claim Hcompl: forall X :e F, (Omega :\: X) :e F.
{ exact andEL (forall A0 :e F, (Omega :\: A0) :e F)
              (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F)
              (andER (Omega :e F)
                     ((forall A0 :e F, (Omega :\: A0) :e F) /\ (forall f0 : set -> set, (forall n :e omega, f0 n :e F) -> bigcup_nat f0 :e F))
                     Hrest2). }
claim HBc: (Omega :\: B) :e F. { exact Hcompl B HB. }
claim HF: is_field Omega F. { exact sigma_algebra_is_field Omega F Hsigma. }
claim Hinter: A :/\: (Omega :\: B) :e F. { exact field_closed_under_intersection Omega F A (Omega :\: B) HF HA HBc. }
claim HeqDiff: A :\: B = A :/\: (Omega :\: B). { exact setminus_inter_compl Omega A B (Hsub A HA). }
rewrite HeqDiff.
exact Hinter.
Qed.
