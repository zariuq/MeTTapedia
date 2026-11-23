Definition ncAnd : prop -> prop -> prop :=
  fun P Q:prop => forall R:prop, (P -> Q -> R) -> R.

Definition naturalClosure : set -> (set -> set) -> set -> prop :=
  fun zero:set => fun successor:set->set => fun number:set =>
    forall P:set->prop,
      P zero -> (forall previous:set, P previous -> P (successor previous)) -> P number.

Theorem ncAndIntro : forall P Q:prop, P -> Q -> ncAnd P Q.
let P Q.
assume HP:P.
assume HQ:Q.
let R.
assume H:P->Q->R.
exact H HP HQ.
Qed.

Theorem ncAndLeft : forall P Q:prop, ncAnd P Q -> P.
let P Q.
assume H:ncAnd P Q.
exact H P (fun HP:P => fun HQ:Q => HP).
Qed.

Theorem ncAndRight : forall P Q:prop, ncAnd P Q -> Q.
let P Q.
assume H:ncAnd P Q.
exact H Q (fun HP:P => fun HQ:Q => HQ).
Qed.

Theorem naturalClosureZero : forall zero:set, forall successor:set->set,
  naturalClosure zero successor zero.
let zero successor.
let P.
assume Hzero:P zero.
assume Hstep:forall previous:set, P previous -> P (successor previous).
exact Hzero.
Qed.

Theorem naturalClosureSuccessor : forall zero:set, forall successor:set->set,
  forall number:set,
    naturalClosure zero successor number -> naturalClosure zero successor (successor number).
let zero successor number.
assume Hnumber:naturalClosure zero successor number.
let P.
assume Hzero:P zero.
assume Hstep:forall previous:set, P previous -> P (successor previous).
exact Hstep number (Hnumber P Hzero Hstep).
Qed.

Theorem naturalClosureInduction : forall zero:set, forall successor:set->set,
  forall P:set->prop,
    P zero ->
    (forall number:set, naturalClosure zero successor number -> P number -> P (successor number)) ->
    forall number:set, naturalClosure zero successor number -> P number.
let zero successor P.
assume Hzero:P zero.
assume Hstep:forall number:set,
  naturalClosure zero successor number -> P number -> P (successor number).
let number.
assume Hnumber:naturalClosure zero successor number.
claim start:ncAnd (naturalClosure zero successor zero) (P zero).
{
  exact ncAndIntro (naturalClosure zero successor zero) (P zero)
    (naturalClosureZero zero successor) Hzero.
}
claim step:forall previous:set,
  ncAnd (naturalClosure zero successor previous) (P previous) ->
  ncAnd (naturalClosure zero successor (successor previous)) (P (successor previous)).
{
  let previous.
  assume Hprevious:ncAnd (naturalClosure zero successor previous) (P previous).
  claim Hnatural:naturalClosure zero successor previous.
  {
    exact ncAndLeft (naturalClosure zero successor previous) (P previous) Hprevious.
  }
  claim Hpredicate:P previous.
  {
    exact ncAndRight (naturalClosure zero successor previous) (P previous) Hprevious.
  }
  exact ncAndIntro (naturalClosure zero successor (successor previous)) (P (successor previous))
    (naturalClosureSuccessor zero successor previous Hnatural)
    (Hstep previous Hnatural Hpredicate).
}
claim reached:ncAnd (naturalClosure zero successor number) (P number).
{
  exact Hnumber (fun previous:set => ncAnd (naturalClosure zero successor previous) (P previous))
    start step.
}
exact ncAndRight (naturalClosure zero successor number) (P number) reached.
Qed.
