(** This source continues NaturalClosure.mg in the same checked input.
    The recursive graph uses explicit logical interfaces. No natural-number
    fact or set-theoretic axiom is admitted by this file. **)

Definition nrFalse : prop := forall P:prop, P.

Section NaturalRecursionLogic.
Variable A:SType.

Definition nrEq : A->A->prop := fun x y:A => forall P:A->prop, P x -> P y.
Definition nrExists : (A->prop)->prop :=
  fun P:A->prop => forall Q:prop, (forall x:A, P x -> Q) -> Q.

Theorem nrEqRefl : forall x:A, nrEq x x.
let x P.
assume H:P x.
exact H.
Qed.

Theorem nrEqSym : forall x y:A, nrEq x y -> nrEq y x.
let x y.
assume H:nrEq x y.
exact H (fun z:A => nrEq z x) (nrEqRefl x).
Qed.

Theorem nrEqTrans : forall x y z:A, nrEq x y -> nrEq y z -> nrEq x z.
let x y z.
assume Hxy:nrEq x y.
assume Hyz:nrEq y z.
let P.
assume HP:P x.
exact Hyz P (Hxy P HP).
Qed.

Theorem nrExistsIntro : forall P:A->prop, forall x:A, P x -> nrExists P.
let P x.
assume H:P x.
let Q.
assume K:forall y:A, P y -> Q.
exact K x H.
Qed.

End NaturalRecursionLogic.

Section NaturalRecursionGraph.
Variable A:SType.

Definition nrGraph : set -> (set->set) -> A -> (set->A->A) -> set -> A -> prop :=
  fun zero:set => fun successor:set->set => fun start:A => fun step:set->A->A =>
  fun number:set => fun value:A => forall R:set->A->prop,
    R zero start ->
    (forall previous:set, forall prior:A, R previous prior -> R (successor previous) (step previous prior)) ->
    R number value.

Theorem nrGraphZero : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, nrGraph zero successor start step zero start.
let zero successor start step R.
assume Hzero:R zero start.
assume Hstep:forall previous:set, forall prior:A,
  R previous prior -> R (successor previous) (step previous prior).
exact Hzero.
Qed.

Theorem nrGraphSuccessor : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, forall number:set, forall value:A,
    nrGraph zero successor start step number value ->
    nrGraph zero successor start step (successor number) (step number value).
let zero successor start step number value.
assume H:nrGraph zero successor start step number value.
let R.
assume Hzero:R zero start.
assume Hstep:forall previous:set, forall prior:A,
  R previous prior -> R (successor previous) (step previous prior).
exact Hstep number value (H R Hzero Hstep).
Qed.

Theorem nrGraphNatural : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, forall number:set, forall value:A,
    nrGraph zero successor start step number value -> naturalClosure zero successor number.
let zero successor start step number value.
assume H:nrGraph zero successor start step number value.
exact H (fun n:set => fun v:A => naturalClosure zero successor n)
  (naturalClosureZero zero successor)
  (fun n:set => fun v:A => fun Hn:naturalClosure zero successor n =>
    naturalClosureSuccessor zero successor n Hn).
Qed.

Theorem nrGraphExists : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, forall number:set,
    naturalClosure zero successor number -> nrExists A (fun value:A => nrGraph zero successor start step number value).
let zero successor start step number.
assume H:naturalClosure zero successor number.
exact H (fun n:set => nrExists A (fun value:A => nrGraph zero successor start step n value))
  (nrExistsIntro A (fun value:A => nrGraph zero successor start step zero value) start
    (nrGraphZero zero successor start step))
  (fun n:set => fun IH:nrExists A (fun value:A => nrGraph zero successor start step n value) =>
    IH (nrExists A (fun value:A => nrGraph zero successor start step (successor n) value))
      (fun value:A => fun Hv:nrGraph zero successor start step n value =>
        nrExistsIntro A (fun next:A => nrGraph zero successor start step (successor n) next)
          (step n value) (nrGraphSuccessor zero successor start step n value Hv))).
Qed.

Theorem nrGraphZeroUnique : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  forall start:A, forall step:set->A->A, forall value:A,
    nrGraph zero successor start step zero value -> nrEq A start value.
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
let start step value.
assume H:nrGraph zero successor start step zero value.
let P.
assume Hstart:P start.
exact H (fun n:set => fun v:A => nrEq set n zero -> P v)
  (fun ignored:nrEq set zero zero => Hstart)
  (fun n:set => fun v:A => fun ignored:nrEq set n zero -> P v =>
    fun impossible:nrEq set (successor n) zero => (different n impossible) (P (step n v)))
  (nrEqRefl set zero).
Qed.

Theorem nrGraphSuccessorInverse : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  (forall left right:set, nrEq set (successor left) (successor right) -> nrEq set left right) ->
  forall start:A, forall step:set->A->A, forall number:set, forall value:A,
    nrGraph zero successor start step (successor number) value ->
    nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step number prior)
      (nrEq A (step number prior) value)).
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
assume injective:forall left right:set,
  nrEq set (successor left) (successor right) -> nrEq set left right.
let start step number value.
assume H:nrGraph zero successor start step (successor number) value.
claim initial:ncAnd (nrGraph zero successor start step zero start)
  (forall previous:set, nrEq set (successor previous) zero ->
    nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
      (nrEq A (step previous prior) start))).
{
  apply ncAndIntro.
  - exact nrGraphZero zero successor start step.
  - let previous.
    assume impossible:nrEq set (successor previous) zero.
    exact different previous impossible
      (nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) start))).
}
claim closed:forall current:set, forall output:A,
  ncAnd (nrGraph zero successor start step current output)
    (forall previous:set, nrEq set (successor previous) current ->
      nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) output))) ->
  ncAnd (nrGraph zero successor start step (successor current) (step current output))
    (forall previous:set, nrEq set (successor previous) (successor current) ->
      nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) (step current output)))).
{
  let current output.
  assume IH:ncAnd (nrGraph zero successor start step current output)
    (forall previous:set, nrEq set (successor previous) current ->
      nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) output))).
  claim Hcurrent:nrGraph zero successor start step current output.
  { exact ncAndLeft (nrGraph zero successor start step current output)
    (forall previous:set, nrEq set (successor previous) current ->
      nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) output))) IH. }
  apply ncAndIntro.
  - exact nrGraphSuccessor zero successor start step current output Hcurrent.
  - let previous.
    assume same:nrEq set (successor previous) (successor current).
    claim before:nrEq set previous current.
    { exact injective previous current same. }
    apply nrExistsIntro A (fun prior:A =>
      ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) (step current output))) output.
    apply ncAndIntro.
    - exact nrEqSym set previous current before
        (fun n:set => nrGraph zero successor start step n output) Hcurrent.
    - exact before (fun n:set => nrEq A (step previous output) (step n output))
        (nrEqRefl A (step previous output)).
}
claim result:ncAnd (nrGraph zero successor start step (successor number) value)
  (forall previous:set, nrEq set (successor previous) (successor number) ->
    nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
      (nrEq A (step previous prior) value))).
{
  exact H (fun n:set => fun v:A => ncAnd (nrGraph zero successor start step n v)
    (forall previous:set, nrEq set (successor previous) n ->
      nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
        (nrEq A (step previous prior) v)))) initial closed.
}
exact ncAndRight (nrGraph zero successor start step (successor number) value)
  (forall previous:set, nrEq set (successor previous) (successor number) ->
    nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step previous prior)
      (nrEq A (step previous prior) value))) result number (nrEqRefl set (successor number)).
Qed.

Theorem nrGraphFunctional : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  (forall left right:set, nrEq set (successor left) (successor right) -> nrEq set left right) ->
  forall start:A, forall step:set->A->A, forall number:set,
    naturalClosure zero successor number ->
    forall left right:A, nrGraph zero successor start step number left ->
      nrGraph zero successor start step number right -> nrEq A left right.
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
assume injective:forall left right:set,
  nrEq set (successor left) (successor right) -> nrEq set left right.
let start step number.
assume Hnumber:naturalClosure zero successor number.
claim initial:forall left right:A, nrGraph zero successor start step zero left ->
  nrGraph zero successor start step zero right -> nrEq A left right.
{
  let left right.
  assume HL:nrGraph zero successor start step zero left.
  assume HR:nrGraph zero successor start step zero right.
  exact nrEqTrans A left start right
    (nrEqSym A start left (nrGraphZeroUnique zero successor different start step left HL))
    (nrGraphZeroUnique zero successor different start step right HR).
}
claim closed:forall n:set, naturalClosure zero successor n ->
  (forall left right:A, nrGraph zero successor start step n left ->
    nrGraph zero successor start step n right -> nrEq A left right) ->
  forall left right:A, nrGraph zero successor start step (successor n) left ->
    nrGraph zero successor start step (successor n) right -> nrEq A left right.
{
  let n.
  assume Hnatural:naturalClosure zero successor n.
  assume IH:forall left right:A, nrGraph zero successor start step n left ->
    nrGraph zero successor start step n right -> nrEq A left right.
  let left right.
  assume HL:nrGraph zero successor start step (successor n) left.
  assume HR:nrGraph zero successor start step (successor n) right.
  claim leftPre:nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step n prior)
    (nrEq A (step n prior) left)).
  { exact nrGraphSuccessorInverse zero successor different injective start step n left HL. }
  claim rightPre:nrExists A (fun prior:A => ncAnd (nrGraph zero successor start step n prior)
    (nrEq A (step n prior) right)).
  { exact nrGraphSuccessorInverse zero successor different injective start step n right HR. }
  apply leftPre.
  let l.
  assume L:ncAnd (nrGraph zero successor start step n l) (nrEq A (step n l) left).
  apply rightPre.
  let r.
  assume R:ncAnd (nrGraph zero successor start step n r) (nrEq A (step n r) right).
  claim Gl:nrGraph zero successor start step n l.
  { exact ncAndLeft (nrGraph zero successor start step n l) (nrEq A (step n l) left) L. }
  claim Gr:nrGraph zero successor start step n r.
  { exact ncAndLeft (nrGraph zero successor start step n r) (nrEq A (step n r) right) R. }
  claim El:nrEq A (step n l) left.
  { exact ncAndRight (nrGraph zero successor start step n l) (nrEq A (step n l) left) L. }
  claim Er:nrEq A (step n r) right.
  { exact ncAndRight (nrGraph zero successor start step n r) (nrEq A (step n r) right) R. }
  claim same:nrEq A l r.
  { exact IH l r Gl Gr. }
  claim images:nrEq A (step n l) (step n r).
  { exact same (fun x:A => nrEq A (step n l) (step n x)) (nrEqRefl A (step n l)). }
  exact nrEqTrans A left (step n l) right (nrEqSym A (step n l) left El)
    (nrEqTrans A (step n l) (step n r) right images Er).
}
exact naturalClosureInduction zero successor
  (fun n:set => forall left right:A, nrGraph zero successor start step n left ->
    nrGraph zero successor start step n right -> nrEq A left right)
  initial closed number Hnumber.
Qed.

Definition nrRecursor : set -> (set->set) -> A -> (set->A->A) -> ((A->prop)->A) -> set -> A :=
  fun zero:set => fun successor:set->set => fun start:A => fun step:set->A->A =>
    fun choose:(A->prop)->A => fun number:set =>
      choose (nrGraph zero successor start step number).

Theorem nrRecursorGraph : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, forall choose:(A->prop)->A,
    (forall P:A->prop, nrExists A P -> P (choose P)) ->
    forall number:set, naturalClosure zero successor number ->
      nrGraph zero successor start step number (nrRecursor zero successor start step choose number).
let zero successor start step choose.
assume selects:forall P:A->prop, nrExists A P -> P (choose P).
let number.
assume Hnumber:naturalClosure zero successor number.
exact selects (fun value:A => nrGraph zero successor start step number value)
  (nrGraphExists zero successor start step number Hnumber).
Qed.

Theorem nrRecursorZero : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  forall start:A, forall step:set->A->A, forall choose:(A->prop)->A,
    (forall P:A->prop, nrExists A P -> P (choose P)) ->
    nrEq A start (nrRecursor zero successor start step choose zero).
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
let start step choose.
assume selects:forall P:A->prop, nrExists A P -> P (choose P).
exact nrGraphZeroUnique zero successor different start step
  (nrRecursor zero successor start step choose zero)
  (nrRecursorGraph zero successor start step choose selects zero (naturalClosureZero zero successor)).
Qed.

Theorem nrRecursorSuccessor : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  (forall left right:set, nrEq set (successor left) (successor right) -> nrEq set left right) ->
  forall start:A, forall step:set->A->A, forall choose:(A->prop)->A,
    (forall P:A->prop, nrExists A P -> P (choose P)) ->
    forall number:set, naturalClosure zero successor number ->
      nrEq A (step number (nrRecursor zero successor start step choose number))
        (nrRecursor zero successor start step choose (successor number)).
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
assume injective:forall left right:set,
  nrEq set (successor left) (successor right) -> nrEq set left right.
let start step choose.
assume selects:forall P:A->prop, nrExists A P -> P (choose P).
let number.
assume Hnumber:naturalClosure zero successor number.
claim current:nrGraph zero successor start step number
  (nrRecursor zero successor start step choose number).
{ exact nrRecursorGraph zero successor start step choose selects number Hnumber. }
exact nrGraphFunctional zero successor different injective start step (successor number)
  (naturalClosureSuccessor zero successor number Hnumber)
  (step number (nrRecursor zero successor start step choose number))
  (nrRecursor zero successor start step choose (successor number))
  (nrGraphSuccessor zero successor start step number
    (nrRecursor zero successor start step choose number) current)
  (nrRecursorGraph zero successor start step choose selects (successor number)
    (naturalClosureSuccessor zero successor number Hnumber)).
Qed.

Theorem nrGraphAgrees : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, forall candidate:set->A,
    nrEq A start (candidate zero) ->
    (forall number:set, naturalClosure zero successor number ->
      nrEq A (step number (candidate number)) (candidate (successor number))) ->
    forall number:set, forall value:A,
      nrGraph zero successor start step number value -> nrEq A value (candidate number).
let zero successor start step candidate.
assume atZero:nrEq A start (candidate zero).
assume atSuccessor:forall number:set, naturalClosure zero successor number ->
  nrEq A (step number (candidate number)) (candidate (successor number)).
let number value.
assume H:nrGraph zero successor start step number value.
claim initial:ncAnd (naturalClosure zero successor zero) (nrEq A start (candidate zero)).
{ exact ncAndIntro (naturalClosure zero successor zero) (nrEq A start (candidate zero))
    (naturalClosureZero zero successor) atZero. }
claim closed:forall n:set, forall v:A,
  ncAnd (naturalClosure zero successor n) (nrEq A v (candidate n)) ->
  ncAnd (naturalClosure zero successor (successor n)) (nrEq A (step n v) (candidate (successor n))).
{
  let n v.
  assume IH:ncAnd (naturalClosure zero successor n) (nrEq A v (candidate n)).
  claim Hnatural:naturalClosure zero successor n.
  { exact ncAndLeft (naturalClosure zero successor n) (nrEq A v (candidate n)) IH. }
  claim Hv:nrEq A v (candidate n).
  { exact ncAndRight (naturalClosure zero successor n) (nrEq A v (candidate n)) IH. }
  apply ncAndIntro.
  - exact naturalClosureSuccessor zero successor n Hnatural.
  - exact nrEqTrans A (step n v) (step n (candidate n)) (candidate (successor n))
      (Hv (fun output:A => nrEq A (step n v) (step n output)) (nrEqRefl A (step n v)))
      (atSuccessor n Hnatural).
}
claim result:ncAnd (naturalClosure zero successor number) (nrEq A value (candidate number)).
{ exact H (fun n:set => fun v:A => ncAnd (naturalClosure zero successor n)
    (nrEq A v (candidate n))) initial closed. }
exact ncAndRight (naturalClosure zero successor number) (nrEq A value (candidate number)) result.
Qed.

Theorem nrRecursorUnique : forall zero:set, forall successor:set->set,
  forall start:A, forall step:set->A->A, forall choose:(A->prop)->A,
    (forall P:A->prop, nrExists A P -> P (choose P)) ->
    forall candidate:set->A,
      nrEq A start (candidate zero) ->
      (forall number:set, naturalClosure zero successor number ->
        nrEq A (step number (candidate number)) (candidate (successor number))) ->
      forall number:set, naturalClosure zero successor number ->
        nrEq A (nrRecursor zero successor start step choose number) (candidate number).
let zero successor start step choose.
assume selects:forall P:A->prop, nrExists A P -> P (choose P).
let candidate.
assume atZero:nrEq A start (candidate zero).
assume atSuccessor:forall number:set, naturalClosure zero successor number ->
  nrEq A (step number (candidate number)) (candidate (successor number)).
let number.
assume Hnumber:naturalClosure zero successor number.
exact nrGraphAgrees zero successor start step candidate atZero atSuccessor number
  (nrRecursor zero successor start step choose number)
  (nrRecursorGraph zero successor start step choose selects number Hnumber).
Qed.

Theorem nrRecursorChoiceIndependent : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  (forall left right:set, nrEq set (successor left) (successor right) -> nrEq set left right) ->
  forall start:A, forall step:set->A->A, forall first second:(A->prop)->A,
    (forall P:A->prop, nrExists A P -> P (first P)) ->
    (forall P:A->prop, nrExists A P -> P (second P)) ->
    forall number:set, naturalClosure zero successor number ->
      nrEq A (nrRecursor zero successor start step first number)
        (nrRecursor zero successor start step second number).
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
assume injective:forall left right:set,
  nrEq set (successor left) (successor right) -> nrEq set left right.
let start step first second.
assume firstSelects:forall P:A->prop, nrExists A P -> P (first P).
assume secondSelects:forall P:A->prop, nrExists A P -> P (second P).
exact nrRecursorUnique zero successor start step first firstSelects
  (nrRecursor zero successor start step second)
  (nrRecursorZero zero successor different start step second secondSelects)
  (nrRecursorSuccessor zero successor different injective start step second secondSelects).
Qed.

Theorem nrRecursion : forall zero:set, forall successor:set->set,
  (forall number:set, nrEq set (successor number) zero -> nrFalse) ->
  (forall left right:set, nrEq set (successor left) (successor right) -> nrEq set left right) ->
  forall start:A, forall step:set->A->A, forall choose:(A->prop)->A,
    (forall P:A->prop, nrExists A P -> P (choose P)) ->
    nrExists (set->A) (fun recurse:set->A =>
      ncAnd (nrEq A start (recurse zero))
        (ncAnd
          (forall number:set, naturalClosure zero successor number ->
            nrEq A (step number (recurse number)) (recurse (successor number)))
          (forall candidate:set->A,
            nrEq A start (candidate zero) ->
            (forall number:set, naturalClosure zero successor number ->
              nrEq A (step number (candidate number)) (candidate (successor number))) ->
            forall number:set, naturalClosure zero successor number -> nrEq A (recurse number) (candidate number)))).
let zero successor.
assume different:forall number:set, nrEq set (successor number) zero -> nrFalse.
assume injective:forall left right:set,
  nrEq set (successor left) (successor right) -> nrEq set left right.
let start step choose.
assume selects:forall P:A->prop, nrExists A P -> P (choose P).
apply nrExistsIntro (set->A)
  (fun recurse:set->A => ncAnd (nrEq A start (recurse zero))
    (ncAnd
      (forall number:set, naturalClosure zero successor number ->
        nrEq A (step number (recurse number)) (recurse (successor number)))
      (forall candidate:set->A,
        nrEq A start (candidate zero) ->
        (forall number:set, naturalClosure zero successor number ->
          nrEq A (step number (candidate number)) (candidate (successor number))) ->
        forall number:set, naturalClosure zero successor number -> nrEq A (recurse number) (candidate number))))
  (nrRecursor zero successor start step choose).
apply ncAndIntro.
- exact nrRecursorZero zero successor different start step choose selects.
- apply ncAndIntro.
  - exact nrRecursorSuccessor zero successor different injective start step choose selects.
  - exact nrRecursorUnique zero successor start step choose selects.
Qed.

End NaturalRecursionGraph.
