(** Continues NaturalClosure.mg and NaturalRecursion.mg.
    The carrier is constructed from explicitly quantified logical interfaces.
    This file admits no axioms and supplies no default theory options. **)

Definition niClassical : prop :=
  forall P:prop, ((P -> nrFalse) -> nrFalse) -> P.

Section NaturalCarrierClassical.
Variable A:SType.

Theorem niNotAll : niClassical -> forall P:A->prop,
  ((forall x:A, P x) -> nrFalse) -> nrExists A (fun x:A => P x -> nrFalse).
assume classical:niClassical.
let P.
assume notAll:(forall x:A, P x) -> nrFalse.
apply classical (nrExists A (fun x:A => P x -> nrFalse)).
assume noWitness:nrExists A (fun x:A => P x -> nrFalse) -> nrFalse.
apply notAll.
let x.
apply classical (P x).
assume notPx:P x -> nrFalse.
exact noWitness (nrExistsIntro A (fun y:A => P y -> nrFalse) x notPx).
Qed.

End NaturalCarrierClassical.

Definition niInjective : (set->set)->prop := fun f:set->set =>
  forall left right:set, nrEq set (f left) (f right) -> nrEq set left right.

Definition niOnto : (set->set)->prop := fun f:set->set =>
  forall target:set, nrExists set (fun source:set => nrEq set target (f source)).

Definition niInfiniteFunction : (set->set)->prop := fun f:set->set =>
  ncAnd (niInjective f) (niOnto f -> nrFalse).

Definition niInfinity : prop := nrExists (set->set) niInfiniteFunction.

Theorem niNotOntoHasOmitted : niClassical -> forall f:set->set,
  (niOnto f -> nrFalse) ->
  nrExists set (fun missing:set => forall source:set, nrEq set (f source) missing -> nrFalse).
assume classical:niClassical.
let f.
assume notOnto:niOnto f -> nrFalse.
claim missing:nrExists set
  (fun target:set => nrExists set (fun source:set => nrEq set target (f source)) -> nrFalse).
{
  exact niNotAll set classical
    (fun target:set => nrExists set (fun source:set => nrEq set target (f source))) notOnto.
}
apply missing (nrExists set
  (fun target:set => forall source:set, nrEq set (f source) target -> nrFalse)).
let target.
assume omitted:nrExists set (fun source:set => nrEq set target (f source)) -> nrFalse.
apply nrExistsIntro set
  (fun missing:set => forall source:set, nrEq set (f source) missing -> nrFalse) target.
let source.
assume same:nrEq set (f source) target.
exact omitted (nrExistsIntro set (fun n:set => nrEq set target (f n)) source
  (nrEqSym set (f source) target same)).
Qed.

Definition niSuccessor : (((set->set)->prop)->(set->set))->set->set :=
  fun choose:((set->set)->prop)->(set->set) => choose niInfiniteFunction.

Definition niZero : ((set->prop)->set)->(((set->set)->prop)->(set->set))->set :=
  fun chooseNumber:(set->prop)->set =>
  fun chooseFunction:((set->set)->prop)->(set->set) =>
  chooseNumber (fun missing:set => forall source:set,
    nrEq set (niSuccessor chooseFunction source) missing -> nrFalse).

Theorem niSuccessorInjective : forall choose:((set->set)->prop)->(set->set),
  (forall P:(set->set)->prop, nrExists (set->set) P -> P (choose P)) ->
  niInfinity -> niInjective (niSuccessor choose).
let choose.
assume selects:forall P:(set->set)->prop, nrExists (set->set) P -> P (choose P).
assume infinite:niInfinity.
exact ncAndLeft (niInjective (niSuccessor choose)) (niOnto (niSuccessor choose) -> nrFalse)
  (selects niInfiniteFunction infinite).
Qed.

Theorem niSuccessorNotOnto : forall choose:((set->set)->prop)->(set->set),
  (forall P:(set->set)->prop, nrExists (set->set) P -> P (choose P)) ->
  niInfinity -> niOnto (niSuccessor choose) -> nrFalse.
let choose.
assume selects:forall P:(set->set)->prop, nrExists (set->set) P -> P (choose P).
assume infinite:niInfinity.
exact ncAndRight (niInjective (niSuccessor choose)) (niOnto (niSuccessor choose) -> nrFalse)
  (selects niInfiniteFunction infinite).
Qed.

Theorem niZeroNotSuccessor : niClassical ->
  forall chooseNumber:(set->prop)->set,
  forall chooseFunction:((set->set)->prop)->(set->set),
  (forall P:set->prop, nrExists set P -> P (chooseNumber P)) ->
  (forall P:(set->set)->prop, nrExists (set->set) P -> P (chooseFunction P)) ->
  niInfinity -> forall number:set,
    nrEq set (niSuccessor chooseFunction number) (niZero chooseNumber chooseFunction) -> nrFalse.
assume classical:niClassical.
let chooseNumber chooseFunction.
assume selectsNumber:forall P:set->prop, nrExists set P -> P (chooseNumber P).
assume selectsFunction:forall P:(set->set)->prop,
  nrExists (set->set) P -> P (chooseFunction P).
assume infinite:niInfinity.
exact selectsNumber
  (fun missing:set => forall source:set, nrEq set (niSuccessor chooseFunction source) missing -> nrFalse)
  (niNotOntoHasOmitted classical (niSuccessor chooseFunction)
    (niSuccessorNotOnto chooseFunction selectsFunction infinite)).
Qed.

Theorem niNaturalZero : forall chooseNumber:(set->prop)->set,
  forall chooseFunction:((set->set)->prop)->(set->set),
  naturalClosure (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction)
    (niZero chooseNumber chooseFunction).
let chooseNumber chooseFunction.
exact naturalClosureZero (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction).
Qed.

Theorem niNaturalSuccessor : forall chooseNumber:(set->prop)->set,
  forall chooseFunction:((set->set)->prop)->(set->set),
  forall number:set,
  naturalClosure (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction) number ->
  naturalClosure (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction)
    (niSuccessor chooseFunction number).
let chooseNumber chooseFunction number.
exact naturalClosureSuccessor (niZero chooseNumber chooseFunction)
  (niSuccessor chooseFunction) number.
Qed.

Section InfiniteNaturalRecursion.
Variable A:SType.

Theorem niRecursion : niClassical ->
  forall chooseNumber:(set->prop)->set,
  forall chooseFunction:((set->set)->prop)->(set->set),
  (forall P:set->prop, nrExists set P -> P (chooseNumber P)) ->
  (forall P:(set->set)->prop, nrExists (set->set) P -> P (chooseFunction P)) ->
  niInfinity ->
  forall start:A, forall step:set->A->A, forall choose:(A->prop)->A,
  (forall P:A->prop, nrExists A P -> P (choose P)) ->
  nrExists (set->A) (fun recurse:set->A =>
    ncAnd (nrEq A start (recurse (niZero chooseNumber chooseFunction)))
      (ncAnd
        (forall number:set,
          naturalClosure (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction) number ->
          nrEq A (step number (recurse number)) (recurse (niSuccessor chooseFunction number)))
        (forall candidate:set->A,
          nrEq A start (candidate (niZero chooseNumber chooseFunction)) ->
          (forall number:set,
            naturalClosure (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction) number ->
            nrEq A (step number (candidate number)) (candidate (niSuccessor chooseFunction number))) ->
          forall number:set,
            naturalClosure (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction) number ->
            nrEq A (recurse number) (candidate number)))).
assume classical:niClassical.
let chooseNumber chooseFunction.
assume selectsNumber:forall P:set->prop, nrExists set P -> P (chooseNumber P).
assume selectsFunction:forall P:(set->set)->prop,
  nrExists (set->set) P -> P (chooseFunction P).
assume infinite:niInfinity.
let start step choose.
assume selects:forall P:A->prop, nrExists A P -> P (choose P).
exact nrRecursion A (niZero chooseNumber chooseFunction) (niSuccessor chooseFunction)
  (niZeroNotSuccessor classical chooseNumber chooseFunction selectsNumber selectsFunction infinite)
  (niSuccessorInjective chooseFunction selectsFunction infinite) start step choose selects.
Qed.

End InfiniteNaturalRecursion.
