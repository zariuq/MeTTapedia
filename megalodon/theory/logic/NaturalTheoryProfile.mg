(** Optional classical natural-number theory over NaturalCarrier.mg.
    The assumptions are individually named: a polymorphic selector and its
    law, double-negation elimination, and Dedekind infinity. They are not
    defaults of the Egal kernel or consequences of a profile tag. **)

Section NaturalTheorySelection.
Variable A:SType.

(** The stable source identity is SHA-256 of
    `Mettapedia:Megalodon:NaturalTheoryProfile:niChoose:forall A.(A->prop)->A:v1`.
    It authorizes this parameter association; it is not a definition hash. **)
(* Parameter niChoose "416ea32884c01532bc760e9c24df68a0d213108d4ceb03f323fa882259356389" *)
Parameter niChoose : (A->prop)->A.
Axiom niChoiceOption : forall P:A->prop,
  nrExists A P -> P (niChoose P).

End NaturalTheorySelection.

Axiom niClassicalOption : niClassical.
Axiom niInfinityOption : niInfinity.

Definition niSelectedSuccessor : set->set := niSuccessor (niChoose (set->set)).
Definition niSelectedZero : set := niZero (niChoose set) (niChoose (set->set)).

Theorem niSelectedZeroNotSuccessor : forall number:set,
  nrEq set (niSelectedSuccessor number) niSelectedZero -> nrFalse.
exact niZeroNotSuccessor niClassicalOption (niChoose set) (niChoose (set->set))
  (niChoiceOption set) (niChoiceOption (set->set)) niInfinityOption.
Qed.

Theorem niSelectedSuccessorInjective : niInjective niSelectedSuccessor.
exact niSuccessorInjective (niChoose (set->set))
  (niChoiceOption (set->set)) niInfinityOption.
Qed.

Theorem niSelectedSuccessorNotOnto : niOnto niSelectedSuccessor -> nrFalse.
exact niSuccessorNotOnto (niChoose (set->set))
  (niChoiceOption (set->set)) niInfinityOption.
Qed.

Theorem niSelectedInfinity : niInfiniteFunction niSelectedSuccessor.
exact ncAndIntro (niInjective niSelectedSuccessor)
  (niOnto niSelectedSuccessor -> nrFalse)
  niSelectedSuccessorInjective niSelectedSuccessorNotOnto.
Qed.

Theorem niSelectedNaturalZero :
  naturalClosure niSelectedZero niSelectedSuccessor niSelectedZero.
exact niNaturalZero (niChoose set) (niChoose (set->set)).
Qed.

Theorem niSelectedNaturalSuccessor : forall number:set,
  naturalClosure niSelectedZero niSelectedSuccessor number ->
  naturalClosure niSelectedZero niSelectedSuccessor (niSelectedSuccessor number).
exact niNaturalSuccessor (niChoose set) (niChoose (set->set)).
Qed.

Theorem niSelectedNaturalInduction : forall P:set->prop,
  P niSelectedZero ->
  (forall number:set, naturalClosure niSelectedZero niSelectedSuccessor number ->
    P number -> P (niSelectedSuccessor number)) ->
  forall number:set, naturalClosure niSelectedZero niSelectedSuccessor number -> P number.
exact naturalClosureInduction niSelectedZero niSelectedSuccessor.
Qed.

Section NaturalTheoryRecursion.
Variable A:SType.

Theorem niSelectedRecursion : forall start:A, forall step:set->A->A,
  nrExists (set->A) (fun recurse:set->A =>
    ncAnd (nrEq A start (recurse niSelectedZero))
      (ncAnd
        (forall number:set, naturalClosure niSelectedZero niSelectedSuccessor number ->
          nrEq A (step number (recurse number)) (recurse (niSelectedSuccessor number)))
        (forall candidate:set->A,
          nrEq A start (candidate niSelectedZero) ->
          (forall number:set, naturalClosure niSelectedZero niSelectedSuccessor number ->
            nrEq A (step number (candidate number)) (candidate (niSelectedSuccessor number))) ->
          forall number:set, naturalClosure niSelectedZero niSelectedSuccessor number ->
            nrEq A (recurse number) (candidate number)))).
let start step.
exact niRecursion A niClassicalOption (niChoose set) (niChoose (set->set))
  (niChoiceOption set) (niChoiceOption (set->set)) niInfinityOption
  start step (niChoose A) (niChoiceOption A).
Qed.

End NaturalTheoryRecursion.
