import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangement

/-!
# Witnessed swaps with alike residuals

Context placement and dependent transport need not produce the literal
canonical residual. A swap here retains its residual comparisons and its
explicit similarity of continuations. It factors into two witnessed
similarities and one canonical interchange. This retains the prescribed
event permutation rather than choosing an arbitrary trace witness.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

open _root_.CategoryTheory

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P)

namespace SimilarityWitness

variable {T}

def consSelf {state : State} (candidate : Firing state) (accepted : P.Admits candidate)
    {first second : P.Run (P.result candidate accepted)} (tail : T.SimilarityWitness first second) :
    T.SimilarityWitness (.cons candidate accepted first) (.cons candidate accepted second) :=
  .cons (T.refl state) (T.move_refl candidate) tail

def consAlike {state : State} {first second : Firing state} (alike : T.Alike first second)
    (accepted : P.Admits first) (accepted' : P.Admits second)
    {rest : P.Run (P.result first accepted)} {rest' : P.Run (P.result second accepted')}
    (tail : T.SimilarityWitness rest rest') :
    T.SimilarityWitness (.cons first accepted rest) (.cons second accepted' rest') :=
  .cons (T.refl state) ((T.move_refl first).trans alike) tail

end SimilarityWitness

inductive SwapWitness : {state : State} → P.Run state → P.Run state → Type (max uS uF uI)
  | here {state : State} {first second : Firing state}
      (accepted : P.Admits first) (accepted' : P.Admits second)
      {afterFirst : Firing (P.result first accepted)}
      (residualFirst : T.Alike (T.residual first accepted second) afterFirst)
      (acceptedAfterFirst : P.Admits afterFirst)
      {afterSecond : Firing (P.result second accepted')}
      (residualSecond : T.Alike (T.residual second accepted' first) afterSecond)
      (acceptedAfterSecond : P.Admits afterSecond)
      {rest : P.Run (P.result afterFirst acceptedAfterFirst)}
      {rest' : P.Run (P.result afterSecond acceptedAfterSecond)}
      (tail : T.SimilarityWitness rest rest') :
      SwapWitness (.cons first accepted (.cons afterFirst acceptedAfterFirst rest))
        (.cons second accepted' (.cons afterSecond acceptedAfterSecond rest'))
  | later {state : State} (candidate : Firing state) (accepted : P.Admits candidate)
      {first second : P.Run (P.result candidate accepted)} (tail : SwapWitness first second) :
      SwapWitness (.cons candidate accepted first) (.cons candidate accepted second)

namespace SwapWitness

variable {T}

def depth : {state : State} → {first second : P.Run state} → T.SwapWitness first second → Nat
  | _, _, _, .here .. => 0
  | _, _, _, .later _ _ tail => tail.depth + 1

theorem swapStep {state : State} {first second : P.Run state}
    (witness : T.SwapWitness first second) : T.SwapStep first second := by
  induction witness with
  | here accepted accepted' residualFirst acceptedAfterFirst residualSecond acceptedAfterSecond tail =>
      exact .here accepted accepted' residualFirst acceptedAfterFirst residualSecond acceptedAfterSecond tail.similar
  | later candidate accepted _ ih => exact .later candidate accepted ih

structure Factorization {state : State} (first second : P.Run state) where
  left : P.Run state
  right : P.Run state
  before : T.SimilarityWitness first left
  swap : T.InterchangeWitness left right
  after : T.SimilarityWitness right second

noncomputable def factor {state : State} {first second : P.Run state}
    (witness : T.SwapWitness first second) : Factorization (T := T) first second := by
  induction witness with
  | @here state first second accepted accepted' afterFirst residualFirst acceptedAfterFirst
      afterSecond residualSecond acceptedAfterSecond rest rest' tail =>
      let canonicalG := (T.admits_alike residualFirst).mpr acceptedAfterFirst
      let canonicalF := (T.admits_alike residualSecond).mpr acceptedAfterSecond
      let toG := T.result_alike residualFirst canonicalG acceptedAfterFirst
      let toF := T.result_alike residualSecond canonicalF acceptedAfterSecond
      let close := T.trans toG (T.trans tail.startIso (T.symm toF))
      let unchanged := T.moveRun (T.symm toG) rest
      let before := (SimilarityWitness.moveRun (T.symm toG) rest).consAlike
        residualFirst.symm acceptedAfterFirst canonicalG |>.consSelf first accepted
      let following := (SimilarityWitness.moveRun close unchanged).symm.trans
        ((SimilarityWitness.moveRun (T.symm toG) rest).symm.trans tail)
      let after := following.consAlike residualSecond canonicalF acceptedAfterSecond |>.consSelf second accepted'
      exact ⟨_, _, before,
        .here accepted accepted' canonicalG canonicalF close unchanged, after⟩
  | later candidate accepted tail inner =>
      exact ⟨.cons candidate accepted inner.left, .cons candidate accepted inner.right,
        inner.before.consSelf candidate accepted, .later candidate accepted inner.swap,
        inner.after.consSelf candidate accepted⟩

noncomputable def cell {state : State} {first second : P.Run state} (witness : T.SwapWitness first second) :
    RunRearrangement.Cell T first second :=
  RunRearrangement.generator T (.inl witness.factor.before) ≫
    RunRearrangement.generator T (.inr witness.factor.swap) ≫
      RunRearrangement.generator T (.inl witness.factor.after)

theorem factor_depth {state : State} {first second : P.Run state} (witness : T.SwapWitness first second) :
    witness.factor.swap.depth = witness.depth := by
  induction witness with
  | here => rfl
  | later candidate accepted tail ih => exact congrArg Nat.succ ih

theorem cell_events {state : State} {first second : P.Run state} (witness : T.SwapWitness first second)
    (event : Fin first.word.length) :
    (RunRearrangement.events T witness.cell event).val = ProofRelevantRuns.swapAt witness.depth event.val := by
  simp only [cell, RunRearrangement.events_comp, RunRearrangement.events_generator,
    RunRearrangement.Generator.events, Equiv.trans_apply, SimilarityWitness.events_val]
  change ProofRelevantRuns.swapAt witness.factor.swap.depth event.val = _
  rw [factor_depth]

end SwapWitness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.SwapWitness.cell_events
