import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunRearrangementPrefix
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunTransport

/-!
# Continuing actual elementary run comparisons

The continuation is transported along the boundary map retained by the
witness. A canonical interchange extends by the actual moved continuation;
its swap depth is unchanged. Similarity extends by a witnessed transport of
the continuation. No arbitrary trace witness is selected in these operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

universe uO uT uH uOcc uS uF uI

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} {T : Transport.{uO,uT,uH,uOcc,uS,uF,uI} P}

theorem SimilarityWitness.moveRun_lastIso : ∀ {source target : State}
    (comparison : T.Iso source target) (run : P.Run source),
    (SimilarityWitness.moveRun comparison run).lastIso = T.moveRunEndIso comparison run
  | _, _, _, .nil _ => rfl
  | _, _, comparison, .cons firing accepted rest =>
      moveRun_lastIso (T.result_move comparison firing accepted) rest

theorem moveRun_append : ∀ {source target : State} (comparison : T.Iso source target)
    (early : P.Run source) (continuation : P.Run early.last),
    T.moveRun comparison (early.append continuation) =
      (T.moveRun comparison early).append
        (T.moveRun (SimilarityWitness.moveRun comparison early).lastIso continuation)
  | _, _, _, .nil _, _ => rfl
  | _, _, comparison, .cons firing accepted rest, continuation =>
      congrArg (Step.Run.cons (T.move comparison firing) ((T.admits_move comparison firing).mpr accepted))
        (moveRun_append (T.result_move comparison firing accepted) rest continuation)

def SimilarityWitness.extend {source target : State} {first : P.Run source} {second : P.Run target}
    (witness : T.SimilarityWitness first second) (continuation : P.Run first.last) :
    T.SimilarityWitness (first.append continuation) (second.append (T.moveRun witness.lastIso continuation)) :=
  witness.append (SimilarityWitness.moveRun witness.lastIso continuation)

def InterchangeWitness.changeTarget {start : State} {first second third : P.Run start}
    (same : second = third) (witness : T.InterchangeWitness first second) :
    T.InterchangeWitness first third := same ▸ witness

theorem InterchangeWitness.depth_changeTarget {start : State} {first second third : P.Run start}
    (same : second = third) (witness : T.InterchangeWitness first second) :
    (witness.changeTarget same).depth = witness.depth := by
  cases same
  rfl

def InterchangeWitness.extend : {start : State} → {first second : P.Run start} →
    (witness : T.InterchangeWitness first second) → (continuation : P.Run first.last) →
      T.InterchangeWitness (first.append continuation) (second.append (T.moveRun witness.lastIso continuation))
  | _, .cons first _ _, .cons second _ _, .here accepted accepted' afterFirst afterSecond close rest, continuation =>
      InterchangeWitness.changeTarget
        (congrArg (fun tail => Step.Run.cons second accepted'
          (.cons (T.residual second accepted' first) afterSecond tail)) (moveRun_append close rest continuation))
        (.here accepted accepted' afterFirst afterSecond close (rest.append continuation))
  | _, _, _, .later firing accepted tail, continuation => .later firing accepted (tail.extend continuation)

theorem InterchangeWitness.depth_extend : ∀ {start : State} {first second : P.Run start}
    (witness : T.InterchangeWitness first second) (continuation : P.Run first.last),
    (witness.extend continuation).depth = witness.depth
  | _, _, _, .here .., _ => InterchangeWitness.depth_changeTarget _ _
  | _, _, _, .later _ _ tail, continuation => congrArg (· + 1) (tail.depth_extend continuation)

theorem InterchangeWitness.position_extend {start : State} {first second : P.Run start}
    (witness : T.InterchangeWitness first second) (continuation : P.Run first.last) (index : Nat) :
    (witness.extend continuation).position index = witness.position index :=
  congrArg (fun depth => ProofRelevantRuns.swapAt depth index) (witness.depth_extend continuation)

theorem InterchangeWitness.continuation_position_fixed {start : State} {first second : P.Run start}
    (witness : T.InterchangeWitness first second) (continuation : P.Run first.last) {index : Nat}
    (inContinuation : first.word.length ≤ index) :
    (witness.extend continuation).position index = index :=
  (witness.position_extend continuation index).trans (witness.fixes_outside inContinuation)

namespace RunRearrangement

def Generator.boundary {start : State} {first second : Object T start}
    (witness : Generator T first second) : T.Iso first.last second.last :=
  match witness with
  | .inl similar => similar.lastIso
  | .inr interchange => interchange.lastIso

def Generator.extend {start : State} {first second : Object T start}
    (witness : Generator T first second) (continuation : P.Run first.last) :
    Generator T (first.append continuation) (second.append (T.moveRun witness.boundary continuation)) :=
  match witness with
  | .inl similar => .inl (similar.extend continuation)
  | .inr interchange => .inr (interchange.extend continuation)

def Generator.position {start : State} {first second : Object T start}
    (witness : Generator T first second) (index : Nat) : Nat :=
  match witness with
  | .inl _ => index
  | .inr interchange => interchange.position index

theorem Generator.position_involutive {start : State} {first second : Object T start}
    (witness : Generator T first second) (index : Nat) :
    witness.position (witness.position index) = index := by
  cases witness with
  | inl => rfl
  | inr interchange => exact interchange.position_position index

theorem Generator.events_val {start : State} {first second : Object T start}
    (witness : Generator T first second) (event : Fin first.word.length) :
    (Generator.events T witness event).val = witness.position event.val := by
  cases witness <;> rfl

theorem Generator.events_inv_val {start : State} {first second : Object T start}
    (witness : Generator T first second) (event : Fin second.word.length) :
    ((Generator.events T witness).symm event).val = witness.position event.val := by
  have forward := congrArg Fin.val ((Generator.events T witness).apply_symm_apply event)
  have position := (witness.events_val ((Generator.events T witness).symm event)).symm.trans forward
  exact (witness.position_involutive ((Generator.events T witness).symm event).val).symm.trans
    (congrArg witness.position position)

theorem Generator.position_extend {start : State} {first second : Object T start}
    (witness : Generator T first second) (continuation : P.Run first.last) (index : Nat) :
    (witness.extend continuation).position index = witness.position index := by
  cases witness with
  | inl => rfl
  | inr interchange => exact interchange.position_extend continuation index

end RunRearrangement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.moveRun_append
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Transport.InterchangeWitness.depth_extend
