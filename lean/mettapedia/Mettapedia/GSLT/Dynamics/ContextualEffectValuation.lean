import Mettapedia.GSLT.Dynamics.ContextualEffectInitiality
import Mettapedia.GSLT.Dynamics.IndexedEventValuation
import Mathlib.Algebra.Ring.Nat

/-!
# Independent valuations of contextual computations

The free contextual computation algebra admits independent interpretations.
This module makes that independence explicit in two ways:

* the product of two effect algebras interprets a program once while retaining
  both results, and either coordinate is recovered exactly;
* a shared-state traversal emits an explicit chronological event history,
  which an independently supplied event valuation may grade.

The semantic answer and its event valuation are deliberately not identified.
Two computations can have the same shared-state result while retaining
different histories and costs.  Thus cost is compositional extra structure,
not a function secretly determined by denotation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ContextualEffectValuation

open ContextualEffectHandlers
open ContextualEffectInitiality
open IndexedEventValuation

universe u

namespace EffectAlgebra

variable {State Answer Intent : Type u}

/-- Coordinatewise product of two interpretations of the same contextual
effect signature. -/
def prod (left right : EffectAlgebra State Answer Intent) :
    EffectAlgebra State Answer Intent where
  Carrier := left.Carrier × right.Carrier
  pure answer := (left.pure answer, right.pure answer)
  choose first second :=
    (left.choose first.1 second.1, right.choose first.2 second.2)
  read next :=
    (left.read (fun state => (next state).1),
      right.read (fun state => (next state).2))
  write state next :=
    (left.write state next.1, right.write state next.2)
  intent request next :=
    (left.intent request next.1, right.intent request next.2)

/-- Forget the right interpretation of a paired effect algebra. -/
def fstHom (left right : EffectAlgebra State Answer Intent) :
    prod left right ⟶ left where
  toFun := Prod.fst
  map_pure := by intros; rfl
  map_choose := by intros; rfl
  map_read := by intros; rfl
  map_write := by intros; rfl
  map_intent := by intros; rfl

/-- Forget the left interpretation of a paired effect algebra. -/
def sndHom (left right : EffectAlgebra State Answer Intent) :
    prod left right ⟶ right where
  toFun := Prod.snd
  map_pure := by intros; rfl
  map_choose := by intros; rfl
  map_read := by intros; rfl
  map_write := by intros; rfl
  map_intent := by intros; rfl

/-- Pairing interpretations does not alter either fold. -/
theorem fold_prod (left right : EffectAlgebra State Answer Intent)
    (program : Program State Answer Intent) :
    ContextualEffectInitiality.EffectAlgebra.fold (prod left right) program =
      (ContextualEffectInitiality.EffectAlgebra.fold left program,
        ContextualEffectInitiality.EffectAlgebra.fold right program) := by
  induction program with
  | pure answer => rfl
  | choose first second firstIH secondIH =>
      simp only [ContextualEffectInitiality.EffectAlgebra.fold_choose, prod]
      apply Prod.ext
      · exact congrArg₂ left.choose
          (congrArg Prod.fst firstIH) (congrArg Prod.fst secondIH)
      · exact congrArg₂ right.choose
          (congrArg Prod.snd firstIH) (congrArg Prod.snd secondIH)
  | read next nextIH =>
      simp only [ContextualEffectInitiality.EffectAlgebra.fold_read, prod]
      apply Prod.ext
      · exact congrArg left.read
          (funext fun state => congrArg Prod.fst (nextIH state))
      · exact congrArg right.read
          (funext fun state => congrArg Prod.snd (nextIH state))
  | write state next nextIH =>
      simp only [ContextualEffectInitiality.EffectAlgebra.fold_write, prod]
      apply Prod.ext
      · exact congrArg (left.write state) (congrArg Prod.fst nextIH)
      · exact congrArg (right.write state) (congrArg Prod.snd nextIH)
  | intent request next nextIH =>
      simp only [ContextualEffectInitiality.EffectAlgebra.fold_intent, prod]
      apply Prod.ext
      · exact congrArg (left.intent request) (congrArg Prod.fst nextIH)
      · exact congrArg (right.intent request) (congrArg Prod.snd nextIH)

@[simp] theorem fold_prod_fst (left right : EffectAlgebra State Answer Intent)
    (program : Program State Answer Intent) :
    (ContextualEffectInitiality.EffectAlgebra.fold
      (prod left right) program).1 =
      ContextualEffectInitiality.EffectAlgebra.fold left program := by
  rw [fold_prod]

@[simp] theorem fold_prod_snd (left right : EffectAlgebra State Answer Intent)
    (program : Program State Answer Intent) :
    (ContextualEffectInitiality.EffectAlgebra.fold
      (prod left right) program).2 =
      ContextualEffectInitiality.EffectAlgebra.fold right program := by
  rw [fold_prod]

end EffectAlgebra

/-! ## Event history as a separate interpretation -/

/-- Events exposed by the left-to-right shared-state traversal.  Payloads are
retained where they carry provenance relevant to later valuations. -/
inductive EffectEvent (State Intent : Type u) : Type u where
  | choose
  | read
  | write (state : State)
  | intent (request : Intent)
deriving DecidableEq

/-- A shared-state traversal retaining its final state and chronological
effect history, but no semantic answers. -/
def sharedHistoryAlgebra (State Answer Intent : Type u) :
    EffectAlgebra State Answer Intent where
  Carrier := State → State × List (EffectEvent State Intent)
  pure := fun _answer state => (state, [])
  choose := fun left right state =>
    let leftResult := left state
    let rightResult := right leftResult.1
    (rightResult.1,
      EffectEvent.choose :: (leftResult.2 ++ rightResult.2))
  read := fun next state =>
    let result := next state state
    (result.1, EffectEvent.read :: result.2)
  write := fun newState next _parentState =>
    let result := next newState
    (result.1, EffectEvent.write newState :: result.2)
  intent := fun request next state =>
    let result := next state
    (result.1, EffectEvent.intent request :: result.2)

/-- Final state and chronological history selected by the shared-state
traversal. -/
def sharedHistoryResult {State Answer Intent : Type u}
    (program : Program State Answer Intent) (initialState : State) :
    State × List (EffectEvent State Intent) :=
  ContextualEffectInitiality.EffectAlgebra.fold
    (sharedHistoryAlgebra State Answer Intent) program initialState

/-- Chronological history selected by the shared-state traversal. -/
def sharedHistory {State Answer Intent : Type u}
    (program : Program State Answer Intent) (initialState : State) :
    List (EffectEvent State Intent) :=
  (sharedHistoryResult program initialState).2

/-- Mapping answer values changes neither the state trajectory nor the effect
occurrences. -/
theorem sharedHistoryResult_map
    {State Answer OtherAnswer Intent : Type u}
    (mapAnswer : Answer → OtherAnswer)
    (program : Program State Answer Intent) (initialState : State) :
    sharedHistoryResult (Program.map mapAnswer program) initialState =
      sharedHistoryResult program initialState := by
  induction program generalizing initialState with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      change
        (let leftResult :=
            sharedHistoryResult (Program.map mapAnswer left) initialState;
          let rightResult :=
            sharedHistoryResult (Program.map mapAnswer right) leftResult.1;
          (rightResult.1,
            EffectEvent.choose :: (leftResult.2 ++ rightResult.2))) =
        (let leftResult := sharedHistoryResult left initialState;
          let rightResult := sharedHistoryResult right leftResult.1;
          (rightResult.1,
            EffectEvent.choose :: (leftResult.2 ++ rightResult.2)))
      simp only [leftIH, rightIH]
  | read next nextIH =>
      change
        (let result := sharedHistoryResult
            (Program.map mapAnswer (next initialState)) initialState;
          (result.1, EffectEvent.read :: result.2)) =
        (let result := sharedHistoryResult (next initialState) initialState;
          (result.1, EffectEvent.read :: result.2))
      rw [nextIH]
  | write state next nextIH =>
      change
        (let result := sharedHistoryResult
            (Program.map mapAnswer next) state;
          (result.1, EffectEvent.write state :: result.2)) =
        (let result := sharedHistoryResult next state;
          (result.1, EffectEvent.write state :: result.2))
      rw [nextIH]
  | intent request next nextIH =>
      change
        (let result := sharedHistoryResult
            (Program.map mapAnswer next) initialState;
          (result.1, EffectEvent.intent request :: result.2)) =
        (let result := sharedHistoryResult next initialState;
          (result.1, EffectEvent.intent request :: result.2))
      rw [nextIH]

/-- Mapping answer values changes neither effect occurrences nor their
chronology.  Event history is an operational observation, independent of the
chosen answer representation. -/
theorem sharedHistory_map {State Answer OtherAnswer Intent : Type u}
    (mapAnswer : Answer → OtherAnswer)
    (program : Program State Answer Intent) (initialState : State) :
    sharedHistory (Program.map mapAnswer program) initialState =
      sharedHistory program initialState := by
  exact congrArg Prod.snd
    (sharedHistoryResult_map mapAnswer program initialState)

/-- Pair the semantic shared-state handler with its independent event-history
handler. -/
def sharedSemanticsAndHistoryAlgebra (State Answer Intent : Type u) :
    EffectAlgebra State Answer Intent :=
  EffectAlgebra.prod
    (ContextualEffectInitiality.EffectAlgebra.sharedAlgebra
      (State := State) (Answer := Answer)
      (Intent := Intent))
    (sharedHistoryAlgebra State Answer Intent)

/-- Adding event history leaves the shared-state denotation exactly
unchanged. -/
theorem shared_semantics_projection {State Answer Intent : Type u}
    (program : Program State Answer Intent) (initialState : State) :
    (ContextualEffectInitiality.EffectAlgebra.fold
        (sharedSemanticsAndHistoryAlgebra State Answer Intent) program).1
        initialState =
      runShared program initialState := by
  unfold sharedSemanticsAndHistoryAlgebra
  rw [EffectAlgebra.fold_prod_fst,
    ContextualEffectInitiality.EffectAlgebra.fold_shared_eq_runShared]

/-- The second coordinate of the paired fold is exactly the declared event
history. -/
theorem shared_history_projection {State Answer Intent : Type u}
    (program : Program State Answer Intent) (initialState : State) :
    ((ContextualEffectInitiality.EffectAlgebra.fold
        (sharedSemanticsAndHistoryAlgebra State Answer Intent) program).2
        initialState).2 =
      sharedHistory program initialState := by
  unfold sharedSemanticsAndHistoryAlgebra sharedHistory sharedHistoryResult
  rw [EffectAlgebra.fold_prod_snd]

/-- Grade a contextual computation only after choosing an event valuation.
The operational syntax does not choose this valuation. -/
def sharedGrade {State Answer Intent : Type u}
    (valuation : Valuation (EffectEvent State Intent))
    (program : Program State Answer Intent) (initialState : State) :
    Option valuation.Grade :=
  valuation.historyGrade (sharedHistory program initialState)

/-- Every independently selected event valuation is invariant under a change
of answer representation. -/
theorem sharedGrade_map {State Answer OtherAnswer Intent : Type u}
    (valuation : Valuation (EffectEvent State Intent))
    (mapAnswer : Answer → OtherAnswer)
    (program : Program State Answer Intent) (initialState : State) :
    sharedGrade valuation (Program.map mapAnswer program) initialState =
      sharedGrade valuation program initialState := by
  unfold sharedGrade
  rw [sharedHistory_map]

/-! ## Separating controls -/

namespace Canary

def plain : Program Unit Bool Unit := .pure false

def redundantWrite : Program Unit Bool Unit :=
  .write () (.pure false)

/-- The extra write is denotationally invisible in the one-state model. -/
theorem same_shared_semantics :
    runShared plain () = runShared redundantWrite () :=
  rfl

/-- The explicit history retains the otherwise invisible operation. -/
theorem distinct_histories :
    sharedHistory plain () = [] ∧
      sharedHistory redundantWrite () = [EffectEvent.write ()] := by
  exact ⟨rfl, rfl⟩

/-- No observer of shared semantic results can reconstruct every operational
history. -/
theorem no_history_from_shared_semantics :
    ¬ ∃ recover : SharedResult Unit Bool Unit →
        List (EffectEvent Unit Unit),
      ∀ program : Program Unit Bool Unit,
        recover (runShared program ()) = sharedHistory program () := by
  rintro ⟨recover, recovers⟩
  have same := congrArg recover same_shared_semantics
  rw [recovers plain, recovers redundantWrite] at same
  simp [sharedHistory, sharedHistoryResult, plain, redundantWrite,
    sharedHistoryAlgebra] at same

/-- A concrete, independently selected unit cost for every retained event. -/
abbrev unitCost : Valuation (EffectEvent Unit Unit) :=
  additive fun _ => (1 : Nat)

/-- Equal denotation does not force equal selected cost. -/
theorem same_semantics_different_cost :
    runShared plain () = runShared redundantWrite () ∧
      sharedGrade unitCost plain () = some 0 ∧
      sharedGrade unitCost redundantWrite () = some 1 := by
  exact ⟨rfl, rfl, rfl⟩

end Canary

/-! ## Axiom audit -/

#print axioms EffectAlgebra.fold_prod
#print axioms sharedHistoryResult_map
#print axioms sharedHistory_map
#print axioms shared_semantics_projection
#print axioms shared_history_projection
#print axioms sharedGrade_map
#print axioms Canary.no_history_from_shared_semantics
#print axioms Canary.same_semantics_different_cost

end Mettapedia.GSLT.Dynamics.ContextualEffectValuation
