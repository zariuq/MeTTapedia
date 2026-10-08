import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperations
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationNormalization
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# All-arity function and independent equation-admission controls

An independent constructor algebra retains every finite output vector and
the whole receiver function. Actual generated primitive images and their
reconstructed meanings are compared before concrete three-position reads.
Changing the third position changes the answer; the original unary/binary
operator family cannot cover that receiver declaration.

Ordered process trees reject the actual structural commutativity schema.
They therefore test constructor reconstruction without masquerading as a
model of the generated pi equation guest.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel
open Mettapedia.CategoryTheory.RelativeClosedSyntax

inductive Tree where
  | empty
  | parallel (first second : Tree)
  | emitted (channel : Nat) (arguments : List Nat)
  | received (arity channel : Nat) (body : (Fin arity → Nat) → Tree)
  | fresh (body : Nat → Tree)
  | replication (body : Tree)

def sort : Srt → Type
  | .nm => Nat
  | .pr => Tree

def tupleType (arity : Nat) : Type := contextOf (S := AllArity.sig) sort (AllArity.names arity)
def functionVector (arity : Nat) : Type :=
  familyOf (S := AllArity.sig) (fun context result => contextOf sort context ⟶[Type] sort result)
    (AllArity.nameArguments arity)

def tuplePack : (arity : Nat) → (Fin arity → Nat) → tupleType arity
  | 0, _ => PUnit.unit
  | arity + 1, values => (values 0, tuplePack arity (fun index => values index.succ))

def tupleValues : (arity : Nat) → tupleType arity → Fin arity → Nat
  | 0, _, index => Fin.elim0 index
  | arity + 1, values, index => Fin.cases values.1 (fun earlier => tupleValues arity values.2 earlier) index

def functionValues : (arity : Nat) → functionVector arity → Fin arity → Nat
  | 0, _, index => Fin.elim0 index
  | arity + 1, values, index =>
      Fin.cases ((show PUnit ⟶ Nat from values.1) PUnit.unit)
        (fun earlier => functionValues arity values.2 earlier) index

theorem tuple_roundtrip (arity : Nat) (values : Fin arity → Nat) :
    tupleValues arity (tuplePack arity values) = values := by
  induction arity with
  | zero => funext index; exact Fin.elim0 index
  | succ arity inductionHypothesis =>
      funext index
      refine Fin.cases rfl (fun earlier => ?_) index
      exact congrFun (inductionHypothesis (fun position => values position.succ)) earlier

def operations : ClosedPresentation.Operations AllArity.sig (Type) where
  sort := sort
  operation
    | .nil => ↾fun _ => .empty
    | .par => ↾fun values => .parallel
        ((show PUnit ⟶ Tree from values.1) PUnit.unit)
        ((show PUnit ⟶ Tree from values.2.1) PUnit.unit)
    | .out arity => ↾fun values => .emitted
        ((show PUnit ⟶ Nat from values.1) PUnit.unit) (List.ofFn (functionValues arity values.2))
    | .inp arity => ↾fun values => .received arity
        ((show PUnit ⟶ Nat from values.1) PUnit.unit)
        (fun supplied => (show tupleType arity ⟶ Tree from values.2.1) (tuplePack arity supplied))
    | .nu => ↾fun values => .fresh (fun name => (show tupleType 1 ⟶ Tree from values.1) (name, PUnit.unit))
    | .rep => ↾fun values => .replication ((show PUnit ⟶ Tree from values.1) PUnit.unit)

def recovered : ClosedPresentation.Operations AllArity.sig (Type) := by
  letI : PreservesFiniteLimits operations.interpretation.functor := operations.interpretation.preservesFiniteLimits
  letI : MonoidalClosedFunctor operations.interpretation.functor := operations.interpretation.preservesExponentials
  exact ClosedPresentation.GeneratedModel.operations (binding := AllArity.sig) operations.interpretation.functor

theorem complete_recovered_assignment : recovered.assignment = operations.assignment := by
  let _ : PreservesFiniteLimits operations.interpretation.functor := operations.interpretation.preservesFiniteLimits
  let _ : MonoidalClosedFunctor operations.interpretation.functor := operations.interpretation.preservesExponentials
  exact (ClosedPresentation.GeneratedModel.assignment_equal (binding := AllArity.sig) operations.interpretation.functor).trans
    (InterpretationNormalization.normalized_assignment operations.assignment operations.realization
      (ClosedPresentation.headers AllArity.sig))

theorem complete_recovered_primitive (origin : Sigma AllArity.Op) :
    recovered.primitiveValue origin = operations.primitiveValue origin :=
  congrArg (fun assignment => assignment.arrow (ULift.up origin)) complete_recovered_assignment

def recoveredRead {result : Srt} (operator : AllArity.Op result)
    (supplied : operations.family (AllArity.sig.arity operator)) : Option (operations.sort result) :=
  (Interpretation.ArrowValue.readAt (some (recovered.primitiveValue ⟨result,operator⟩))
    (operations.family (AllArity.sig.arity operator)) (operations.sort result)).map (fun arrow => arrow supplied)

theorem recoveredRead_actual {result : Srt} (operator : AllArity.Op result)
    (supplied : operations.family (AllArity.sig.arity operator)) :
    recoveredRead operator supplied = some (operations.operation operator supplied) := by
  rw [recoveredRead,complete_recovered_primitive]
  rw [ClosedPresentation.Operations.primitiveValue,Interpretation.ArrowValue.readAt_supplied]
  rfl

def channel (value : Nat) : PUnit ⟶ Nat := ↾fun _ => value
def body (offset : Nat) : tupleType 3 ⟶ Tree := ↾fun values =>
  .emitted ((show Nat from values.1) + offset) [values.2.1,values.2.2.1]

def changedBody (offset : Nat) : tupleType 3 ⟶ Tree := ↾fun values =>
  .emitted ((show Nat from values.1) + offset) [values.2.1,(show Nat from values.2.2.1) + 1]

theorem complete_three_receiver (name offset : Nat) :
    recoveredRead (AllArity.Op.inp 3) (channel name,(body offset,PUnit.unit)) =
      some (.received 3 name (fun values => .emitted (values 0 + offset) [values 1,values 2])) := by
  rw [recoveredRead_actual]
  rfl

def receiverObservation : Tree → Option (Nat × Nat × List Nat)
  | .received _ name supplied => match supplied (fun position => position.val + 7) with
      | .emitted result arguments => some (name,result,arguments)
      | _ => none
  | _ => none

theorem all_three_positions (name offset : Nat) :
    (recoveredRead (AllArity.Op.inp 3) (channel name,(body offset,PUnit.unit))).bind receiverObservation =
      some (name,7 + offset,[8,9]) := by
  rw [complete_three_receiver]
  rfl

theorem changed_third_position :
    recoveredRead (AllArity.Op.inp 3) (channel 5,(body 11,PUnit.unit)) ≠
      recoveredRead (AllArity.Op.inp 3) (channel 5,(changedBody 11,PUnit.unit)) := by
  intro same
  have read := congrArg (fun value => value.bind receiverObservation) same
  rw [all_three_positions,recoveredRead_actual] at read
  exact (by decide : (some ((5 : Nat),(18 : Nat),[8,9])) ≠ some (5,18,[8,10])) read

theorem three_receiver_outside_fragment (operator : PolyadicPi.Op Srt.pr) :
    AllArity.fragment.opMap operator ≠ AllArity.Op.inp 3 := by
  cases operator <;> intro impossible <;> cases impossible

def equationEnvironment : operations.model.Env PUnit [Srt.pr,Srt.pr] := fun _ position => match position with
  | .zero => ↾fun _ => Tree.empty
  | .succ .zero => ↾fun _ => Tree.emitted 31 []

def equationParameters : PUnit ⟶ operations.family AllArity.structuralMetas := ↾fun _ =>
  ((↾fun _ => Tree.empty),(↾fun _ => Tree.empty),PUnit.unit)

theorem structural_commutativity_rejected :
    ¬ operations.model.SchemaFamilySatisfaction AllArity.equations := by
  intro admitted
  have same := admitted ⟨0,by decide⟩
  have read := congrArg (fun value => value.value PUnit equationParameters equationEnvironment PUnit.unit) same
  change Tree.parallel Tree.empty (Tree.emitted 31 []) = Tree.parallel (Tree.emitted 31 []) Tree.empty at read
  have first := (Tree.parallel.inj read).1
  cases first

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedControls
