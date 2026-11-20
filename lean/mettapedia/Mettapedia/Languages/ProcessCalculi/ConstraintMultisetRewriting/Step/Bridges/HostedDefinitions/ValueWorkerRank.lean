import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ValueWorkerCases

/-!
# A syntactic potential for the actual value-worker steps

The cursor is ghost evidence describing the existing literal calls. Its
potential counts unvisited data and pending continuation work. No source
reduction relation or evaluator is introduced by this representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank

open Mettapedia.OSLF.Binding
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open ValueContinuation

mutual

def weight {context : Ctx MSig} {sort : Unit} : Term MSig context sort → Nat
  | .var _ => 1
  | .op _ arguments => 1 + argumentsWeight arguments

def argumentsWeight {context : Ctx MSig} {arity : List (List Unit × Unit)} : Args MSig arity context → Nat
  | .nil => 0
  | .cons first later => weight first + argumentsWeight later

end

theorem tuple_arguments_weight (children : List MClosed) :
    argumentsWeight (ctupleArgs children) = (children.map weight).sum := by
  induction children with
  | nil => rfl
  | cons first rest ih =>
      simp only [ctupleArgs, argumentsWeight, List.map_cons, List.sum_cons, ih]

theorem node_weight (tag : String) (children : List MClosed) :
    weight (nodeC tag children) = 2 + (children.map weight).sum := by
  change 1 + argumentsWeight (ctupleArgs (csym tag :: children)) = _
  rw [tuple_arguments_weight (csym tag :: children)]
  change 1 + (1 + (children.map weight).sum) = _
  omega

theorem successor_weight (datum : MClosed) :
    weight (successor datum) = 2 +
      weight (encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0)) + weight datum := by
  simp only [successor, node_weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

theorem pair_weight (first second : MClosed) :
    weight (pair first second) = 2 + weight first + weight second := by
  simp only [pair, node_weight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  omega

def stackWeight : Stack → Nat
  | .base => 0
  | .succ rest => 1 + stackWeight rest
  | .first second rest => 3 * weight second + 3 + stackWeight rest
  | .second _ rest => 1 + stackWeight rest

inductive Cursor where
  | checking (datum : MClosed) (stack : Stack)
  | returning (datum : MClosed) (stack : Stack)

def Cursor.view : Cursor → MClosed
  | .checking datum stack => valueC datum (code stack)
  | .returning datum stack => resumeC datum (code stack)

def Cursor.potential : Cursor → Nat
  | .checking datum stack => 3 * weight datum + stackWeight stack + 1
  | .returning _ stack => stackWeight stack

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueWorkerRank
