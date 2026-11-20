import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.DriverRewrites

/-!
# Continuation invariants of the actual value worker

This proof stack describes the private continuation data of the seven
value-worker equations. It reconstructs the initial datum and records which
left components have already passed the worker. Its base is the actual public
finish continuation, rather than an arbitrary datum resembling a private frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueContinuation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing.DirectedAnswers (Value)

def successor (term : MClosed) : MClosed :=
  nodeC "prime-tm-app" [encodeTm (.const TowerNumbersModel.succ : Tower.Tm 0), term]

def pair (first second : MClosed) : MClosed := nodeC "prime-tm-pair" [first, second]

inductive Stack where
  | base
  | succ (rest : Stack)
  | first (second : MClosed) (rest : Stack)
  | second (first : MClosed) (rest : Stack)

def code : Stack → MClosed
  | .base => finishContinuation
  | .succ rest => nodeC "hd-main-value-succ" [code rest]
  | .first second rest => nodeC "hd-main-value-pair-first" [second, code rest]
  | .second first rest => nodeC "hd-main-value-pair-second" [first, code rest]

def plug (term : MClosed) : Stack → MClosed
  | .base => term
  | .succ rest => plug (successor term) rest
  | .first second rest => plug (pair term second) rest
  | .second first rest => plug (pair first term) rest

def Valid : Stack → Prop
  | .base => True
  | .succ rest | .first _ rest => Valid rest
  | .second first rest => (∃ term : Tower.Tm 0, Value term ∧ first = encodeTm term) ∧ Valid rest

theorem base_iff (stack : Stack) : code stack = finishContinuation ↔ stack = .base := by
  cases stack <;> simp [code, finishContinuation, DataEmbedding.nodeC_eq_iff]

theorem succ_iff (stack : Stack) (rest : MClosed) :
    code stack = nodeC "hd-main-value-succ" [rest] ↔
      ∃ tail, stack = .succ tail ∧ rest = code tail := by
  cases stack <;> simp [code, finishContinuation, DataEmbedding.nodeC_eq_iff]
  exact eq_comm

theorem first_iff (stack : Stack) (second rest : MClosed) :
    code stack = nodeC "hd-main-value-pair-first" [second, rest] ↔
      ∃ tail, stack = .first second tail ∧ rest = code tail := by
  cases stack <;> simp [code, finishContinuation, DataEmbedding.nodeC_eq_iff]
  intro _
  exact eq_comm

theorem second_iff (stack : Stack) (first rest : MClosed) :
    code stack = nodeC "hd-main-value-pair-second" [first, rest] ↔
      ∃ tail, stack = .second first tail ∧ rest = code tail := by
  cases stack <;> simp [code, finishContinuation, DataEmbedding.nodeC_eq_iff]
  intro _
  exact eq_comm

@[simp] theorem successor_encoded (term : Tower.Tm 0) :
    successor (encodeTm term) = encodeTm (TowerVectorsModel.succC term) := by
  simp only [successor, TowerVectorsModel.succC, encodeTm_app]

@[simp] theorem pair_encoded (first second : Tower.Tm 0) :
    pair (encodeTm first) (encodeTm second) = encodeTm (.pair first second) :=
  (encodeTm_pair first second).symm

theorem value_injective {first second : Tower.Tm 0} (same : encodeTm first = encodeTm second) :
    first = second := encodeTm_injective same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueContinuation

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.ValueContinuation.base_iff
