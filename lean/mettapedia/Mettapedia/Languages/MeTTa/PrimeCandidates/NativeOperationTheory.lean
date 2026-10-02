import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler
import Mettapedia.GSLT.Dynamics.WeightedLinearInterpretation

/-!
# Native weighted computation in its finite-arity operation theory

An authored program supplies the actual Need machine, its physical equation
rows and their binding-local coefficients. A family of initial worlds gives
free variables; a declared finite observation reindexes the returned and
suspended worlds. The corresponding free operation is interpreted by the
generic handler exactly as the independently executed native frontier.

Finite observations are explicit. Reindexing leaves retains occurrence
multiplicity and coefficients, while the full frontier remains available
before observation. No observation turns an unfinished computation into a
certified completed answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOperationTheory

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.FiniteOperationTheory
open Mettapedia.GSLT.Dynamics
open NativeEquationNeed NativeCandidateGrades NativeWeightedHandler
open Mettapedia.GSLT.Core.WeightedMuScheduler

variable {V : Type} [Semiring V]

abbrev SourceTheory (State V : Type) [Semiring V] :=
  ResumptionOperationTheory.FreeTheory
    (WeightedBranchingResumption.Operation State V) WeightedBranchingResumption.Response

abbrev OperationTheory (V : Type) [Semiring V] := SourceTheory WorkState V

def sourceArity (State V : Type) [Semiring V] (n : Nat) : SourceTheory State V := n

def arityObject (V : Type) [Semiring V] (n : Nat) : OperationTheory V := n

/-- One free operation construction for settled, pending and nested native
sources. Finite observation remains downstream of the full residual account. -/
def sourceOperation {State Answer : Type}
    (source : WeightedBranchingResumption.Coalgebra State Answer V) (fuel : Nat)
    {n m : Nat} (initial : Fin m → State) (observe : Answer ⊕ State → Fin n) :
    sourceArity State V n ⟶ sourceArity State V m :=
  ofTerms fun inputIndex =>
    ResumptionAlgebra.bind
      (WeightedBranchingResumption.cut source fuel (initial inputIndex))
      (fun leaf => ResumptionAlgebra.pure (observe leaf))

theorem source_operation_handler {State Answer : Type}
    (source : WeightedBranchingResumption.Coalgebra State Answer V)
    (fuel : Nat) {n m : Nat} (initial : Fin m → State)
    (observe : Answer ⊕ State → Fin n) (inputIndex : Fin m) :
    (terms ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
      (sourceOperation source fuel initial observe)) inputIndex).run =
      (WeightedBranchingResumption.contributions source fuel
        (initial inputIndex)).map (fun leaf => (observe leaf.1, leaf.2)) := by
  change WeightedResumption.interpret WeightedBranchingResumption.catalogue
    (ResumptionAlgebra.bind
      (WeightedBranchingResumption.cut source fuel (initial inputIndex))
      (fun leaf => ResumptionAlgebra.pure (observe leaf))) = _
  rw [WeightedResumption.interpret_map, WeightedBranchingResumption.interpret_cut]

def operation (program : Program) (clause : WeighClause V Row) (fuel : Nat)
    {n m : Nat} (initial : Fin m → WorkState) (observe : WorkState ⊕ WorkState → Fin n) :
    arityObject V n ⟶ arityObject V m :=
  sourceOperation (source program clause) fuel initial observe

/-- The open operation is checked against the actual native frontier,
which is executed independently of the free operation construction. -/
theorem native_operation_handler (program : Program) (clause : WeighClause V Row)
    (fuel : Nat) {n m : Nat} (initial : Fin m → WorkState)
    (observe : WorkState ⊕ WorkState → Fin n) (inputIndex : Fin m) :
    (terms ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
      (operation program clause fuel initial observe)) inputIndex).run =
      (WeightedBranchingResumption.contributions (source program clause) fuel
        (initial inputIndex)).map (fun leaf => (observe leaf.1, leaf.2)) :=
  source_operation_handler _ _ _ _ _

/-- The common linear interpretation acts on independently executed native
contributions. The finite observer is explicit, and aggregation is downstream
of the occurrence-sensitive frontier. -/
theorem native_operation_linear {S : Type} [CommSemiring S]
    (program : Program) (clause : WeighClause S Row) (fuel : Nat) {n m : Nat}
    (initial : Fin m → WorkState) (observe : WorkState ⊕ WorkState → Fin n)
    (valuation : Fin n → S) (inputIndex : Fin m) :
    WeightedLinearInterpretation.operationLinearMap
        ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
          (operation program clause fuel initial observe)) valuation inputIndex =
      WeightedLinearInterpretation.evaluate
        (WeightedBranchingResumption.contributions (source program clause) fuel (initial inputIndex))
        (fun leaf => valuation (observe leaf)) := by
  change WeightedLinearInterpretation.evaluate
    (terms ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
      (operation program clause fuel initial observe)) inputIndex).run valuation = _
  rw [native_operation_handler]
  exact WeightedLinearInterpretation.evaluate_reindex _ observe valuation

/-- Nested native coefficient continuations inhabit the same free operation
theory. Open inputs carry their own captured worlds and argument bindings. -/
def nestedOperation (program : Program)
    (annotation : Row → Option Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (interpretation : Outcome → Option V)
    (fuel : Nat) {n m : Nat} (initial : Fin m → NestedWork)
    (observe : NestedResult ⊕ NestedWork → Fin n) :
    sourceArity NestedWork V n ⟶ sourceArity NestedWork V m :=
  sourceOperation (nestedSource program annotation interpretation) fuel initial observe

theorem native_nested_operation_handler (program : Program)
    (annotation : Row → Option Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (interpretation : Outcome → Option V)
    (fuel : Nat) {n m : Nat} (initial : Fin m → NestedWork)
    (observe : NestedResult ⊕ NestedWork → Fin n) (inputIndex : Fin m) :
    (terms ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
      (nestedOperation program annotation interpretation fuel initial observe)) inputIndex).run =
      (WeightedBranchingResumption.contributions (nestedSource program annotation interpretation)
        fuel (initial inputIndex)).map (fun leaf => (observe leaf.1, leaf.2)) :=
  source_operation_handler _ _ _ _ _

/-- The extensional linear reading agrees with independently executed nested
native contributions. It keeps the scalar-linearity qualification explicit. -/
theorem native_nested_operation_linear {S : Type} [CommSemiring S]
    (program : Program)
    (annotation : Row → Option Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (interpretation : Outcome → Option S)
    (fuel : Nat) {n m : Nat} (initial : Fin m → NestedWork)
    (observe : NestedResult ⊕ NestedWork → Fin n)
    (valuation : Fin n → S) (inputIndex : Fin m) :
    WeightedLinearInterpretation.operationLinearMap
        ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
          (nestedOperation program annotation interpretation fuel initial observe))
        valuation inputIndex =
      WeightedLinearInterpretation.evaluate
        (WeightedBranchingResumption.contributions (nestedSource program annotation interpretation)
          fuel (initial inputIndex)) (fun leaf => valuation (observe leaf)) := by
  change WeightedLinearInterpretation.evaluate
    (terms ((ResumptionOperationTheory.handler WeightedBranchingResumption.catalogue).map
      (nestedOperation program annotation interpretation fuel initial observe)) inputIndex).run
      valuation = _
  rw [native_nested_operation_handler]
  exact WeightedLinearInterpretation.evaluate_reindex _ observe valuation

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeOperationTheory
