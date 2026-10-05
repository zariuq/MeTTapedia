import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlBinders
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaControlCorrespondence
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingMaterialization

/-!
# Binding observations at the native-argument boundary

The independent selector permits any emitted atom with the same observation
under the result bindings. Native dispatch, however, consumes syntactic
arguments. The example below separates these two contracts even for a
satisfiable frame containing only integer data. An execution correspondence
must account for binding materialization before native invocation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings Space)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps

/-- Ordinary integer equality, with a distinct result for noninteger operands.
It has no guest-kernel operation or access to a binding frame. -/
def integerEqualityDispatch : GroundedDispatch where
  executable operator := operator = .symbol "=="
  outcome operator arguments result := operator = .symbol "==" ∧
    result = match arguments with
      | [.grounded (.int left), .grounded (.int right)] =>
          .ok [(.symbol (if left = right then "True" else "False"), Bindings.empty)]
      | _ => .incorrectArgument

theorem integer_equality_closed (left right : Int) :
    integerEqualityDispatch.outcome (.symbol "==")
      [.grounded (.int left), .grounded (.int right)]
      (.ok [(.symbol (if left = right then "True" else "False"), Bindings.empty)]) :=
  ⟨rfl, rfl⟩

theorem integer_equality_symbolic_refusal (name : String) (right : Int) :
    integerEqualityDispatch.outcome (.symbol "==")
      [.var name, .grounded (.int right)] .incorrectArgument :=
  ⟨rfl, rfl⟩

/-- The minimal evaluator does not inspect the binding frame before passing
these symbolic arguments to the host. -/
theorem unresolved_integer_equality_run (name : String) (right : Int)
    (bindings : Bindings) :
    CoreRunRel Space.empty integerEqualityDispatch []
      (call "eval" [call "==" [.var name, .grounded (.int right)]]) bindings
      (Atom.notReducible, bindings) := by
  apply CoreRunRel.instruction
  · simp [call, embeddedInstruction]
  · simp [call, Minimal.IsChain]
  · apply CoreStepRel.eval
    exact CoreInvocationRel.groundedIncorrectArgument Space.empty (.symbol "==")
      [.var name, .grounded (.int right)] bindings rfl
      (integer_equality_symbolic_refusal name right)

/-- Matching a concrete zero may leave its variable in an emitted native
call, although every model assigns zero to that variable. The host call then
refuses its syntactic argument. Binding observation alone therefore cannot
be used as an execution-substitution theorem. -/
theorem observed_zero_need_not_be_materialized :
    ∃ output : Bindings,
      UnifySuccessRel (.grounded (.int 0)) (.var "fuel")
        (call "eval" [call "==" [.grounded (.int 0), .grounded (.int 0)]])
        Bindings.empty
        (call "eval" [call "==" [.var "fuel", .grounded (.int 0)]]) output ∧
      (∃ valuation, HEBindingSatisfied valuation output) ∧
      (∀ valuation, HEBindingSatisfied valuation output →
        HEAtomEquationSatisfied valuation (.var "fuel") (.grounded (.int 0))) ∧
      CoreRunRel Space.empty integerEqualityDispatch []
        (call "eval" [call "==" [.var "fuel", .grounded (.int 0)]]) output
        (Atom.notReducible, output) ∧
      (∀ valuation, HEBindingSatisfied valuation output →
        ¬HEAtomEquationSatisfied valuation Atom.notReducible (.symbol "True")) := by
  obtain ⟨output, candidate⟩ :=
    (unify_empty_iff_model (.grounded (.int 0)) (.var "fuel")).mpr
      ⟨fun _ => toLeaTTaAtom (.grounded (.int 0)), by
        simp only [HEAtomEquationSatisfied, toLeaTTaAtom, applyClassSolution]⟩
  have zero : ∀ valuation, HEBindingSatisfied valuation output →
      HEAtomEquationSatisfied valuation (.var "fuel") (.grounded (.int 0)) := by
    intro valuation satisfied
    exact ((candidate_solution_iff candidate valuation).mp satisfied).2.symm
  refine ⟨output, ⟨candidate, ?_⟩, ?_, zero,
    unresolved_integer_equality_run "fuel" 0 output, ?_⟩
  · intro valuation satisfied
    have assigned := zero valuation satisfied
    simp only [HEAtomEquationSatisfied, toLeaTTaAtom, applyClassSolution] at assigned
    simp [HEAtomEquationSatisfied, call, toLeaTTaAtom, toLeaTTaAtoms,
      applyClassSolution, assigned]
  · obtain ⟨_, _, _, _, satisfiable⟩ := candidate
    exact satisfiable
  · intro valuation _
    simp [HEAtomEquationSatisfied, Atom.notReducible, toLeaTTaAtom, applyClassSolution]

/-- The two fuel operations emitted by `withFuel` have the exact closed-call
execution after actual binding materialization. The raw selector observation
is sufficient at this boundary because `evalOp` performs the missing step. -/
theorem materialized_fuel_operations
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) (fuel : Atom) (remaining : Nat)
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation fuel (.grounded (.int remaining))) :
    Metta.Minimal.evalOp environment state continuation
        (toLeaTTaAtom (call "==" [fuel, .grounded (.int 0)])) runtime =
      Metta.Minimal.evalOp environment state continuation
        (toLeaTTaAtom (call "==" [.grounded (.int remaining), .grounded (.int 0)])) runtime ∧
    Metta.Minimal.evalOp environment state continuation
        (toLeaTTaAtom (call "-" [fuel, .grounded (.int 1)])) runtime =
      Metta.Minimal.evalOp environment state continuation
        (toLeaTTaAtom (call "-" [.grounded (.int remaining), .grounded (.int 1)])) runtime := by
  have invocation (head : String) (argument : Atom) :
      Metta.Minimal.evalOp environment state continuation
          (toLeaTTaAtom (call head [fuel, argument])) runtime =
        Metta.Minimal.evalOp environment state continuation
          (toLeaTTaAtom (call head [.grounded (.int remaining), argument])) runtime := by
    apply invariant.evalOp_observation environment state continuation
    intro valuation satisfied
    have same := observed valuation satisfied
    simp only [HEAtomEquationSatisfied] at same
    simp [HEAtomEquationSatisfied, call, toLeaTTaAtom, toLeaTTaAtoms,
      applyClassSolution, same]
  exact ⟨invocation "==" _, invocation "-" _⟩

/-- An actual singleton runtime frame removes the alias before equality;
the result holds for every surrounding runtime state and continuation. -/
theorem actual_zero_alias_materializes
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) :
    Metta.Minimal.evalOp environment state continuation
        (toLeaTTaAtom (call "==" [.var "fuel", .grounded (.int 0)]))
        [.val "fuel" (toLeaTTaAtom (.grounded (.int 0)))] =
      Metta.Minimal.evalOp environment state continuation
        (toLeaTTaAtom (call "==" [.grounded (.int 0), .grounded (.int 0)]))
        [.val "fuel" (toLeaTTaAtom (.grounded (.int 0)))] := by
  apply evalOp_eq_of_instantiate_eq
  simp [call, toLeaTTaAtom, toLeaTTaAtoms, toLeaTTaGround,
    Metta.instantiate, Metta.Bindings.resolveAtom,
    Metta.Bindings.resolve_singleton_val_self_of_not_mem, Metta.Atom.vars]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.MeTTaEmit.Control
