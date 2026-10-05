import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeConformance

/-!
# From binding observations to materialized invocation

A reachable runtime binding record has its own canonical resolver as a
model. Consequently, equality in every model determines equal instantiated
syntax. The existing minimal interpreter applies that instantiation before
native dispatch; its invocation operation therefore respects the observation.
This is stronger than a raw dispatch relation on unresolved arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaTypeConformance

/-- The actual runtime resolver is one of the models quantified by the
specification's binding observation. Its satisfaction follows from the
existing reachable-state invariant. -/
theorem LeaQueryOpBindingInvariant.materializes_observation
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    {left right : Atom}
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation left right) :
    Metta.instantiate runtime (toLeaTTaAtom left) =
      Metta.instantiate runtime (toLeaTTaAtom right) := by
  rw [← applyClassSolution_lea_eq_instantiate,
    ← applyClassSolution_lea_eq_instantiate]
  exact observed (leaClassSolution runtime)
    ((invariant.solutionTheory _).mpr invariant.runtime.canonical.1)

/-- Closed observed data has exactly its original syntax after actual
instantiation, rather than merely an equal observation in the carried frame. -/
theorem LeaQueryOpBindingInvariant.materializes_closed
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    {atom expected : Atom} (closed : (toLeaTTaAtom expected).vars = [])
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation atom expected) :
    Metta.instantiate runtime (toLeaTTaAtom atom) = toLeaTTaAtom expected := by
  rw [invariant.materializes_observation observed,
    ← applyClassSolution_lea_eq_instantiate]
  calc
    _ = applyClassSolution (fun name => .var name) (toLeaTTaAtom expected) := by
      apply applyClassSolution_congr_on_atom_vars
      intro name member
      simp only [closed, List.not_mem_nil] at member
    _ = _ := Spec.Match.ModelTheory.applyClassSolution_identity _

/-- Actual `evalOp` substitutes bindings before inspecting the head or
arguments. Equality after this substitution is an invocation congruence. -/
theorem evalOp_eq_of_instantiate_eq
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) (bindings : Metta.Bindings)
    {left right : Metta.Atom}
    (same : Metta.instantiate bindings left = Metta.instantiate bindings right) :
    Metta.Minimal.evalOp environment state continuation left bindings =
      Metta.Minimal.evalOp environment state continuation right bindings := by
  unfold Metta.Minimal.evalOp
  rw [same]

/-- Binding observations may be used at the actual interpreter's invocation
boundary, because that boundary materializes the arguments first. -/
theorem LeaQueryOpBindingInvariant.evalOp_observation
    {spec : Bindings} {runtime : Metta.Bindings}
    (invariant : LeaQueryOpBindingInvariant spec runtime)
    (environment : Metta.Minimal.MinEnv) (state : Metta.Minimal.St)
    (continuation : Metta.Minimal.Stack) {left right : Atom}
    (observed : ∀ valuation, HEBindingSatisfied valuation spec →
      HEAtomEquationSatisfied valuation left right) :
    Metta.Minimal.evalOp environment state continuation (toLeaTTaAtom left) runtime =
      Metta.Minimal.evalOp environment state continuation (toLeaTTaAtom right) runtime :=
  evalOp_eq_of_instantiate_eq environment state continuation runtime
    (invariant.materializes_observation observed)

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
