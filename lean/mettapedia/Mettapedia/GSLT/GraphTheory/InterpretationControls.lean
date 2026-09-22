import Mettapedia.GSLT.GraphTheory.Interpretation
import Mettapedia.GSLT.Core.WebSemanticsControls

/-! Nonconstant, capture-sensitive, and inhabited controls for graph interpretation. -/

namespace Mettapedia.GSLT.GraphTheory.InterpretationControls

open Mettapedia.GSLT.Core

variable (D : GraphModel)

private def naturalEnv : Env GraphModel.naturalModel := fun n => {n}

/-- Identity computation returns the input's actual denotation. -/
theorem identity_on_variable (ρ : Env D) (n : Nat) :
    interpret D ρ (.app LambdaTerm.I (.var n)) = ρ n := by
  simpa [LambdaTerm.I, LambdaTerm.subst, interpret] using
    interpret_beta D (.var 0) (.var n) ρ

/-- A real model distinguishes two inputs to the same identity program. -/
theorem natural_identity_distinguishes_inputs :
    interpret GraphModel.naturalModel naturalEnv
      (.app LambdaTerm.I (.var 0)) ≠
    interpret GraphModel.naturalModel naturalEnv
      (.app LambdaTerm.I (.var 1)) := by
  rw [identity_on_variable, identity_on_variable]
  change ({0} : Set Nat) ≠ {1}
  intro h
  have := Set.singleton_injective h
  omega

/-- Passing an old variable through a new binder preserves its dependency. -/
theorem old_variable_beta (ρ : Env D) :
    interpret D ρ (.app (.lam (.lam (.var 1))) (.var 0)) =
      interpret D ρ (.lam (.var 1)) := by
  simpa [LambdaTerm.subst, LambdaTerm.shift] using
    interpret_beta D (.lam (.var 1)) (.var 0) ρ

/-- Applying the two candidate functions to a different set exposes capture. -/
theorem old_variable_not_captured (ρ : Env D) (argument : Set D.Carrier)
    (different : ρ 0 ≠ argument) :
    interpret D ρ (.app (.lam (.lam (.var 1))) (.var 0)) ≠
      interpret D ρ (.lam (.var 0)) := by
  rw [old_variable_beta]
  intro h
  have hApplied := congrArg (fun functions => D.apply functions argument) h
  change D.apply (D.abstraction (fun _ => ρ 0)) argument =
    D.apply (D.abstraction id) argument at hApplied
  rw [D.apply_abstraction (fun _ : Set D.Carrier => ρ 0)
      (ScottContinuous.const (ρ 0)),
    D.apply_abstraction id ScottContinuous.id] at hApplied
  exact different hApplied

/-- The capture-incorrect body is distinguishable in an actual natural-number model. -/
theorem natural_old_variable_not_captured :
    interpret GraphModel.naturalModel naturalEnv
      (.app (.lam (.lam (.var 1))) (.var 0)) ≠
    interpret GraphModel.naturalModel naturalEnv (.lam (.var 0)) := by
  apply old_variable_not_captured GraphModel.naturalModel naturalEnv (naturalEnv 1)
  change ({0} : Set Nat) ≠ {1}
  intro h
  have := Set.singleton_injective h
  omega

/-- The model class now has an actual consistent instance, not a vacuous interface. -/
theorem natural_graph_theory_inhabited :
    IsGraphTheory (lambdaTheoryOf GraphModel.naturalModel) ∧
      (lambdaTheoryOf GraphModel.naturalModel).Consistent :=
  ⟨lambdaTheoryOf_isGraphTheory _, lambdaTheoryOf_consistent _⟩

/-- A beta redex can be solvable without already being in head normal form. -/
theorem identity_redex_solvable (n : Nat) :
    (LambdaTerm.app LambdaTerm.I (.var n)).Solvable ∧
      (LambdaTerm.app LambdaTerm.I (.var n)).isHNF = false := by
  refine ⟨?_, rfl⟩
  refine ⟨.var n, Relation.ReflTransGen.single ?_, rfl⟩
  simpa [LambdaTerm.I, LambdaTerm.subst] using
    ParRed.beta (ParRed.var 0) (ParRed.var n)

/-- The reduction-sensitive negative control does not depend on a fuel limit. -/
theorem Omega_remains_unsolvable : LambdaTerm.Omega.Unsolvable := Omega_unsolvable

/-- An empty intersection would identify I and K; no graph model has that theory. -/
theorem no_universal_graph_theory {theory : LambdaTheory}
    (allEquations : theory.equations = Set.univ) : ¬IsGraphTheory theory := by
  rintro ⟨model, sameEquations⟩
  have hIK : ⟨LambdaTerm.I, LambdaTerm.K⟩ ∈ theoryOf model := by
    rw [← sameEquations, allEquations]
    exact Set.mem_univ _
  exact lambdaTheoryOf_consistent model hIK

/-- The exact empty-family intersection is an explicit obstruction to claiming
unrestricted intersection closure. -/
theorem empty_intersection_not_graph :
    ¬∃ theory : LambdaTheory, IsGraphTheory theory ∧
      theory.equations = ⋂ member ∈ (∅ : Set LambdaTheory), member.equations := by
  rintro ⟨theory, isGraph, equations⟩
  have allEquations : theory.equations = Set.univ := by simpa using equations
  exact no_universal_graph_theory allEquations isGraph

end Mettapedia.GSLT.GraphTheory.InterpretationControls
