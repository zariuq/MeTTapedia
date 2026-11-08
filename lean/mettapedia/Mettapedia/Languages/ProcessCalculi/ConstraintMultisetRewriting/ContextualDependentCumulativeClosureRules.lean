import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCumulativeClosureChain
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentMillerClosurePermutedTransfer

/-!
# Closure of the cumulative round: the obligations discharged on the permuted Miller class

The obligations of `ContextualDependentCumulativeClosure.Obligations`, for the class `PermutedMiller`:

* **the occurs checks** only refute (`occursSearch_refutes`, `occursFullSearch_refutes`), so they keep every class;
* **twin collapse** retypes twins equation by equation (`collapse_keeps`, R119's `permutedMiller_collapse_update`);
* **the conversion scan** drops the equations that hold at every substitution (`scan_eq_filter`, `conversion_keeps`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCumulativeClosure

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentFragment ContextualDependentRank
open ContextualDependentMillerClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-! ## Rules that only refute -/

section Refuting

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

/-- **R96's occurs check only refutes.** -/
theorem occursSearch_refutes {Θ : Context S.R} :
    ∀ (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem)
      (smaller : update.target.arity < Θ.arity),
      ContextualDependentOccursCheck.occursSearch facts roots heads algebra rigid complete problem ≠
        some (.solved update smaller)
  | [], _, _ => fun fired => by cases fired
  | equation :: rest, update, smaller => by
      intro fired
      simp only [ContextualDependentOccursCheck.occursSearch] at fired
      split at fired
      · cases fired
      · split at fired
        · cases fired
        · obtain ⟨inner, computed, same⟩ := Option.map_eq_some_iff.mp fired
          cases inner with
          | solved moved movedSmaller => exact occursSearch_refutes rest moved movedSmaller computed
          | refuted absent => cases same

/-- **The full occurs check only refutes.** -/
theorem occursFullSearch_refutes {Θ : Context S.R} :
    ∀ (problem : EquationStore (TotalTerm Θ)) (update : Update S.levels problem)
      (smaller : update.target.arity < Θ.arity),
      ContextualDependentOccursFull.occursFullSearch facts roots heads algebra rigid complete problem ≠
        some (.solved update smaller)
  | [], _, _ => fun fired => by cases fired
  | equation :: rest, update, smaller => by
      intro fired
      simp only [ContextualDependentOccursFull.occursFullSearch] at fired
      split at fired
      · cases fired
      · split at fired
        · cases fired
        · obtain ⟨inner, computed, same⟩ := Option.map_eq_some_iff.mp fired
          cases inner with
          | solved moved movedSmaller => exact occursFullSearch_refutes rest moved movedSmaller computed
          | refuted absent => cases same

theorem occursSearch_keeps (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop) :
    RuleKeeps holds fun problem =>
      ContextualDependentOccursCheck.occursSearch facts roots heads algebra rigid complete problem :=
  fun _ problem _ update smaller fired =>
    absurd fired (occursSearch_refutes facts roots heads algebra rigid complete problem update smaller)

theorem occursFullSearch_keeps (holds : {Γ : Context S.R} → EquationStore (TotalTerm Γ) → Prop) :
    RuleKeeps holds fun problem =>
      ContextualDependentOccursFull.occursFullSearch facts roots heads algebra rigid complete problem :=
  fun _ problem _ update smaller fired =>
    absurd fired (occursFullSearch_refutes facts roots heads algebra rigid complete problem update smaller)

end Refuting

/-! ## Twin collapse and the conversion scan -/

section Scan

variable [DecidableEq Head] [DecidableRel S.R.headEq] [∀ head, Decidable (S.R.isUniverse head)]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (reducer : ExecutableReduction.Reducer S.R)

/-- **Twin collapse keeps the permuted class.** -/
theorem collapse_keeps (fuel : Nat) :
    UpdateKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentTwinsUnder.collapse facts roots heads algebra reducer fuel problem :=
  fun _ _ permuted => permutedMiller_collapse_update facts roots heads algebra reducer fuel permuted

/-- **The conversion scan is a filter**: it keeps the equations it cannot certify. -/
theorem scan_eq_filter (fuel : Nat) {Γ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Γ),
      Conversion.scan facts roots heads algebra reducer fuel problem =
        problem.filter fun equation =>
          (Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2).isNone
  | [] => rfl
  | equation :: rest => by
      simp only [Conversion.scan]
      cases checked : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
      | none =>
          rw [List.filter_cons_of_pos (by simp [checked])]
          exact congrArg _ (scan_eq_filter fuel rest)
      | some certificate =>
          rw [List.filter_cons_of_neg (by simp [checked])]
          exact scan_eq_filter fuel rest

/-- **The conversion scan keeps the permuted class**: it drops only equations that hold at every substitution. -/
theorem conversion_keeps (fuel : Nat) :
    UpdateKeeps (fun problem => PermutedMiller S.levels problem) fun problem =>
      ContextualDependentUpdate.conversion facts roots heads algebra reducer fuel problem := by
  intro Θ problem permuted
  change PermutedMiller S.levels (Conversion.scan facts roots heads algebra reducer fuel problem)
  rw [scan_eq_filter]
  refine PermutedMiller.filter_valid _ (fun equation dropped Δ σ => ?_) permuted
  cases checked : Conversion.compare facts roots heads algebra reducer fuel equation.1 equation.2 with
  | none => simp [checked] at dropped
  | some certificate => exact (frames S.levels).preserves σ certificate.down

end Scan

end ContextualDependentCumulativeClosure
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
