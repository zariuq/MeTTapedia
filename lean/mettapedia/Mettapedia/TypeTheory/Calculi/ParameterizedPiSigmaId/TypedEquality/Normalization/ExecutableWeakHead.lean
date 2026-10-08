import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableReduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Algorithmic.Relation

/-!
# Weak-head execution with one shared budget

Reduction visits function positions and projections, then the positions
declared by an inspection plan. It leaves lambda bodies, pair components and
uninspected arguments as written. Every recursive return carries its unused
budget; sequential calls use that remainder rather than the original budget.
The returned path is built from the independent contextual reduction relation.

Inspection plans are data, not normalization or typing witnesses. Any plan is
sound for reduction. A plan's agreement with a language's inspection skeleton
is a separate admission contract. The budget counts the visits of this
procedure, not C allocations, arithmetic operations or wall-clock time.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableWeakHead

variable {Head : Type}

/-- Paths inspected by native algebraic patterns. They never enter a binder. -/
inductive Path where
  | here
  | function (rest : Path)
  | argument (rest : Path)
  | reflexivity (rest : Path)
  deriving DecidableEq, Repr

abbrev Plan (Head : Type) := {n : Nat} → Tm Head n → List Path

structure Result (R : Rules Head) {n : Nat} (source : Tm Head n) (budget : Nat) where
  value : Tm Head n
  remaining : Nat
  remaining_le : remaining ≤ budget
  reduction : Reduces R source value

variable (R : Rules Head) (root : ExecutableReduction.RootEvaluator R) (plan : Plan Head)

private def finish {n budget : Nat} (source : Tm Head n) (remaining : Nat)
    (bound : remaining ≤ budget) : Result R source budget :=
  ⟨source, remaining, bound, .refl⟩

private def rebase {n firstBudget secondBudget : Nat} {source middle : Tm Head n}
    (initialPath : Reduces R source middle) (bound : secondBudget ≤ firstBudget)
    (result : Result R middle secondBudget) : Result R source firstBudget :=
  ⟨result.value, result.remaining, result.remaining_le.trans bound, initialPath.trans result.reduction⟩

mutual

def run : (budget : Nat) → {n : Nat} → (source : Tm Head n) → Option (Result R source budget)
  | 0, _, _ => none
  | budget+1, _, source => match source with
      | .app function argument => do
          let computed ← run budget function
          let functionPath : Reduces R (.app function argument) (.app computed.value argument) :=
            Reduces.congr (fun step => .congAppFun step) computed.reduction
          match shape : computed.value with
          | .lam body =>
              let next ← run computed.remaining (inst0 argument body)
              return rebase R
                (functionPath.trans (.single (shape ▸ StepCore.betaPi body argument)))
                (computed.remaining_le.trans (Nat.le_succ budget)) next
          | _ =>
              let spine := Tm.app computed.value argument
              let inspected ← runPaths computed.remaining (plan spine) spine
              let initialPath := functionPath.trans inspected.reduction
              let bound := inspected.remaining_le.trans
                (computed.remaining_le.trans (Nat.le_succ budget))
              match root inspected.value with
              | none => return ⟨inspected.value, inspected.remaining, bound, initialPath⟩
              | some next =>
                  let continued ← run inspected.remaining next.val
                  return rebase R (initialPath.trans (.single (.root next.property))) bound continued
      | .fst pair => do
          let computed ← run budget pair
          let pairPath : Reduces R (.fst pair) (.fst computed.value) :=
            Reduces.congr (fun step => .congFst step) computed.reduction
          match shape : computed.value with
          | .pair first second =>
              let next ← run computed.remaining first
              return rebase R
                (pairPath.trans (.single (shape ▸ StepCore.betaSigmaFst first second)))
                (computed.remaining_le.trans (Nat.le_succ budget)) next
          | _ => return ⟨.fst computed.value, computed.remaining,
              computed.remaining_le.trans (Nat.le_succ budget), pairPath⟩
      | .snd pair => do
          let computed ← run budget pair
          let pairPath : Reduces R (.snd pair) (.snd computed.value) :=
            Reduces.congr (fun step => .congSnd step) computed.reduction
          match shape : computed.value with
          | .pair first second =>
              let next ← run computed.remaining second
              return rebase R
                (pairPath.trans (.single (shape ▸ StepCore.betaSigmaSnd first second)))
                (computed.remaining_le.trans (Nat.le_succ budget)) next
          | _ => return ⟨.snd computed.value, computed.remaining,
              computed.remaining_le.trans (Nat.le_succ budget), pairPath⟩
      | .const name => match root (.const name) with
          | none => some (finish R (.const name) budget (Nat.le_succ budget))
          | some next => do
              let result ← run budget next.val
              return rebase R (.single (.root next.property)) (Nat.le_succ budget) result
      | other => some (finish R other budget (Nat.le_succ budget))
termination_by budget _ _ => budget
decreasing_by
  all_goals first
    | omega
    | (have bound := computed.remaining_le; omega)
    | (have bound := computed.remaining_le; have inspectedBound := inspected.remaining_le; omega)

def runAt : (budget : Nat) → {n : Nat} → Path → (source : Tm Head n) →
    Option (Result R source budget)
  | 0, _, _, _ => none
  | budget+1, _, path, source => match path, source with
      | .here, term => do
          let computed ← run budget term
          return rebase R .refl (Nat.le_succ budget) computed
      | .function rest, .app function argument => do
          let computed ← runAt budget rest function
          return ⟨.app computed.value argument, computed.remaining,
            computed.remaining_le.trans (Nat.le_succ budget),
            Reduces.congr (fun step => .congAppFun step) computed.reduction⟩
      | .argument rest, .app function argument => do
          let computed ← runAt budget rest argument
          return ⟨.app function computed.value, computed.remaining,
            computed.remaining_le.trans (Nat.le_succ budget),
            Reduces.congr (fun step => .congAppArg step) computed.reduction⟩
      | .reflexivity rest, .refl subject => do
          let computed ← runAt budget rest subject
          return ⟨.refl computed.value, computed.remaining,
            computed.remaining_le.trans (Nat.le_succ budget),
            Reduces.congr (fun step => .congRefl step) computed.reduction⟩
      | _, _ => none
termination_by budget _ _ _ => budget
decreasing_by all_goals omega

def runPaths : (budget : Nat) → {n : Nat} → List Path → (source : Tm Head n) →
    Option (Result R source budget)
  | _, _, [], source => some (finish R source _ (Nat.le_refl _))
  | 0, _, _ :: _, _ => none
  | budget+1, _, path :: paths, source => do
      let first ← runAt budget path source
      let rest ← runPaths first.remaining paths first.value
      return rebase R first.reduction (first.remaining_le.trans (Nat.le_succ budget)) rest
termination_by budget _ _ _ => budget
decreasing_by
  all_goals first
    | omega
    | (have bound := first.remaining_le; omega)

end

def value {n : Nat} (budget : Nat) (source : Tm Head n) : Option (Tm Head n) :=
  (run R root plan budget source).map Result.value

theorem value_sound {n budget : Nat} {source target : Tm Head n}
    (computed : value R root plan budget source = some target) : Reduces R source target := by
  unfold value at computed
  cases outcome : run R root plan budget source with
  | none => simp only [outcome, Option.map_none] at computed; cases computed
  | some result =>
      simp only [outcome, Option.map_some, Option.some.injEq] at computed
      exact computed ▸ result.reduction

def runValue {n : Nat} (budget : Nat) (source : Tm Head n) : Option (Tm Head n × Nat) :=
  (run R root plan budget source).map (fun result => (result.value, result.remaining))

theorem runValue_sound {n budget remaining : Nat} {source target : Tm Head n}
    (computed : runValue R root plan budget source = some (target, remaining)) :
    Reduces R source target ∧ remaining ≤ budget := by
  unfold runValue at computed
  cases outcome : run R root plan budget source with
  | none => simp only [outcome, Option.map_none] at computed; cases computed
  | some result =>
      simp only [outcome, Option.map_some, Option.some.injEq, Prod.mk.injEq] at computed
      obtain ⟨rfl, rfl⟩ := computed
      exact ⟨result.reduction, result.remaining_le⟩

end TypedEquality.Normalization.ExecutableWeakHead
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
