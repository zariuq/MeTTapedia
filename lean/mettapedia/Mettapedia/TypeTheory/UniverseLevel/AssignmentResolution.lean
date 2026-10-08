import Mettapedia.TypeTheory.UniverseLevel.Algebra

/-!
# Resolving level assignments and substituting schema arguments

Assignment resolution follows assigned expressions recursively. Simultaneous
substitution treats each supplied expression as an argument, without resolving
it again in the schema's parameter namespace. The two operations have different
semantics. This executable resolver is bounded by traversal depth; it is not a
model of a native shared instruction budget.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.UniverseLevel

variable {L : Type}

abbrev LevelAssignments (L : Type) := Nat → Option (LevelExpr L)

def LevelAssignments.substitution (assignments : LevelAssignments L) (index : Nat) : LevelExpr L :=
  (assignments index).getD (.param index)

inductive LevelAssignments.Resolves (assignments : LevelAssignments L) :
    LevelExpr L → LevelExpr L → Prop where
  | const (level : L) : Resolves assignments (.const level) (.const level)
  | unassigned {index : Nat} : assignments index = none →
      Resolves assignments (.param index) (.param index)
  | assigned {index : Nat} {replacement result : LevelExpr L} :
      assignments index = some replacement → replacement ≠ .param index →
      Resolves assignments replacement result → Resolves assignments (.param index) result
  | succ {source result : LevelExpr L} : Resolves assignments source result →
      Resolves assignments (.succ source) (.succ result)
  | max {first second firstResult secondResult : LevelExpr L} :
      Resolves assignments first firstResult → Resolves assignments second secondResult →
      Resolves assignments (.max first second) (.max firstResult secondResult)

def LevelAssignments.resolve [DecidableEq L] (assignments : LevelAssignments L) :
    Nat → (source : LevelExpr L) → Option {result // assignments.Resolves source result}
  | 0, _ => none
  | _fuel+1, .const level => some ⟨.const level, .const level⟩
  | fuel+1, .param index => match found : assignments index with
      | none => some ⟨.param index, .unassigned found⟩
      | some replacement =>
          if same : replacement = .param index then none else do
            let resolved ← assignments.resolve fuel replacement
            return ⟨resolved.val, .assigned found same resolved.property⟩
  | fuel+1, .succ source => do
      let resolved ← assignments.resolve fuel source
      return ⟨.succ resolved.val, .succ resolved.property⟩
  | fuel+1, .max first second => do
      let firstResolved ← assignments.resolve fuel first
      let secondResolved ← assignments.resolve fuel second
      return ⟨.max firstResolved.val secondResolved.val,
        .max firstResolved.property secondResolved.property⟩

def LevelAssignments.Compatible [LevelOrder L] (assignments : LevelAssignments L)
    (valuation : Nat → L) : Prop :=
  ∀ {index replacement}, assignments index = some replacement →
    valuation index = replacement.eval valuation

theorem LevelAssignments.Resolves.eval [LevelOrder L] {assignments : LevelAssignments L}
    {source result : LevelExpr L} (resolved : assignments.Resolves source result)
    {valuation : Nat → L} (compatible : assignments.Compatible valuation) :
    result.eval valuation = source.eval valuation := by
  induction resolved with
  | const _ => rfl
  | unassigned _ => rfl
  | assigned known _ _ ih => exact ih.trans (compatible known).symm
  | succ _ ih => simpa only [LevelExpr.eval] using congrArg LevelOrder.succ ih
  | max _ _ ihFirst ihSecond => simp only [LevelExpr.eval, ihFirst, ihSecond]

/-- Resolution preserves meaning under valuations satisfying the assignments.
Substitution instead composes an arbitrary valuation with the argument meanings. -/
theorem LevelAssignments.resolution_semantics [LevelOrder L] [DecidableEq L]
    {assignments : LevelAssignments L} {source result : LevelExpr L} {fuel : Nat}
    (computed : (assignments.resolve fuel source).map Subtype.val = some result)
    {valuation : Nat → L} (compatible : assignments.Compatible valuation) :
    result.eval valuation = source.eval valuation := by
  cases found : assignments.resolve fuel source with
  | none => simp only [found, Option.map_none, reduceCtorEq] at computed
  | some resolved =>
      simp only [found, Option.map_some, Option.some.injEq] at computed
      subst result
      exact resolved.property.eval compatible

namespace AssignmentResolutionControls

def chain : LevelAssignments Nat
  | 0 => some (.param 1)
  | 1 => some (.const 0)
  | _ => none

theorem recursive_resolution : (chain.resolve 3 (.param 0)).map Subtype.val = some (.const 0) := by
  decide +kernel

theorem simultaneous_argument : (LevelExpr.param 0).subst chain.substitution = .param 1 := rfl

theorem resolution_is_not_simultaneous :
    (chain.resolve 3 (.param 0)).map Subtype.val ≠
      some ((LevelExpr.param 0).subst chain.substitution) := by decide +kernel

def cycle : LevelAssignments Nat
  | 0 => some (.param 1)
  | 1 => some (.param 0)
  | _ => none

@[simp] theorem cycle_zero : cycle 0 = some (.param 1) := rfl
@[simp] theorem cycle_one : cycle 1 = some (.param 0) := rfl

theorem cycle_never_resolves (fuel : Nat) :
    cycle.resolve fuel (.param 0) = none ∧ cycle.resolve fuel (.param 1) = none := by
  induction fuel with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
      simp only [LevelAssignments.resolve, cycle_zero, cycle_one, ih.1, ih.2]
      constructor <;> split <;> rfl

theorem cycle_arguments_can_be_substituted :
    (LevelExpr.param 0).subst cycle.substitution = .param 1 ∧
      (LevelExpr.param 1).subst cycle.substitution = .param 0 := ⟨rfl, rfl⟩

theorem instantiation_does_not_reflect_universal_equality :
    ¬ (∀ valuation : Nat → Nat,
      (LevelExpr.param 0).eval valuation = (LevelExpr.const 0).eval valuation) ∧
      (LevelExpr.param 0).subst (fun _ => .const (0 : Nat)) =
        (LevelExpr.const 0).subst (fun _ => .const 0) := by
  refine ⟨?_, rfl⟩
  intro equal
  have impossible := equal (fun _ => 1)
  exact Nat.one_ne_zero impossible

end AssignmentResolutionControls
end Mettapedia.TypeTheory.UniverseLevel
