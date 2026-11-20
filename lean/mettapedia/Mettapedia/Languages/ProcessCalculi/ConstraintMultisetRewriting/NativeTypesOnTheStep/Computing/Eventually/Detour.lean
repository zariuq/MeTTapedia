import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Limits

/-!
# The order of reduction: a typed term with a normal form that the full normalizer never reaches

The tree's full normalizer (`ExecutableReduction.normalize`) tries the root evaluator, then β and the
projections at the root, then the subterms from left to right. A row that inspects a later argument is
not left-normal: where its inspected argument still computes, the normalizer first reduces the
arguments to its left, and an argument that unfolds into a copy of the whole term keeps it there.

The package `detourTower`, over the tower, has a small type `nat` whose one constructor is `zero`,
constants `b` and `d` of `nat`, a function `e : nat → nat → nat`, and three rows: `b ⟶ zero`;
`e x zero ⟶ zero`, which inspects its second argument; and `d ⟶ e d b`. Its root evaluator is
complete (`detourRoot_complete`).

* `d` is typed at `nat` (`detour_typed`). It has the normal form `zero` (`detour_reduces`,
  `zero_normal`): reduce `b` inside `e d b`, then the row of `e`. It has the weak-head normal form `zero`
  under the roles in which `e` inspects its second argument (`detour_whRed`, `zero_whnf`).
* `d` is not strongly normalizing (`detour_not_sn`): `d ⟶ e d b ⟶ e (e d b) b ⟶ …`.
* **The full normalizer fails on `d` at every budget** (`detour_normalize_none`): each of its steps
  unfolds the leftmost `d` (`step_tower`), so it never reaches the inspected argument `b`.

So, for a single typed term, neither a weak-head normal form nor a normal form makes the tree's full
normalizer terminate: what fails is its order of reduction. Whether this package meets the hypotheses
of the general theorems (`Qualified`, completeness of the algorithmic equality, weak-head normal forms
for every typed term) is not established here: its rows define `b` and `d` at arity zero, outside the
format of the tree's constructor systems, which asks for a positive arity. A package that meets them,
with the same failure of the full normalizer, is in `Erasing` (`Erasing.separation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually
namespace Detour

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableReduction

/-- The names of the package. -/
def natName : DeclName := .mkSimple "nat"
def zeroName : DeclName := .mkSimple "zero"
def bName : DeclName := .mkSimple "b"
def eName : DeclName := .mkSimple "e"
def dName : DeclName := .mkSimple "d"

theorem b_ne_zero : bName ≠ zeroName := by decide
theorem d_ne_b : dName ≠ bName := by decide
theorem e_ne_b : eName ≠ bName := by decide
theorem e_ne_d : eName ≠ dName := by decide
theorem d_ne_e : dName ≠ eName := by decide
theorem zero_ne_b : zeroName ≠ bName := by decide
theorem zero_ne_d : zeroName ≠ dName := by decide
theorem zero_ne_e : zeroName ≠ eName := by decide
theorem d_ne_nat : dName ≠ natName := by decide
theorem nat_ne_e : natName ≠ eName := by decide
theorem zero_ne_nat : zeroName ≠ natName := by decide

/-- `e x y`. -/
abbrev eApp {n : Nat} (x y : Tm Tower.Head n) : Tm Tower.Head n := .app (.app (.const eName) x) y

/-- **The rows**: `b ⟶ zero`; `e x zero ⟶ zero`; `d ⟶ e d b`. -/
def detourComputation : RootComputation Tower.Head where
  step := fun l r =>
    (l = .const bName ∧ r = .const zeroName) ∨
    (∃ x, l = eApp x (.const zeroName) ∧ r = .const zeroName) ∨
    (l = .const dName ∧ r = eApp (.const dName) (.const bName))
  rename := by
    intro n m ρ l r h
    rcases h with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨Presentation.rename ρ x, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  substitute := by
    intro n m σ l r h
    rcases h with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨subst σ x, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **The package**: the tower with a small type `nat` whose one constructor is `zero`, the
constants `b` and `d` of `nat`, a function `e : nat → nat → nat`, and the three rows. -/
def detourTower : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = natName then some (.head (.sort (.const 0)))
      else if name = eName then some (.pi (.const natName) (.pi (.const natName) (.const natName)))
      else if name = zeroName ∨ name = bName ∨ name = dName then some (.const natName)
      else none
    computation := detourComputation }

/-- `nat` is a small type. -/
theorem nat_typed : Typed detourTower .nil (.const natName) (.head (.sort (.const 0))) := by
  have declared : detourTower.constantType natName = some (.head (.sort (.const 0))) := by
    simp [detourTower]
  exact .const declared (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

/-- `d` is a term of `nat`. -/
theorem detour_typed : Typed detourTower .nil (.const dName) (.const natName) := by
  have declared : detourTower.constantType dName = some (.const natName) := by
    simp [detourTower, d_ne_e, d_ne_nat]
  exact .const declared nat_typed (LevelTower.IsUniverse.sort _)

/-- **The root evaluator** of the three rows. -/
def detourRoot : RootEvaluator detourTower := fun {_} t => match t with
  | .const c =>
      if hb : c = bName then some ⟨.const zeroName, Or.inl ⟨by rw [hb], rfl⟩⟩
      else if hd : c = dName then
        some ⟨eApp (.const dName) (.const bName), Or.inr (Or.inr ⟨by rw [hd], rfl⟩)⟩
      else none
  | .app (.app (.const c) x) (.const z) =>
      if h : c = eName ∧ z = zeroName then
        some ⟨.const zeroName, Or.inr (Or.inl ⟨x, by rw [h.1, h.2], rfl⟩)⟩
      else none
  | _ => none

/-- **The root evaluator is complete.** -/
theorem detourRoot_complete : RootComplete detourTower detourRoot := by
  intro n t none' u step
  rcases step with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [detourRoot] at none'
  · simp [detourRoot] at none'
  · simp [detourRoot, d_ne_b] at none'

/-! ## A normal form, and a weak-head normal form -/

theorem step_b : detourTower.computation.step (.const bName : Tm Tower.Head 0) (.const zeroName) :=
  Or.inl ⟨rfl, rfl⟩

theorem step_d : detourTower.computation.step (.const dName : Tm Tower.Head 0)
    (eApp (.const dName) (.const bName)) :=
  Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem step_e (x : Tm Tower.Head 0) :
    detourTower.computation.step (eApp x (.const zeroName)) (.const zeroName) :=
  Or.inr (Or.inl ⟨x, rfl, rfl⟩)

/-- **`d` reduces to `zero`**: `d ⟶ e d b ⟶ e d zero ⟶ zero`. -/
theorem detour_reduces :
    Relation.ReflTransGen (StepCore detourTower.computation detourTower.headEq)
      (.const dName : Tm Tower.Head 0) (.const zeroName) :=
  ((Relation.ReflTransGen.single (.root step_d)).tail (.congAppArg (.root step_b))).tail
    (.root (step_e _))

/-- No row starts at `zero`. -/
theorem no_row_at_zero (u : Tm Tower.Head 0) :
    ¬ detourTower.computation.step (.const zeroName) u := by
  rintro (⟨same, -⟩ | ⟨x, same, -⟩ | ⟨same, -⟩)
  · exact zero_ne_b (Tm.const.inj same)
  · cases same
  · exact zero_ne_d (Tm.const.inj same)

/-- **`zero` is a normal form**: no step leaves it. -/
theorem zero_normal (u : Tm Tower.Head 0) :
    ¬ StepCore detourTower.computation detourTower.headEq (.const zeroName) u := by
  intro step
  generalize source : (.const zeroName : Tm Tower.Head 0) = t at step
  cases step with
  | root h =>
      subst source
      exact no_row_at_zero u h
  | _ => cases source

/-- The roles: `nat` is an inductive type whose one constructor is `zero`; `e` inspects its second
argument; `b` and `d` compute at arity zero. -/
def detourRoles : Roles Tower.Head := fun name =>
  if name = natName then .inductive [(zeroName, [])]
  else if name = eName then .computes 2 (.split 1 .constructor fun _ => .leaf)
  else if name = bName ∨ name = dName then .computes 0 .leaf
  else if name = zeroName then .constructor 0
  else .rigid

theorem detourRoles_e : detourRoles eName = .computes 2 (.split 1 .constructor fun _ => .leaf) := by
  simp [detourRoles, nat_ne_e.symm]

theorem detourRoles_zero : detourRoles zeroName = .constructor 0 := by
  simp [detourRoles, zero_ne_e, zero_ne_b, zero_ne_d, zero_ne_nat]

/-- **`d` reaches the weak-head normal form `zero`**: the scrutinee `b` is reduced before the row of
`e` fires. -/
theorem detour_whRed :
    WhRed detourTower detourRoles (.const dName : Tm Tower.Head 0) (.const zeroName) := by
  have unfold : WhStep detourTower detourRoles (.const dName) (eApp (.const dName) (.const bName)) :=
    .root step_d
  have scrutinee : WhStep detourTower detourRoles (eApp (.const dName) (.const bName))
      (eApp (.const dName) (.const zeroName)) :=
    WhStep.scrutinee_single (before := [.const dName]) (after := []) detourRoles_e rfl (.root step_b)
  exact ((Relation.ReflTransGen.single unfold).tail scrutinee).tail (.root (step_e _))

/-- `zero` is no spine of a computing constant. -/
theorem zero_not_computing_spine {c : DeclName} {args : List (Tm Tower.Head 0)} {arity : Nat}
    {inspect : InspectTree} (role : detourRoles c = .computes arity inspect)
    (same : (.const zeroName : Tm Tower.Head 0) = appSpine (.const c) args) : False := by
  rcases appSpine_const_cases c args with spine | ⟨f, a, spine⟩
  · rw [spine] at same
    rw [← Tm.const.inj same, detourRoles_zero] at role
    cases role
  · rw [spine] at same
    cases same

/-- **`zero` is weak-head normal.** -/
theorem zero_whnf : Whnf detourTower detourRoles (.const zeroName : Tm Tower.Head 0) := by
  intro u step
  generalize source : (.const zeroName : Tm Tower.Head 0) = t at step
  cases step with
  | root h =>
      subst source
      exact no_row_at_zero u h
  | scrutinee role _ _ _ => exact zero_not_computing_spine role source
  | _ => cases source

/-! ## Not strongly normalizing -/

/-- `d`, and `e (…) b` around it `k` times. -/
def tower : Nat → Tm Tower.Head 0
  | 0 => .const dName
  | k + 1 => eApp (tower k) (.const bName)

/-- Each term of the tower steps to the next, unfolding its leftmost `d`. -/
theorem tower_reduces : ∀ k, StrongNormalization.Reduces detourTower (tower k) (tower (k + 1))
  | 0 => .root step_d
  | k + 1 => .congAppFun (.congAppArg (tower_reduces k))

/-- **`d` is not strongly normalizing.** -/
theorem detour_not_sn : ¬ StrongNormalization.SN detourTower (.const dName : Tm Tower.Head 0) := by
  intro sn
  have never : ∀ t, StrongNormalization.SN detourTower t → ∀ k, tower k = t → False := by
    intro t accessible
    induction accessible with
    | intro t _ ih =>
        intro k same
        subst same
        exact ih (tower (k + 1)) (tower_reduces k) (k + 1) rfl
  exact never _ sn 0 rfl

/-! ## The full normalizer never reaches the inspected argument -/

theorem root_const_e : detourRoot (.const eName : Tm Tower.Head 0) = none := by
  simp [detourRoot, e_ne_b, e_ne_d]

theorem step_const_e : step detourTower detourRoot (.const eName : Tm Tower.Head 0) = none := by
  rw [ExecutableReduction.step, root_const_e]

theorem root_app_e (x : Tm Tower.Head 0) : detourRoot (.app (.const eName) x) = none := by
  cases x <;> rfl

theorem root_tower_succ (k : Nat) : detourRoot (tower (k + 1)) = none := by
  show detourRoot (eApp (tower k) (.const bName)) = none
  simp [detourRoot, b_ne_zero]

/-- At `e x`, the normalizer steps inside `x`. -/
theorem step_app_e {x : Tm Tower.Head 0} {next : StepResult detourTower x}
    (stepped : step detourTower detourRoot x = some next) :
    (step detourTower detourRoot (.app (.const eName) x)).map Subtype.val =
      some (.app (.const eName) next.val) := by
  rw [ExecutableReduction.step, root_app_e]
  simp only [step_const_e, stepped, Option.map_some]
  intro body same
  cases same

/-- **Each step of the normalizer unfolds the leftmost `d`.** -/
theorem step_tower : ∀ k, (step detourTower detourRoot (tower k)).map Subtype.val = some (tower (k + 1))
  | 0 => by
      show (step detourTower detourRoot (.const dName)).map Subtype.val =
        some (eApp (.const dName) (.const bName))
      rw [ExecutableReduction.step]
      simp [detourRoot, d_ne_b]
  | k + 1 => by
      have ih := step_tower k
      cases hk : step detourTower detourRoot (tower k) with
      | none =>
          rw [hk] at ih
          cases ih
      | some next =>
          rw [hk] at ih
          simp only [Option.map_some, Option.some.injEq] at ih
          have inner := step_app_e hk
          cases hf : step detourTower detourRoot (.app (.const eName) (tower k)) with
          | none =>
              rw [hf] at inner
              cases inner
          | some next' =>
              rw [hf] at inner
              simp only [Option.map_some, Option.some.injEq] at inner
              show (step detourTower detourRoot (.app (.app (.const eName) (tower k)) (.const bName))).map
                Subtype.val = some (eApp (tower (k + 1)) (.const bName))
              rw [ExecutableReduction.step,
                show detourRoot (.app (.app (.const eName) (tower k)) (.const bName)) = none from
                  root_tower_succ k]
              simp only [hf, Option.map_some, inner, ih]
              intro body same
              cases same

/-- The normalizer returns nothing from any term of the tower, at any budget. -/
theorem tower_normalize_none : ∀ (fuel k : Nat), normalize detourTower detourRoot fuel (tower k) = none
  | 0, _ => rfl
  | fuel + 1, k => by
      have stepped := step_tower k
      cases h : step detourTower detourRoot (tower k) with
      | none =>
          rw [h] at stepped
          cases stepped
      | some next =>
          rw [h] at stepped
          obtain ⟨v, pv⟩ := next
          simp only [Option.map_some, Option.some.injEq] at stepped
          subst stepped
          rw [ExecutableReduction.normalize, h]
          simp only [tower_normalize_none fuel (k + 1)]

/-- **The full normalizer fails on `d` at every budget.** -/
theorem detour_normalize_none (fuel : Nat) :
    normalize detourTower detourRoot fuel (.const dName : Tm Tower.Head 0) = none :=
  tower_normalize_none fuel 0

/-- **A typed term with a normal form and a weak-head normal form on which the full normalizer fails at
every budget**, with a complete root evaluator, in a package that is not strongly normalizing. -/
theorem detour :
    RootComplete detourTower detourRoot ∧
      Typed detourTower .nil (.const dName) (.const natName) ∧
      Relation.ReflTransGen (StepCore detourTower.computation detourTower.headEq)
        (.const dName : Tm Tower.Head 0) (.const zeroName) ∧
      (∀ u, ¬ StepCore detourTower.computation detourTower.headEq (.const zeroName : Tm Tower.Head 0) u) ∧
      WhRed detourTower detourRoles (.const dName : Tm Tower.Head 0) (.const zeroName) ∧
      Whnf detourTower detourRoles (.const zeroName : Tm Tower.Head 0) ∧
      ¬ StrongNormalization.SN detourTower (.const dName : Tm Tower.Head 0) ∧
      ∀ fuel, normalize detourTower detourRoot fuel (.const dName : Tm Tower.Head 0) = none :=
  ⟨detourRoot_complete, detour_typed, detour_reduces, zero_normal, detour_whRed, zero_whnf,
    detour_not_sn, detour_normalize_none⟩

#print axioms detourRoot_complete
#print axioms detour_typed
#print axioms detour_reduces
#print axioms zero_normal
#print axioms detour_whRed
#print axioms zero_whnf
#print axioms detour_not_sn
#print axioms step_tower
#print axioms detour_normalize_none
#print axioms detour

end Detour
end NativeTypesOnTheStep.Computing.Eventually
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
