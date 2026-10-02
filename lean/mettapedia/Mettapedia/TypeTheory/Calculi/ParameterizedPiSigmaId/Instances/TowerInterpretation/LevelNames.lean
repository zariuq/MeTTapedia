import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerLevelSubstitution

/-!
# Level names: the levels as terms

A universe of the tower carries a level expression, and a level expression is not a term: a
term cannot take a level as an argument. This file adds the levels as terms, with no new term
former and no new rule of the judgment. The heads of the tower are extended by two heads that
carry level expressions (`Head`):

* `names b`, the type of the names of the levels below the level expression `b`;
* `name e`, the name of the level expression `e`.

The rules (`baseRules`), under bounds `Δ` on the level parameters:

* `name e : names b` when `e + 1 ≤ b` at the valuations that respect the bounds;
* `names b : U_b`;
* `names b ⊑ names b'` when `b ≤ b'`, so a name below `b` is a name below `b'` with no
  coercion;
* two names, or two types of names, are equal when their level expressions are;
* the universes are those of the tower, compared under the bounds.

A product over the levels below `b` is the dependent function type over `names b`, and a
function on levels is applied to the name of a level expression, which may mention level
parameters.

Level substitution acts on the new heads as on universes (`substLevelsHead`), and the rules are
stable under admissible substitutions (`HeadTyping.substLevels`, `Cumulative.substLevels`,
`HeadEq.substLevels`). Stronger bounds prove more (`HeadTyping.mono`). The annotated tower with
bounded parameters is contained in the package without declarations along the inclusion of
heads (`tower_morphism`); so the identity on a universe, derived in the tower, is derived here
(`identity_typed`).

Positive examples: the name of a level below a bound is a name below it, for closed levels
(`levelName_const_typed`) and for a bounded parameter (`levelName_param_typed`); below a bound
closed under the successor, the name of the successor of a bounded parameter
(`levelName_succ_param_typed`); the names below a level are names below every greater one
(`levelsBelow_sub`); two expressions with one value name one level (`levelName_equal`).

Negative examples: the name of a level is not a name below that level
(`levelName_not_below_self`); without the bound a parameter has no name below a closed level
(`levelName_param_not_typed`); a type of names is not a universe (`names_not_universe`).

Scope: the rules of the heads and their annotated package without declarations. Functions on
the level names are in `LevelFamilies`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace LevelNames

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open Presentation.TypedEquality.Annotated.TowerControls (P₀)
open Mettapedia.TypeTheory.UniverseLevel
open LevelBounds (LeUnder EqUnder Admissible leUnder_subst eqUnder_subst unbounded
  valid_unbounded)
open LevelTower (oneBound oneBound_zero)

/-- **The heads of the tower with level names**: the heads of the tower, the type of the names
of the levels below a level expression, and the name of a level expression. -/
inductive Head (L : Type) where
  | tower : LevelTower.Head L → Head L
  | names : LevelExpr L → Head L
  | name : LevelExpr L → Head L

variable {L : Type}

section Terms

variable {n : Nat}

/-- The universe at a level expression. -/
abbrev universeAt (e : LevelExpr L) : CTm (Head L) n := .head (.tower (.sort e))

/-- The universe at a closed level. -/
abbrev CU (d : L) : CTm (Head L) n := universeAt (.const d)

/-- The type of the names of the levels below a level expression. -/
abbrev levelsBelow (b : LevelExpr L) : CTm (Head L) n := .head (.names b)

/-- The name of a level expression. -/
abbrev levelName (e : LevelExpr L) : CTm (Head L) n := .head (.name e)

end Terms

/-! ## The rules -/

/-- The universes are those of the tower. -/
inductive IsUniverse : Head L → Prop where
  | tower {u : LevelTower.Head L} : LevelTower.IsUniverse u → IsUniverse (.tower u)

/-- The type formers are formed at the universes of the tower. -/
inductive Join : Head L → Head L → Head L → Prop where
  | tower {u v w : LevelTower.Head L} :
      LevelTower.Join u v w → Join (.tower u) (.tower v) (.tower w)

/-- Substitute level expressions for the level parameters of a head. -/
def substLevelsHead (σ : Nat → LevelExpr L) : Head L → Head L
  | .tower h => .tower (LevelTower.substLevelsHead σ h)
  | .names b => .names (b.subst σ)
  | .name e => .name (e.subst σ)

/-- Substituting the parameters for themselves changes no head. -/
theorem substLevelsHead_param (h : Head L) : substLevelsHead LevelExpr.param h = h := by
  cases h with
  | tower t =>
    cases t with
    | legacyGround => rfl
    | sort e => exact congrArg (fun e => Head.tower (.sort e)) (LevelExpr.subst_param e)
  | names b => exact congrArg Head.names (LevelExpr.subst_param b)
  | name e => exact congrArg Head.name (LevelExpr.subst_param e)

/-- Level substitutions compose. -/
theorem substLevelsHead_comp (τ σ : Nat → LevelExpr L) (h : Head L) :
    substLevelsHead τ (substLevelsHead σ h) =
      substLevelsHead (fun i => (σ i).subst τ) h := by
  cases h with
  | tower t =>
    cases t with
    | legacyGround => rfl
    | sort e => exact congrArg (fun e => Head.tower (.sort e)) (LevelExpr.subst_subst τ σ e)
  | names b => exact congrArg Head.names (LevelExpr.subst_subst τ σ b)
  | name e => exact congrArg Head.name (LevelExpr.subst_subst τ σ e)

variable [LevelOrder L]

/-- Replace every level expression of a head by its value at a valuation of the level
parameters. -/
def evalHead (ν : Nat → L) : Head L → Head L
  | .tower .legacyGround => .tower .legacyGround
  | .tower (.sort e) => .tower (.sort (.const (e.eval ν)))
  | .names b => .names (.const (b.eval ν))
  | .name e => .name (.const (e.eval ν))

/-- Evaluating after a level substitution is evaluating at the values of the substituted
expressions. -/
theorem evalHead_substLevelsHead (ν : Nat → L) (σ : Nat → LevelExpr L) (h : Head L) :
    evalHead ν (substLevelsHead σ h) = evalHead (fun i => (σ i).eval ν) h := by
  cases h with
  | tower t =>
    cases t with
    | legacyGround => rfl
    | sort e =>
      exact congrArg (fun d => Head.tower (.sort (.const d))) (LevelExpr.eval_subst ν σ e)
  | names b => exact congrArg (fun d => Head.names (.const d)) (LevelExpr.eval_subst ν σ b)
  | name e => exact congrArg (fun d => Head.name (.const d)) (LevelExpr.eval_subst ν σ e)

/-- **The typing of the heads** under bounds on the level parameters: the tower's, the type of
the names below a level in the universe at that level, and the name of a level among the names
below every level strictly above it. -/
inductive HeadTyping (Δ : LevelBounds L) : Head L → Head L → Prop where
  | tower {h u : LevelTower.Head L} :
      LevelTower.HeadTyping h u → HeadTyping Δ (.tower h) (.tower u)
  | names (b : LevelExpr L) : HeadTyping Δ (.names b) (.tower (.sort b))
  | name {e b : LevelExpr L} : LeUnder Δ (.succ e) b → HeadTyping Δ (.name e) (.names b)

/-- Cumulativity under the bounds: of the universes, and of the types of names. -/
def Cumulative (Δ : LevelBounds L) : Head L → Head L → Prop
  | .tower u, .tower v => LevelTower.CumulativeUnder Δ u v
  | .names b, .names b' => LeUnder Δ b b'
  | _, _ => False

/-- Equality of heads under the bounds: of the heads of the tower, and of the types of names
and of the names with equal level expressions. -/
def HeadEq (Δ : LevelBounds L) : Head L → Head L → Prop
  | .tower h, .tower h' => LevelTower.HeadEqUnder Δ h h'
  | .names b, .names b' => EqUnder Δ b b'
  | .name e, .name e' => EqUnder Δ e e'
  | _, _ => False

/-- **The rules of the tower with level names**, under bounds on the level parameters. -/
def baseRules (Δ : LevelBounds L) : Rules (Head L) where
  headTyping := HeadTyping Δ
  isUniverse := IsUniverse
  join := Join
  cumulative := Cumulative Δ
  headEq := HeadEq Δ

/-- The annotated package of the tower with level names and no declaration. -/
def bare (Δ : LevelBounds L) : ChurchRules (baseRules Δ) :=
  ChurchRules.empty (baseRules Δ) (fun _ => rfl)

/-! ## Stability under level substitution -/

section Substitution

variable {Δ Δ' : LevelBounds L} {σ : Nat → LevelExpr L}

/-- The typing of heads is stable under admissible level substitutions. -/
theorem HeadTyping.substLevels (admissible : Admissible Δ' Δ σ) {h u : Head L}
    (typing : HeadTyping Δ h u) :
    HeadTyping Δ' (substLevelsHead σ h) (substLevelsHead σ u) := by
  cases typing with
  | tower known =>
    cases known with
    | legacyGround => exact .tower .legacyGround
    | sort level => exact .tower (.sort _)
  | names b => exact .names _
  | name below => exact .name (leUnder_subst below admissible)

omit [LevelOrder L] in
/-- Universes are stable under level substitution. -/
theorem IsUniverse.substLevels {u : Head L} (isUniverse : IsUniverse u) :
    IsUniverse (substLevelsHead σ u) := by
  cases isUniverse with
  | tower known =>
    cases known with
    | sort level => exact .tower (.sort _)

omit [LevelOrder L] in
/-- The formation levels are stable under level substitution. -/
theorem Join.substLevels {u v w : Head L} (joined : Join u v w) :
    Join (substLevelsHead σ u) (substLevelsHead σ v) (substLevelsHead σ w) := by
  cases joined with
  | tower known =>
    cases known with
    | sorts left right => exact .tower (.sorts _ _)

/-- Cumulativity is stable under admissible level substitutions. -/
theorem Cumulative.substLevels (admissible : Admissible Δ' Δ σ) {u v : Head L}
    (below : Cumulative Δ u v) :
    Cumulative Δ' (substLevelsHead σ u) (substLevelsHead σ v) := by
  cases u with
  | tower s =>
    cases v with
    | tower t =>
      cases s with
      | legacyGround => exact below.elim
      | sort left =>
        cases t with
        | legacyGround => exact below.elim
        | sort right => exact leUnder_subst below admissible
    | names _ => exact below.elim
    | name _ => exact below.elim
  | names b =>
    cases v with
    | tower _ => exact below.elim
    | names b' => exact leUnder_subst below admissible
    | name _ => exact below.elim
  | name _ => exact below.elim

/-- Equality of heads is stable under admissible level substitutions. -/
theorem HeadEq.substLevels (admissible : Admissible Δ' Δ σ) {h h' : Head L}
    (same : HeadEq Δ h h') : HeadEq Δ' (substLevelsHead σ h) (substLevelsHead σ h') := by
  cases h with
  | tower s =>
    cases h' with
    | tower t =>
      cases s with
      | legacyGround =>
        cases t with
        | legacyGround => trivial
        | sort _ => exact same.elim
      | sort left =>
        cases t with
        | legacyGround => exact same.elim
        | sort right => exact eqUnder_subst same admissible
    | names _ => exact same.elim
    | name _ => exact same.elim
  | names b =>
    cases h' with
    | tower _ => exact same.elim
    | names b' => exact eqUnder_subst same admissible
    | name _ => exact same.elim
  | name e =>
    cases h' with
    | tower _ => exact same.elim
    | names _ => exact same.elim
    | name e' => exact eqUnder_subst same admissible

end Substitution

/-! ## Stronger bounds prove more -/

section Monotone

variable {Δ Δ' : LevelBounds L}

/-- An order of levels under bounds holds under every stronger bounds. -/
theorem leUnder_mono (stronger : ∀ ν : Nat → L, Δ'.Valid ν → Δ.Valid ν) {e₁ e₂ : LevelExpr L}
    (below : LeUnder Δ e₁ e₂) : LeUnder Δ' e₁ e₂ :=
  fun ν valid => below ν (stronger ν valid)

/-- An equality of levels under bounds holds under every stronger bounds. -/
theorem eqUnder_mono (stronger : ∀ ν : Nat → L, Δ'.Valid ν → Δ.Valid ν) {e₁ e₂ : LevelExpr L}
    (same : EqUnder Δ e₁ e₂) : EqUnder Δ' e₁ e₂ :=
  fun ν valid => same ν (stronger ν valid)

/-- The typing of heads holds under every stronger bounds. -/
theorem HeadTyping.mono (stronger : ∀ ν : Nat → L, Δ'.Valid ν → Δ.Valid ν) {h u : Head L}
    (typing : HeadTyping Δ h u) : HeadTyping Δ' h u := by
  cases typing with
  | tower known => exact .tower known
  | names b => exact .names b
  | name below => exact .name (leUnder_mono stronger below)

/-- Cumulativity holds under every stronger bounds. -/
theorem Cumulative.mono (stronger : ∀ ν : Nat → L, Δ'.Valid ν → Δ.Valid ν) {u v : Head L}
    (below : Cumulative Δ u v) : Cumulative Δ' u v := by
  cases u with
  | tower s =>
    cases v with
    | tower t =>
      cases s with
      | legacyGround => exact below.elim
      | sort left =>
        cases t with
        | legacyGround => exact below.elim
        | sort right => exact leUnder_mono stronger below
    | names _ => exact below.elim
    | name _ => exact below.elim
  | names b =>
    cases v with
    | tower _ => exact below.elim
    | names b' => exact leUnder_mono stronger below
    | name _ => exact below.elim
  | name _ => exact below.elim

/-- Equality of heads holds under every stronger bounds. -/
theorem HeadEq.mono (stronger : ∀ ν : Nat → L, Δ'.Valid ν → Δ.Valid ν) {h h' : Head L}
    (same : HeadEq Δ h h') : HeadEq Δ' h h' := by
  cases h with
  | tower s =>
    cases h' with
    | tower t =>
      cases s with
      | legacyGround =>
        cases t with
        | legacyGround => trivial
        | sort _ => exact same.elim
      | sort left =>
        cases t with
        | legacyGround => exact same.elim
        | sort right => exact eqUnder_mono stronger same
    | names _ => exact same.elim
    | name _ => exact same.elim
  | names b =>
    cases h' with
    | tower _ => exact same.elim
    | names b' => exact eqUnder_mono stronger same
    | name _ => exact same.elim
  | name e =>
    cases h' with
    | tower _ => exact same.elim
    | names _ => exact same.elim
    | name e' => exact eqUnder_mono stronger same

end Monotone

/-! ## The tower inside the tower with level names -/

/-- **The annotated tower with bounded level parameters is contained in the tower with level
names**, along the inclusion of heads: every derivation of the tower is a derivation here. -/
theorem tower_morphism (Δ : LevelBounds L) :
    (LevelTower.boundedChurch (P₀ (L := L)) Δ).Morphism (bare Δ) Head.tower where
  headTyping := fun typing => .tower typing
  isUniverse := fun isUniverse => .tower isUniverse
  join := fun joined => .tower joined
  cumulative := fun below => below
  headEq := fun same => same
  constantType := fun {_ T} (declared : (none : Option (CTm (LevelTower.Head L) 0)) = some T) =>
    nomatch declared
  computation := fun step => step.elim
  requires := fun step _ => step.elim

/-- **The identity on the universe at a level expression**, a derivation of the tower read
in the tower with level names: `λ (A : U_e). λ (a : A). a` has type `Π (A : U_e). A → A`. -/
theorem identity_typed (Δ : LevelBounds L) (e : LevelExpr L) :
    CDerivable (bare Δ)
      (.typing .nil (.lam (universeAt e) (.lam (.var 0) (.var 0)))
        (.pi (universeAt e) (.pi (.var 0) (.var 1)))) :=
  (LevelTower.identity_typed (P := LevelTower.boundedChurch (P₀ (L := L)) Δ)
    (LevelTower.overTower_rules.toTowerFormation.bounded Δ) e).mapHead (tower_morphism Δ)

/-! ## Typings of the names -/

section Typings

variable {Δ : LevelBounds L} {n : Nat} {Γ : CCtx (Head L) n}

/-- The universe at a level expression is a member of the universe at its successor. -/
theorem universeAt_typed (e : LevelExpr L) :
    CDerivable (bare Δ) (.typing Γ (universeAt e) (universeAt (.succ e))) :=
  .headType (.tower (.sort e))

/-- The universe at a level strictly below another is a member of the universe at that
level. -/
theorem universeAt_mem {e e' : LevelExpr L} (below : LeUnder Δ (.succ e) e') :
    CDerivable (bare Δ) (.typing Γ (universeAt e) (universeAt e')) :=
  .sub (universeAt_typed e) (.subUniv below)

/-- **The type of the names of the levels below a level is a type at that level.** -/
theorem levelsBelow_typed (b : LevelExpr L) :
    CDerivable (bare Δ) (.typing Γ (levelsBelow b) (universeAt b)) :=
  .headType (.names b)

/-- **The name of a level is a name below every level strictly above it.** -/
theorem levelName_typed {e b : LevelExpr L} (below : LeUnder Δ (.succ e) b) :
    CDerivable (bare Δ) (.typing Γ (levelName e) (levelsBelow b)) :=
  .headType (.name below)

/-- **The names below a level are names below every greater level.** -/
theorem levelsBelow_sub {b b' : LevelExpr L} (below : LeUnder Δ b b') :
    CDerivable (bare Δ) (.sub Γ (levelsBelow b) (levelsBelow b')) :=
  .subUniv below

/-- **Two level expressions with one value name one level.** -/
theorem levelName_equal {e e' b : LevelExpr L} (same : EqUnder Δ e e')
    (below : LeUnder Δ (.succ e) b) :
    CDerivable (bare Δ) (.equality Γ (levelName e) (levelName e') (levelsBelow b)) :=
  .headEq same (levelName_typed below)
    (levelName_typed fun ν valid => by
      have known := below ν valid
      rw [LevelExpr.eval, same ν valid] at known
      exact known)

/-- The name of a closed level below a closed bound. -/
theorem levelName_const_typed {d c : L} (below : d < c) :
    CDerivable (bare Δ) (.typing Γ (levelName (.const d)) (levelsBelow (.const c))) :=
  levelName_typed fun _ _ => LevelOrder.succ_le_of_lt below

/-- **The name of a bounded level parameter is a name below its bound.** -/
theorem levelName_param_typed (c : L) :
    CDerivable (bare (oneBound c))
      (.typing Γ (levelName (.param 0)) (levelsBelow (.const c))) :=
  levelName_typed (LevelBounds.succ_le_of_lt_bound (oneBound_zero c))

/-- **Below a bound closed under the successor, the successor of a bounded level parameter has
a name below the bound.** -/
theorem levelName_succ_param_typed {c : L} (limit : ∀ d, d < c → LevelOrder.succ d < c) :
    CDerivable (bare (oneBound c))
      (.typing Γ (levelName (.succ (.param 0))) (levelsBelow (.const c))) :=
  levelName_typed fun ν valid =>
    LevelOrder.succ_le_of_lt (limit (ν 0) (valid 0 c (oneBound_zero c)))

end Typings

/-! ## Negative examples -/

/-- **The name of a level is not a name below that level.** -/
theorem levelName_not_below_self (c : L) :
    ¬ HeadTyping (unbounded L) (.name (.const c)) (.names (.const c)) := by
  intro typing
  cases typing with
  | name below =>
    exact absurd (below (fun _ => c) (valid_unbounded _))
      (not_le_of_gt (LevelOrder.lt_succ c))

/-- **Without its bound a level parameter has no name below a closed level.** -/
theorem levelName_param_not_typed (c : L) :
    ¬ HeadTyping (unbounded L) (.name (.param 0)) (.names (.const c)) := by
  intro typing
  cases typing with
  | name below =>
    exact absurd (below (fun _ => c) (valid_unbounded _))
      (not_le_of_gt (LevelOrder.lt_succ c))

omit [LevelOrder L] in
/-- **A type of names is not a universe**: no type former is formed in it. -/
theorem names_not_universe (b : LevelExpr L) : ¬ IsUniverse (Head.names b) := by
  intro isUniverse
  cases isUniverse

end LevelNames
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
