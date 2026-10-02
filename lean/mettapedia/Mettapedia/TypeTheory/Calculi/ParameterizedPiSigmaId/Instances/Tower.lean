import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# The cumulative tower

The presentation with an uninterpreted legacy ground head and explicit predicative
universe levels, over any level order, satisfies every hypothesis of the
normalization model: its levels, evaluated under any valuation, form a level
model; cumulativity is a preorder compatible with head equality whose joins are
least upper bounds; head equality steps preserve typing; and it declares no
constants and no root computations.

So for this presentation, with dependent functions and pairs, identity types
and η for functions and pairs, the consequences hold without hypotheses and at
every level order: injectivity and discrimination of type formers, preservation
of typing under reduction, and soundness of the conversion algorithm. The tower
over the natural numbers is one instance; the tower over the ordinal notations
below ε₀ is another.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel

namespace TowerModel

variable {L : Type} [LevelOrder L]

/-- The level of a head under a valuation of the level parameters. -/
def level (valuation : Nat → L) : LevelTower.Head L → L
  | .legacyGround => LevelOrder.bot
  | .sort l => LevelExpr.eval valuation l

/-- The tower's levels under a valuation form a level model. -/
def levels (valuation : Nat → L) : LevelModel (LevelTower.rules L) L where
  level := level valuation
  successor := by
    intro u hu
    cases hu with
    | sort l => exact ⟨.sort (.succ l), .sort _, .sort l, rfl⟩
  universe_typing := by
    intro u v hu typing
    cases hu with
    | sort l =>
        cases typing with
        | sort _ => exact ⟨.sort _, rfl⟩
  ground_typing := by
    intro h v typing
    cases typing with
    | legacyGround => exact .sort _
    | sort _ => exact .sort _
  cumulative_universe := by
    intro u v c
    cases u with
    | legacyGround => exact c.elim
    | sort l =>
        cases v with
        | legacyGround => exact c.elim
        | sort r => exact ⟨.sort l, .sort r, c valuation⟩
  headEq_level := by
    intro h h' same
    cases h with
    | legacyGround =>
        cases h' with
        | legacyGround => exact ⟨Iff.rfl, rfl⟩
        | sort _ => exact same.elim
    | sort l =>
        cases h' with
        | legacyGround => exact same.elim
        | sort r => exact ⟨⟨fun _ => .sort _, fun _ => .sort _⟩, same valuation⟩
  join_level := by
    intro u v w join
    cases join with
    | sorts l r => exact ⟨.sort _, rfl⟩
  join_exists := by
    intro u v hu hv
    cases hu with
    | sort l =>
        cases hv with
        | sort r => exact ⟨_, .sorts l r⟩
  join_upper := by
    intro u v w join
    cases join with
    | sorts l r =>
        exact ⟨fun ν => le_max_left (LevelExpr.eval ν l) (LevelExpr.eval ν r),
          fun ν => le_max_right (LevelExpr.eval ν l) (LevelExpr.eval ν r)⟩
  cumulative_refl := by
    intro u hu
    cases hu with
    | sort l => exact fun ν => le_refl (LevelExpr.eval ν l)
  headEq_symm := by
    intro h h' same
    cases h with
    | legacyGround =>
        cases h' with
        | legacyGround => trivial
        | sort _ => exact same.elim
    | sort l =>
        cases h' with
        | legacyGround => exact same.elim
        | sort r => exact fun ν => (same ν).symm
  headEq_trans := by
    intro h h' h'' first second
    cases h with
    | legacyGround =>
        cases h' with
        | legacyGround => exact second
        | sort _ => exact first.elim
    | sort l =>
        cases h' with
        | legacyGround => exact first.elim
        | sort m =>
            cases h'' with
            | legacyGround => exact second.elim
            | sort r => exact fun ν => (first ν).trans (second ν)
  universe_decided := by
    intro h
    cases h with
    | legacyGround => exact .inr (by intro hu; cases hu)
    | sort l => exact .inl (.sort l)

/-- The tower declares no constants. -/
def roles : Roles (LevelTower.Head L) := fun _ => .rigid

/-- The tower has no root computations. -/
theorem shape : RootShape (LevelTower.rules L) roles where
  spine := fun step => step.elim
  deterministic := fun step => step.elim

/-- The normalization setting of the tower under a valuation. -/
def setting (valuation : Nat → L) : Setting (LevelTower.Head L) L where
  R := LevelTower.rules L
  roles := roles
  E := declarative (LevelTower.rules L)
  levels := levels valuation
  shape := shape
  constructors := .of_no_inductive fun _ _ role => by cases role

theorem laws (valuation : Nat → L) :
    (setting valuation).E.Laws (setting valuation).R (setting valuation).roles :=
  declarative_laws roles (levels valuation)

theorem constants (valuation : Nat → L) : SemanticConstants (setting valuation) := by
  intro name type u declared
  cases declared

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts (LevelTower.rules L) roles :=
  .ofSemantic (S := setting fun _ => (LevelOrder.bot : L)) (laws _) (constants _)

theorem roots : RootPreserving (LevelTower.rules L) := by
  intro n Γ l r A _ step
  exact step.elim

/-- Head equality steps preserve typing: equal levels are cumulative both ways. -/
theorem heads : HeadPreserving (LevelTower.rules L) := by
  intro n Γ h h' A same typing
  obtain ⟨u, headTyping, le⟩ := Typed.generation typing
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : (LevelTower.rules L).cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelOrder.succ (LevelExpr.eval ν r) ≤ LevelOrder.succ (LevelExpr.eval ν l)
            exact LevelOrder.succ_le_succ (le_of_eq (same ν).symm)
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

/-- Cumulativity of the tower is a preorder compatible with head equality, with
least upper bounds. -/
theorem algebra : CumulativeAlgebra (LevelTower.rules L) where
  trans := by
    intro u v w first second
    cases u with
    | legacyGround => exact first.elim
    | sort l =>
        cases v with
        | legacyGround => exact first.elim
        | sort m =>
            cases w with
            | legacyGround => exact second.elim
            | sort r => exact fun ν => (first ν).trans (second ν)
  same_left := by
    intro u u' v same c
    rcases same with rfl | same
    · exact c
    cases u with
    | legacyGround =>
        cases u' with
        | legacyGround => exact c
        | sort _ => exact same.elim
    | sort l =>
        cases u' with
        | legacyGround => exact same.elim
        | sort m =>
            cases v with
            | legacyGround => exact c.elim
            | sort r => exact fun ν => (same ν).le.trans (c ν)
  same_right := by
    intro u v v' c same
    rcases same with rfl | same
    · exact c
    cases v with
    | legacyGround =>
        cases v' with
        | legacyGround => exact c
        | sort _ => exact same.elim
    | sort m =>
        cases v' with
        | legacyGround => exact same.elim
        | sort r =>
            cases u with
            | legacyGround => exact c.elim
            | sort l => exact fun ν => (c ν).trans (same ν).le
  join_least := by
    intro u v w x join first second
    cases join with
    | sorts l r =>
        cases x with
        | legacyGround => exact first.elim
        | sort m =>
            exact fun ν => max_le (first ν) (second ν)

end TowerModel

/-! ## Consequences for the tower -/

section Consequences

open TowerModel

variable {L : Type} [LevelOrder L] {n : Nat} {Γ : Ctx (LevelTower.Head L) n}

/-- Injectivity of dependent function types in the tower. -/
theorem LevelTower.pi_injective {A A' : Tm (LevelTower.Head L) n}
    {B B' : Tm (LevelTower.Head L) (n + 1)}
    (equal : TypeEq (LevelTower.rules L) Γ (.pi A B) (.pi A' B'))
    (formed : CtxFormed (LevelTower.rules L) Γ) :
    TypeEq (LevelTower.rules L) Γ A A' ∧ TypeEq (LevelTower.rules L) (.snoc Γ A) B B' :=
  TypeEq.pi_injective TowerModel.facts equal formed

/-- Injectivity of dependent pair types in the tower. -/
theorem LevelTower.sigma_injective {A A' : Tm (LevelTower.Head L) n}
    {B B' : Tm (LevelTower.Head L) (n + 1)}
    (equal : TypeEq (LevelTower.rules L) Γ (.sigma A B) (.sigma A' B'))
    (formed : CtxFormed (LevelTower.rules L) Γ) :
    TypeEq (LevelTower.rules L) Γ A A' ∧ TypeEq (LevelTower.rules L) (.snoc Γ A) B B' :=
  TypeEq.sigma_injective TowerModel.facts equal formed

/-- Injectivity of identity types in the tower. -/
theorem LevelTower.id_injective {A A' a a' b b' : Tm (LevelTower.Head L) n}
    (equal : TypeEq (LevelTower.rules L) Γ (.id A a b) (.id A' a' b'))
    (formed : CtxFormed (LevelTower.rules L) Γ) :
    TypeEq (LevelTower.rules L) Γ A A' ∧ Equal (LevelTower.rules L) Γ a a' A ∧
      Equal (LevelTower.rules L) Γ b b' A :=
  TypeEq.id_injective TowerModel.facts equal formed

/-- Injectivity of heads in the tower: equal universes have equal levels under
every valuation. -/
theorem LevelTower.head_injective {h h' : LevelTower.Head L}
    (equal : TypeEq (LevelTower.rules L) Γ (.head h) (.head h'))
    (formed : CtxFormed (LevelTower.rules L) Γ) :
    HeadSame (LevelTower.rules L) h h' :=
  TypeEq.head_injective TowerModel.facts equal formed

/-- Type formers of the tower are distinguished by typed equality. -/
theorem LevelTower.former {A B : Tm (LevelTower.Head L) n}
    (fA : Former (setting fun _ => (LevelOrder.bot : L)) A)
    (fB : Former (setting fun _ => (LevelOrder.bot : L)) B)
    (equal : TypeEq (LevelTower.rules L) Γ A B) (formed : CtxFormed (LevelTower.rules L) Γ) :
    fA.kind = fB.kind :=
  Reducible.former (S := setting fun _ => (LevelOrder.bot : L)) (laws _) (constants _) fA fB
    equal formed

/-- Reduction of the tower preserves typing and is a typed equality. -/
theorem LevelTower.reduces_preserve {t t' T : Tm (LevelTower.Head L) n}
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (red : Reduces (LevelTower.rules L) t t') (typing : Typed (LevelTower.rules L) Γ t T) :
    Typed (LevelTower.rules L) Γ t' T ∧ Equal (LevelTower.rules L) Γ t t' T :=
  Reduces.preserve (S := setting fun _ => (LevelOrder.bot : L)) TowerModel.facts roots heads
    formed red typing

/-- Soundness of the conversion algorithm for the tower. -/
theorem LevelTower.algorithm_sound {st : AlgorithmStatement (LevelTower.Head L)}
    (derivation : Algorithm (LevelTower.rules L) st) :
    AlgorithmSound (setting fun _ => (LevelOrder.bot : L)) st :=
  Algorithm.sound (S := setting fun _ => (LevelOrder.bot : L)) TowerModel.facts roots heads
    algebra derivation

/-- Two terms of a type that the conversion algorithm relates are equal. -/
theorem LevelTower.algorithm_compare_sound {a b T : Tm (LevelTower.Head L) n}
    (derivation : Algorithm (LevelTower.rules L) (.compare Γ a b T))
    (formed : CtxFormed (LevelTower.rules L) Γ)
    (ta : Typed (LevelTower.rules L) Γ a T) (tb : Typed (LevelTower.rules L) Γ b T) :
    Equal (LevelTower.rules L) Γ a b T :=
  LevelTower.algorithm_sound derivation formed ta tb

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
