import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.AlgorithmSoundness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-!
# The cumulative tower

The presentation with an uninterpreted legacy ground head and explicit predicative
universe levels satisfies every hypothesis of the normalization model: its
levels, evaluated under any valuation, form a level model; cumulativity is a
preorder compatible with head equality whose joins are least upper bounds;
head equality steps preserve typing; and it declares no constants and no root
computations.

So for this presentation, with dependent functions and pairs, identity types
and η for functions and pairs, the consequences hold without hypotheses:
injectivity and discrimination of type formers, preservation of typing under
reduction, and soundness of the conversion algorithm.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel

namespace TowerModel

/-- The level of a head under a valuation of the level parameters. -/
def level (valuation : Nat → Nat) : Tower.Head → Nat
  | .legacyGround => 0
  | .sort l => LevelExpr.eval valuation l

/-- The tower's levels under a valuation form a level model. -/
def levels (valuation : Nat → Nat) : LevelModel Tower.rules ℕ where
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
def roles : Roles Tower.Head := fun _ => .rigid

/-- The tower has no root computations. -/
theorem shape : RootShape Tower.rules roles where
  spine := fun step => step.elim
  deterministic := fun step => step.elim

/-- The normalization setting of the tower under a valuation. -/
def setting (valuation : Nat → Nat) : Setting Tower.Head ℕ where
  R := Tower.rules
  roles := roles
  E := declarative Tower.rules
  levels := levels valuation
  shape := shape
  constructors := .of_no_inductive fun _ _ role => by cases role

theorem laws (valuation : Nat → Nat) :
    (setting valuation).E.Laws (setting valuation).R (setting valuation).roles :=
  declarative_laws roles (levels valuation)

theorem constants (valuation : Nat → Nat) : SemanticConstants (setting valuation) := by
  intro name type u declared
  cases declared

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts Tower.rules roles :=
  .ofSemantic (S := setting fun _ => 0) (laws _) (constants _)

theorem roots : RootPreserving Tower.rules := by
  intro n Γ l r A _ step
  exact step.elim

/-- Head equality steps preserve typing: equal levels are cumulative both ways. -/
theorem heads : HeadPreserving Tower.rules := by
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
          have raise : Tower.rules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

/-- Cumulativity of the tower is a preorder compatible with head equality, with
least upper bounds. -/
theorem algebra : CumulativeAlgebra Tower.rules where
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

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- Injectivity of dependent function types in the tower. -/
theorem Tower.pi_injective {A A' : Tm Tower.Head n} {B B' : Tm Tower.Head (n + 1)}
    (equal : TypeEq Tower.rules Γ (.pi A B) (.pi A' B')) (formed : CtxFormed Tower.rules Γ) :
    TypeEq Tower.rules Γ A A' ∧ TypeEq Tower.rules (.snoc Γ A) B B' :=
  TypeEq.pi_injective TowerModel.facts equal formed

/-- Injectivity of dependent pair types in the tower. -/
theorem Tower.sigma_injective {A A' : Tm Tower.Head n} {B B' : Tm Tower.Head (n + 1)}
    (equal : TypeEq Tower.rules Γ (.sigma A B) (.sigma A' B'))
    (formed : CtxFormed Tower.rules Γ) :
    TypeEq Tower.rules Γ A A' ∧ TypeEq Tower.rules (.snoc Γ A) B B' :=
  TypeEq.sigma_injective TowerModel.facts equal formed

/-- Injectivity of identity types in the tower. -/
theorem Tower.id_injective {A A' a a' b b' : Tm Tower.Head n}
    (equal : TypeEq Tower.rules Γ (.id A a b) (.id A' a' b'))
    (formed : CtxFormed Tower.rules Γ) :
    TypeEq Tower.rules Γ A A' ∧ Equal Tower.rules Γ a a' A ∧ Equal Tower.rules Γ b b' A :=
  TypeEq.id_injective TowerModel.facts equal formed

/-- Injectivity of heads in the tower: equal universes have equal levels under
every valuation. -/
theorem Tower.head_injective {h h' : Tower.Head}
    (equal : TypeEq Tower.rules Γ (.head h) (.head h')) (formed : CtxFormed Tower.rules Γ) :
    HeadSame Tower.rules h h' :=
  TypeEq.head_injective TowerModel.facts equal formed

/-- Type formers of the tower are distinguished by typed equality. -/
theorem Tower.former {A B : Tm Tower.Head n} (fA : Former (setting fun _ => 0) A)
    (fB : Former (setting fun _ => 0) B)
    (equal : TypeEq Tower.rules Γ A B) (formed : CtxFormed Tower.rules Γ) :
    fA.kind = fB.kind :=
  Reducible.former (S := setting fun _ => 0) (laws _) (constants _) fA fB equal formed

/-- Reduction of the tower preserves typing and is a typed equality. -/
theorem Tower.reduces_preserve {t t' T : Tm Tower.Head n} (formed : CtxFormed Tower.rules Γ)
    (red : Reduces Tower.rules t t') (typing : Typed Tower.rules Γ t T) :
    Typed Tower.rules Γ t' T ∧ Equal Tower.rules Γ t t' T :=
  Reduces.preserve (S := setting fun _ => 0) TowerModel.facts roots heads formed red typing

/-- Soundness of the conversion algorithm for the tower. -/
theorem Tower.algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm Tower.rules st) : AlgorithmSound (setting fun _ => 0) st :=
  Algorithm.sound (S := setting fun _ => 0) TowerModel.facts roots heads algebra derivation

/-- Two terms of a type that the conversion algorithm relates are equal. -/
theorem Tower.algorithm_compare_sound {a b T : Tm Tower.Head n}
    (derivation : Algorithm Tower.rules (.compare Γ a b T)) (formed : CtxFormed Tower.rules Γ)
    (ta : Typed Tower.rules Γ a T) (tb : Typed Tower.rules Γ b T) :
    Equal Tower.rules Γ a b T :=
  Tower.algorithm_sound derivation formed ta tb

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
