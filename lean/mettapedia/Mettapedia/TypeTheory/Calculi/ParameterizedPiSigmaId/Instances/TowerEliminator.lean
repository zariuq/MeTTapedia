import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Eliminator
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
/-!
# The cumulative tower with the identity eliminator

The tower extended by one declared constant, the based identity eliminator at
two chosen universes, with its linear computation rule. Every hypothesis of
the normalization model holds: the eliminator is semantic, its rule preserves
typing, and the root computation has the required shape. So injectivity,
discrimination, preservation and soundness of the conversion algorithm hold
for this presentation without hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)

namespace TowerEliminatorModel

/-- The eliminator's rule as a root computation: at reflexivity, the method. -/
def computation (J : DeclName) : RootComputation Tower.Head where
  step := fun {n} l r => ∃ a₀ a₁ a₂ a₃ a₄ a₅ : Tm Tower.Head n,
    l = appSpine (.const J) [a₀, a₁, a₂, a₃, a₄, .refl a₅] ∧ r = a₃
  rename := by
    intro n m ρ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
    subst e₁
    exact ⟨Presentation.rename ρ a₀, Presentation.rename ρ a₁, Presentation.rename ρ a₂,
      Presentation.rename ρ a₃, Presentation.rename ρ a₄, Presentation.rename ρ a₅,
      by rw [rename_appSpine]; rfl, by rw [e₂]⟩
  substitute := by
    intro n m σ l r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
    subst e₁
    exact ⟨Presentation.subst σ a₀, Presentation.subst σ a₁, Presentation.subst σ a₂,
      Presentation.subst σ a₃, Presentation.subst σ a₄, Presentation.subst σ a₅,
      by rw [subst_appSpine]; rfl, by rw [e₂]⟩

/-- The tower with the eliminator `J` at universes `u` and `v`. -/
def rules (J : DeclName) (u v : Tower.Head) : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name => if name = J then some (elimType u v) else none
    computation := computation J }

/-- The eliminator computes on its sixth argument; nothing else is declared. -/
def roles (J : DeclName) : Roles Tower.Head := fun name => if name = J then .computes 6 (.split 5 .constructor fun _ => .leaf) else .rigid

theorem shape (J : DeclName) (u v : Tower.Head) : RootShape (rules J u v) (roles J) where
  spine := by
    intro n t r step
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, _⟩ := step
    subst e₁
    exact ⟨J, 6, .split 5 .constructor fun _ => .leaf, [a₀, a₁, a₂, a₃, a₄, .refl a₅],
      by simp [roles], rfl, rfl, InspectTree.accepts_single.mpr ⟨_, rfl, .inl ⟨a₅, rfl⟩⟩⟩
  deterministic := by
    intro n t r r' h₁ h₂
    obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := h₁
    obtain ⟨b₀, b₁, b₂, b₃, b₄, b₅, e₃, e₄⟩ := h₂
    subst e₂ e₄
    rw [e₁] at e₃
    obtain ⟨_, args⟩ := appSpine_const_injective e₃
    simp only [List.cons.injEq] at args
    exact args.2.2.2.1

/-- The tower's level model, for the extended rule package. -/
def levels (J : DeclName) (u v : Tower.Head) (valuation : Nat → Nat) :
    LevelModel (rules J u v) ℕ where
  level := (TowerModel.levels valuation).level
  successor := (TowerModel.levels valuation).successor
  universe_typing := (TowerModel.levels valuation).universe_typing
  ground_typing := (TowerModel.levels valuation).ground_typing
  cumulative_universe := (TowerModel.levels valuation).cumulative_universe
  headEq_level := (TowerModel.levels valuation).headEq_level
  join_level := (TowerModel.levels valuation).join_level
  join_exists := (TowerModel.levels valuation).join_exists
  join_upper := (TowerModel.levels valuation).join_upper
  cumulative_refl := (TowerModel.levels valuation).cumulative_refl
  headEq_symm := (TowerModel.levels valuation).headEq_symm
  headEq_trans := (TowerModel.levels valuation).headEq_trans
  universe_decided := (TowerModel.levels valuation).universe_decided

/-- The normalization setting. -/
def setting (J : DeclName) (u v : Tower.Head) (valuation : Nat → Nat) : Setting Tower.Head ℕ where
  R := rules J u v
  roles := roles J
  E := declarative (rules J u v)
  levels := levels J u v valuation
  shape := shape J u v
  constructors := .of_no_inductive fun name _ role => by
    unfold roles at role
    split at role <;> cases role

theorem laws (J : DeclName) (u v : Tower.Head) (valuation : Nat → Nat) :
    (setting J u v valuation).E.Laws (setting J u v valuation).R (setting J u v valuation).roles :=
  declarative_laws (roles J) (levels J u v valuation)

/-! ## The declared type is typed -/

section Typing

variable (lu lv : LevelExpr)

/-- The eliminator's declared type is typed in the tower, using no constants. -/
theorem elimType_typed : ∃ w, Tower.IsUniverse w ∧
    Typed Tower.rules .nil (elimType (.sort lu) (.sort lv)) (.head w) := by
  let su : Tower.Head := .sort lu
  let sv : Tower.Head := .sort lv
  have hu : Tower.rules.isUniverse su := .sort lu
  -- the carrier
  have tE0 : Typed Tower.rules .nil (.head su) (.head (.sort (.succ lu))) := .headType (.sort lu)
  -- the base point
  have tE1 : Typed Tower.rules (.snoc .nil (.head su)) (.var 0) (.head su) := .var 0
  -- the motive's type
  have tA2 : Typed Tower.rules (.snoc (.snoc .nil (.head su)) (.var 0)) (.var 1) (.head su) :=
    .var 1
  have tIdInner : Typed Tower.rules (.snoc (.snoc (.snoc .nil (.head su)) (.var 0)) (.var 1))
      (.id (.var 2) (.var 1) (.var 0)) (.head su) :=
    .idForm (.var 2) hu (.var 1) (.var 0)
  have tInnerPi := Derivable.piForm tIdInner hu
    (.headType (.sort lv) : Typed Tower.rules (.snoc (.snoc (.snoc (.snoc .nil (.head su)) (.var 0))
      (.var 1)) (.id (.var 2) (.var 1) (.var 0))) (.head sv) (.head (.sort (.succ lv))))
    (.sort _) (.sorts lu (.succ lv))
  have tE2 := Derivable.piForm tA2 hu tInnerPi (.sort _) (.sorts lu (.max lu (.succ lv)))
  -- the method's type
  have tP3 : Typed Tower.rules (.snoc (.snoc (.snoc .nil (.head su)) (.var 0))
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head sv)))) (.var 0)
      (.pi (.var 2) (.pi (.id (.var 3) (.var 2) (.var 0)) (.head sv))) := .var 0
  have tx3 : Typed Tower.rules (.snoc (.snoc (.snoc .nil (.head su)) (.var 0))
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head sv)))) (.var 1) (.var 2) := .var 1
  have tPx : Typed Tower.rules (.snoc (.snoc (.snoc .nil (.head su)) (.var 0))
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head sv)))) (.app (.var 0) (.var 1))
      (.pi (.id (.var 2) (.var 1) (.var 1)) (.head sv)) := .appElim tP3 tx3
  have tE3 : Typed Tower.rules (.snoc (.snoc (.snoc .nil (.head su)) (.var 0))
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head sv))))
      (.app (.app (.var 0) (.var 1)) (.refl (.var 1))) (.head sv) :=
    .appElim tPx (.reflIntro tx3)
  -- the target point
  have tE4 : Typed Tower.rules (.snoc (.snoc (.snoc (.snoc .nil (.head su)) (.var 0))
      (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) (.head sv))))
      (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))) (.var 3) (.head su) := .var 3
  -- the path's type
  have tE5 : Typed Tower.rules (elimPrefix su sv) (.id (.var 4) (.var 3) (.var 0)) (.head su) :=
    .idForm (.var 4) hu (.var 3) (.var 0)
  -- the result type
  have tP6 : Typed Tower.rules (elimTelescope su sv) (.var 3)
      (.pi (.var 5) (.pi (.id (.var 6) (.var 5) (.var 0)) (.head sv))) := .var 3
  have tPy : Typed Tower.rules (elimTelescope su sv) (.app (.var 3) (.var 1))
      (.pi (.id (.var 5) (.var 4) (.var 1)) (.head sv)) := .appElim tP6 (.var 1)
  have tBody : Typed Tower.rules (elimTelescope su sv) elimBody (.head sv) :=
    .appElim tPy (.var 0)
  -- closing the telescope
  have t6 := Derivable.piForm tE5 hu tBody (.sort lv) (.sorts lu lv)
  have t5 := Derivable.piForm tE4 hu t6 (.sort _) (.sorts lu (.max lu lv))
  have t4 := Derivable.piForm tE3 (.sort lv) t5 (.sort _) (.sorts lv _)
  have t3 := Derivable.piForm tE2 (.sort _) t4 (.sort _) (.sorts _ _)
  have t2 := Derivable.piForm tE1 hu t3 (.sort _) (.sorts lu _)
  have t1 := Derivable.piForm tE0 (.sort _) t2 (.sort _) (.sorts _ _)
  exact ⟨_, .sort _, t1⟩

end Typing

/-! ## The hypotheses of the model -/

section Hypotheses

variable (J : DeclName) (lu lv : LevelExpr) (valuation : Nat → Nat)

theorem constantFree_sub :
    RulesSub Tower.rules (constantFreeRules (rules J (.sort lu) (.sort lv))) :=
  ⟨id, id, id, id, id, id, id⟩

/-- The package declares the eliminator. -/
theorem declares :
    DeclaresEliminator (setting J (.sort lu) (.sort lv) valuation) J (.sort lu) (.sort lv) where
  role := by simp [setting, roles]
  declared := by simp [setting, rules]
  rule := fun {_ a₀ a₁ a₂ a₃ a₄ a₅} => ⟨a₀, a₁, a₂, a₃, a₄, a₅, rfl, rfl⟩
  hu := .sort lu
  hv := .sort lv
  typed := by
    obtain ⟨w, hw, typed⟩ := elimType_typed lu lv
    exact ⟨w, hw, Derivable.mono (constantFree_sub J lu lv) typed⟩

/-- The only declared constant, the eliminator, is semantic. -/
theorem constants : SemanticConstants (setting J (.sort lu) (.sort lv) valuation) := by
  intro name type u declared _ _
  by_cases h : name = J
  · subst h
    have e : type = elimType (.sort lu) (.sort lv) := by
      simpa [setting, rules] using declared.symm
    subst e
    exact (declares name lu lv valuation).semantic (laws name _ _ valuation)
  · simp [setting, rules, h] at declared

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts (rules J (.sort lu) (.sort lv)) (roles J) :=
  .ofSemantic (S := setting J (.sort lu) (.sort lv) fun _ => 0) (laws J _ _ _) (constants J lu lv _)

/-- The eliminator's rule preserves typing. -/
theorem roots : RootPreserving (rules J (.sort lu) (.sort lv)) := by
  intro n Γ l r A formed step typing
  obtain ⟨a₀, a₁, a₂, a₃, a₄, a₅, e₁, e₂⟩ := step
  subst e₁ e₂
  exact (declares J lu lv fun _ => 0).rule_preserves (TowerEliminatorModel.facts J lu lv) (RulesSub.refl _) formed
      typing

/-- Head equality steps preserve typing. -/
theorem heads : HeadPreserving (rules J (.sort lu) (.sort lv)) := by
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
          have raise : (rules J (.sort lu) (.sort lv)).cumulative (.sort (.succ r))
              (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem algebra : CumulativeAlgebra (rules J (.sort lu) (.sort lv)) where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

end Hypotheses

end TowerEliminatorModel

/-! ## Consequences for the tower with the eliminator -/

section Consequences

open TowerEliminatorModel

variable {J : DeclName} {lu lv : LevelExpr} {n : Nat}
  {Γ : Ctx Tower.Head n}

/-- The eliminator is a semantic constant of the model. -/
theorem TowerEliminator.semantic :
    SemanticConstant (setting J (.sort lu) (.sort lv) fun _ => 0) J
      (elimType (.sort lu) (.sort lv)) :=
  (declares J lu lv fun _ => 0).semantic (laws J _ _ fun _ => 0)

/-- Injectivity of dependent function types. -/
theorem TowerEliminator.pi_injective {A A' : Tm Tower.Head n} {B B' : Tm Tower.Head (n + 1)}
    (equal : TypeEq (rules J (.sort lu) (.sort lv)) Γ (.pi A B) (.pi A' B'))
    (formed : CtxFormed (rules J (.sort lu) (.sort lv)) Γ) :
    TypeEq (rules J (.sort lu) (.sort lv)) Γ A A' ∧
      TypeEq (rules J (.sort lu) (.sort lv)) (.snoc Γ A) B B' :=
  TypeEq.pi_injective (TowerEliminatorModel.facts J lu lv) equal formed

/-- Injectivity of identity types. -/
theorem TowerEliminator.id_injective {A A' a a' b b' : Tm Tower.Head n}
    (equal : TypeEq (rules J (.sort lu) (.sort lv)) Γ (.id A a b) (.id A' a' b'))
    (formed : CtxFormed (rules J (.sort lu) (.sort lv)) Γ) :
    TypeEq (rules J (.sort lu) (.sort lv)) Γ A A' ∧
      Equal (rules J (.sort lu) (.sort lv)) Γ a a' A ∧
      Equal (rules J (.sort lu) (.sort lv)) Γ b b' A :=
  TypeEq.id_injective (TowerEliminatorModel.facts J lu lv) equal formed

/-- Reduction preserves typing, including the eliminator's computation. -/
theorem TowerEliminator.reduces_preserve {t t' T : Tm Tower.Head n}
    (formed : CtxFormed (rules J (.sort lu) (.sort lv)) Γ)
    (red : Reduces (rules J (.sort lu) (.sort lv)) t t')
    (typing : Typed (rules J (.sort lu) (.sort lv)) Γ t T) :
    Typed (rules J (.sort lu) (.sort lv)) Γ t' T ∧ Equal (rules J (.sort lu) (.sort lv)) Γ t t' T :=
  Reduces.preserve (S := setting J (.sort lu) (.sort lv) fun _ => 0) (TowerEliminatorModel.facts J
      lu lv) (roots J lu lv) (heads J lu lv) formed red typing

/-- Soundness of the conversion algorithm. -/
theorem TowerEliminator.algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm (rules J (.sort lu) (.sort lv)) st) :
    AlgorithmSound (setting J (.sort lu) (.sort lv) fun _ => 0) st :=
  Algorithm.sound (S := setting J (.sort lu) (.sort lv) fun _ => 0) (TowerEliminatorModel.facts J
      lu lv) (roots J lu lv) (heads J lu lv) (algebra J lu lv) derivation

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
