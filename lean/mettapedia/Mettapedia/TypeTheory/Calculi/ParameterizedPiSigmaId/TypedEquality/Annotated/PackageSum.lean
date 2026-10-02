import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.LogicalRelationFundamental
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Schemas

/-!
# The sum of two annotated packages

Two packages over one language of heads are put together (`ChurchRules.sum`): the universe
rules of the first, the declarations of the first and then those of the second, and the root
steps of both, each with the premises its own package requires of it.

The first package is contained in the sum (`ChurchRulesSub.sum_left`). The second is contained
in it when its universe rules are among the first's and the first declares none of its names
(`ChurchRulesSub.sum_right`). Every derivation of either package is then a derivation of the
sum (`CDerivable.mono`). The universe rules of the sum are the first's, so a level model of
the first is one of the sum (`LevelModel.sum`).

Positive example: a name only the second package declares is declared in the sum with the
second's type (`sumDecls_right`). Negative example: a name both declare has the first's type
in the sum, so a second package that redeclares a name is not contained
(`sumDecls_shadowed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-! ## Declarations -/

/-- The declarations of two packages together: those of the first, and those of the second at
the names the first does not declare. -/
def sumDecls {α : Type} (first second : DeclName → Option α) : DeclName → Option α :=
  fun c =>
    match first c with
    | some T => some T
    | none => second c

theorem sumDecls_left {α : Type} {first second : DeclName → Option α} {c : DeclName} {T : α}
    (declared : first c = some T) : sumDecls first second c = some T := by
  unfold sumDecls
  rw [declared]

theorem sumDecls_right {α : Type} {first second : DeclName → Option α} {c : DeclName}
    (fresh : first c = none) : sumDecls first second c = second c := by
  unfold sumDecls
  rw [fresh]

/-- A name both declare has the first's declaration. -/
theorem sumDecls_shadowed {α : Type} {first second : DeclName → Option α} {c : DeclName}
    {T T' : α} (declared : first c = some T) (different : T ≠ T') :
    sumDecls first second c ≠ some T' := by
  rw [sumDecls_left declared]
  exact fun same => different (Option.some.inj same)

/-! ## The sum -/

/-- The rules of two packages together: the universe rules of the first, the declarations of
both and the root steps of both. -/
def Rules.sum (R₁ R₂ : Rules Head) : Rules Head :=
  { R₁ with
    constantType := sumDecls R₁.constantType R₂.constantType
    computation := Normalization.RootComputation.union R₁.computation R₂.computation }

/-- The universe rules of a sum are those of its first package, and so is a level model. -/
def LevelModel.sum {L : Type} [UniverseLevel.LevelOrder L] {R₁ : Rules Head}
    (levels : Normalization.LevelModel R₁ L) (R₂ : Rules Head) :
    Normalization.LevelModel (Rules.sum R₁ R₂) L where
  level := levels.level
  successor := levels.successor
  universe_typing := levels.universe_typing
  ground_typing := levels.ground_typing
  cumulative_universe := levels.cumulative_universe
  headEq_level := levels.headEq_level
  join_level := levels.join_level
  join_exists := levels.join_exists
  join_upper := levels.join_upper
  cumulative_refl := levels.cumulative_refl
  headEq_symm := levels.headEq_symm
  headEq_trans := levels.headEq_trans
  universe_decided := levels.universe_decided

/-- The root computations of two annotated packages together. A step requires the premises
that the package it is a step of requires of it. -/
def CRootComputation.sum (c₁ c₂ : CRootComputation Head) : CRootComputation Head where
  step := fun l r => c₁.step l r ∨ c₂.step l r
  rename := by
    intro n m ρ l r step
    exact step.elim (fun h => .inl (c₁.rename ρ h)) (fun h => .inr (c₂.rename ρ h))
  substitute := by
    intro n m σ l r step
    exact step.elim (fun h => .inl (c₁.substitute σ h)) (fun h => .inr (c₂.substitute σ h))
  requires := fun l r premises =>
    (c₁.step l r ∧ c₁.requires l r premises) ∨ (c₂.step l r ∧ c₂.requires l r premises)
  requires_rename := by
    intro n m ρ l r premises required
    exact required.elim
      (fun h => .inl ⟨c₁.rename ρ h.1, c₁.requires_rename ρ h.2⟩)
      (fun h => .inr ⟨c₂.rename ρ h.1, c₂.requires_rename ρ h.2⟩)
  requires_substitute := by
    intro n m σ l r premises required
    exact required.elim
      (fun h => .inl ⟨c₁.substitute σ h.1, c₁.requires_substitute σ h.2⟩)
      (fun h => .inr ⟨c₂.substitute σ h.1, c₂.requires_substitute σ h.2⟩)

/-- **The sum of two annotated packages.** -/
def ChurchRules.sum {R₁ R₂ : Rules Head} (P₁ : ChurchRules R₁) (P₂ : ChurchRules R₂) :
    ChurchRules (Rules.sum R₁ R₂) where
  constantType := sumDecls P₁.constantType P₂.constantType
  computation := CRootComputation.sum P₁.computation P₂.computation
  erase_constantType := by
    intro c
    show (sumDecls P₁.constantType P₂.constantType c).map CTm.erase =
      sumDecls R₁.constantType R₂.constantType c
    have first := P₁.erase_constantType c
    cases found : P₁.constantType c with
    | none =>
      rw [found] at first
      rw [sumDecls_right found, sumDecls_right first.symm]
      exact P₂.erase_constantType c
    | some T =>
      rw [found] at first
      rw [sumDecls_left found, sumDecls_left first.symm]
      rfl
  erase_step := by
    intro n l r step
    exact step.elim (fun h => Or.inl (P₁.erase_step h)) (fun h => Or.inr (P₂.erase_step h))

variable {R₁ R₂ : Rules Head}

/-- **The first package is contained in the sum.** -/
theorem ChurchRulesSub.sum_left (P₁ : ChurchRules R₁) (P₂ : ChurchRules R₂) :
    ChurchRulesSub P₁ (P₁.sum P₂) where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  constantType := fun known => sumDecls_left known
  computation := .inl
  requires := fun step required => ⟨_, .inl ⟨step, required⟩, fun _ member => member⟩

/-- **The second package is contained in the sum** when its universe rules are among the
first's and the first declares none of its names. -/
theorem ChurchRulesSub.sum_right (P₁ : ChurchRules R₁) (P₂ : ChurchRules R₂)
    (headTyping : ∀ {h u : Head}, R₂.headTyping h u → R₁.headTyping h u)
    (isUniverse : ∀ {u : Head}, R₂.isUniverse u → R₁.isUniverse u)
    (join : ∀ {u v w : Head}, R₂.join u v w → R₁.join u v w)
    (cumulative : ∀ {u v : Head}, R₂.cumulative u v → R₁.cumulative u v)
    (headEq : ∀ {h h' : Head}, R₂.headEq h h' → R₁.headEq h h')
    (fresh : ∀ {c : DeclName} {D : CTm Head 0}, P₂.constantType c = some D →
      P₁.constantType c = none) :
    ChurchRulesSub P₂ (P₁.sum P₂) where
  headTyping := headTyping
  isUniverse := isUniverse
  join := join
  cumulative := cumulative
  headEq := headEq
  constantType := fun known => (sumDecls_right (fresh known)).trans known
  computation := .inr
  requires := fun step required => ⟨_, .inr ⟨step, required⟩, fun _ member => member⟩

/-- Every derivation of the first package is a derivation of the sum. -/
theorem CDerivable.sum_left {P₁ : ChurchRules R₁} (P₂ : ChurchRules R₂) {s : CStatement Head}
    (derivation : CDerivable P₁ s) : CDerivable (P₁.sum P₂) s :=
  derivation.mono (ChurchRulesSub.sum_left P₁ P₂)

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
