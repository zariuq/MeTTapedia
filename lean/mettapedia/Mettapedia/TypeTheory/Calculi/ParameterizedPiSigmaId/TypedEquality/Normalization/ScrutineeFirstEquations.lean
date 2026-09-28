import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstDefinition

/-!
# The equations of a definition admitted through its scrutinee-first form

A definition `f` by structural recursion on its argument at position `s`,
whose recursive calls may change the arguments before the scrutinee, is
admitted as two constants: its scrutinee-first form `f'`, by structural
recursion on the first argument, and `f` itself, defined by
`f x̄ y z̄ = f' y x̄ z̄`.

* A call of `f` is equal to the call of `f'` on the moved arguments: this is
  the δ-step of `f`.
* At a constructor pattern, `f` is equal to the scrutinee-first right-hand
  side, whose recursive calls are `f'` at the fields: the δ-step of `f`
  followed by the ι-step of `f'`.

So each authored equation holds as a typed equality: its right-hand side's
recursive calls `f ā v z̄`, at changed arguments `ā`, are the scrutinee-first
calls `f' v ā z̄` by the first item.

The telescopes are arbitrary: the entries before the scrutinee may depend on
each other and the later entries on everything before them. Only the typings
the two declarations carry are used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open TelescopeAbstraction (closeType applyClosed applyClosed_subst)

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {S : Setting Head L}

/-- Applying a head along a telescope depends only on its length. -/
theorem applyClosed_ofEntries_irrel (e e₂ : (i : Nat) → Tm Head i) {m : Nat} (n : Nat)
    (σ : Sub Head n m) (t : Tm Head m) :
    applyClosed (ofEntries e n) σ t = applyClosed (ofEntries e₂ n) σ t := by
  rw [applyClosed_eq_appSpine, applyClosed_eq_appSpine, telescopeArgs_ofEntries_ofFn,
    telescopeArgs_ofEntries_ofFn]

section Equations

variable (facts : FormFacts S.R S.roles)
  {e e' : (i : Nat) → Tm Head i} {F : Nat → Tm Head 0} {f f' : DeclName} {s d : Nat}
  {C : Tm Head (s + 1 + d)} {R₁ : Rules Head}
  (defn : DeclaresDefinition S R₁ f (ofEntries e (s + 1 + d)) C (definitionBody F f' s d))
include facts defn

/-- A call of `f` is the call of its scrutinee-first form on the moved
arguments. -/
theorem ScrutineeFirst.call_equal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {σ : Sub Head (s + 1 + d) n}
    (typed : SubstMor S.R (ofEntries e (s + 1 + d)) Γ σ) :
    Equal S.R Γ (applyClosed (ofEntries e (s + 1 + d)) σ (.const f))
      (applyClosed (ofEntries e' (0 + 1 + (s + d))) (fun j => σ (teleMoveBack s d j)) (.const f'))
      (Presentation.subst σ C) := by
  have typing : Typed S.R Γ (applyClosed (ofEntries e (s + 1 + d)) σ (.const f))
      (Presentation.subst σ C) :=
    Typed.telescope_apply typed defn.typing
  have reduct := DeclaresDefinition.rule_preserves facts defn (RulesSub.refl _) formed σ typing
  rw [subst_definitionBody, applyClosed_ofEntries_irrel (fun i => liftClosed (scrutineeFirst F s i)) e'] at reduct
  have step := defn.rule σ
  rw [subst_definitionBody, applyClosed_ofEntries_irrel (fun i => liftClosed (scrutineeFirst F s i)) e'] at step
  exact .root step typing reduct

variable {T : DeclName} {ctors : List (DeclName × List (Field Head))}
  {body' : (k : DeclName) → (fields : List (Field Head)) →
    Tm Head (0 + fields.length + (s + d) + (recPositions fields).length)}
  {R₀ : Rules Head}
  (first : DeclaresRecursion S R₀ f' T ctors e' 0 (s + d) (Presentation.rename (teleMove s d) C)
    body')
  {R₀' R₁' R₂' : Rules Head} {u : Head} {rec : DeclName} {v : Head}
  (ind : DeclaresInductive S R₀' R₁' R₂' T u ctors rec v)
include first ind

/-- The authored equation at a constructor pattern: `f` there is the
scrutinee-first right-hand side, the recursive calls being those of `f'` at
the fields. -/
theorem ScrutineeFirst.equation {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {k : DeclName} {fields : List (Field Head)} (mem : (k, fields) ∈ ctors)
    (σ : Sub Head (s + 1 + d) n) (as : List (Tm Head n)) (has : as.length = fields.length)
    {A : Tm Head n}
    (typing : Typed S.R Γ (applyClosed (ofEntries e (s + 1 + d))
      (replaceScrut s (appSpine (.const k) as) d σ) (.const f)) A) :
    Equal S.R Γ (applyClosed (ofEntries e (s + 1 + d))
        (replaceScrut s (appSpine (.const k) as) d σ) (.const f))
      (Presentation.subst (matchSub 0 fields.length as (s + d) (fun j => σ (teleMoveBack s d j)))
        (Presentation.subst (hypSub f' e' 0 (s + d) fields) (body' k fields))) A := by
  have reduct := DeclaresDefinition.rule_preserves facts defn (RulesSub.refl _) formed _ typing
  rw [subst_definitionBody_replaceScrut, applyClosed_ofEntries_irrel (fun i => liftClosed (scrutineeFirst F s i)) e'] at reduct
  have δ := defn.rule (replaceScrut s (appSpine (.const k) as) d σ)
  rw [subst_definitionBody_replaceScrut, applyClosed_ofEntries_irrel (fun i => liftClosed (scrutineeFirst F s i)) e'] at δ
  have ι := first.rule mem (fun j => σ (teleMoveBack s d j)) as has
  have reduct' := DeclaresRecursion.rule_preserves facts first ind (RulesSub.refl _) formed mem
    (fun j => σ (teleMoveBack s d j)) as has reduct
  exact .trans (.root δ typing reduct) (.root ι reduct reduct')

end Equations

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
