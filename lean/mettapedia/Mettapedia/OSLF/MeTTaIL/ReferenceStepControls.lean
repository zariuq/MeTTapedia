import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution
import Mettapedia.OSLF.MeTTaIL.ReferenceStepEquations

/-!
# Controls: the reference step relation

- **In place.** `Lam (λ. x) ~> Lam (λ. y) if x ~> y` steps a body as an open term: `λx. (λy. y) x`
  steps to `λx. x`, as in the least contextual relation.
- **Explicit binders.** The same rule with the body under a premise-local binder also steps in the
  reference relation. The least contextual relation refuses premises with binders.
- **Quantified premises.** `AllOk {xs…} ~> Ok if ∀ x ∈ xs, ok x` fires on a bag of `A`s and `B`s, and
  not on a bag holding `Bad`. The least contextual relation never fires it.
- **Scopes.** `Lam (λ. x) ~> Lam (λ. Lam (λ. y)) if x ~> y` places the stepped body one binder deeper.
  The reference relation lifts it, so the body's variable still names the outer binder; the least
  contextual relation leaves it unshifted, and the inner binder captures it.
- **Equations under binders.** `Shift x = Lam (λ. x)` moves its metavariable under a binder. Its
  instance at `Shift #0` is `Lam (λ. #1)` in the reference relation; the canonical plain instantiation
  gives `Lam (λ. #0)`, captured. The equation is not aligned.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ReferenceStepControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep

def termSort : TypeExpr := .base "Term"

def lam (body : Pattern) : Pattern := .apply "Lam" [.lambda none body]
def app (function argument : Pattern) : Pattern := .apply "App" [function, argument]
def ok : Pattern := .apply "Ok" []

def beta : RewriteRule :=
  { name := "Beta", typeContext := [], premises := [],
    left := app (lam (.fvar "body")) (.fvar "argument"),
    right := .subst (.fvar "body") (.fvar "argument") }

/-- A body steps where it is: a congruence premise whose source was captured under the binder. -/
def lamBody : RewriteRule :=
  { name := "LamBody", typeContext := [], premises := [.congruence (.fvar "x") (.fvar "y")],
    left := lam (.fvar "x"), right := lam (.fvar "y") }

/-- A body step under one premise-local binder. -/
def bodyStep : ScopedStepPremise where
  binders := [termSort]
  resultType := termSort
  source := .fvar "x"
  target := .fvar "y"

/-- The same rule with the body under a premise-local binder. -/
def lamScoped : RewriteRule :=
  { name := "LamScoped", typeContext := [], premises := [.scopedStep bodyStep],
    left := lam (.fvar "x"), right := lam (.fvar "y") }

/-- A stepped body placed one binder deeper. -/
def lamDeeper : RewriteRule :=
  { name := "LamDeeper", typeContext := [], premises := [.congruence (.fvar "x") (.fvar "y")],
    left := lam (.fvar "x"), right := lam (lam (.fvar "y")) }

def lambdaWith (rule : RewriteRule) : LanguageDef :=
  { name := "Lambda", types := ["Term"], terms := [], equations := [], rewrites := [beta, rule] }

/-- `λx. (λy. y) x`. -/
def underBinder : Pattern := lam (app (lam (.bvar 0)) (.bvar 0))

/-- A listed target is a step. -/
theorem step_of_mem_targets {relEnv : RelationEnv} {language : LanguageDef} {fuel : ℕ} {source target : Pattern}
    (listed : target ∈ (stepsAt relEnv language fuel source).map (·.2)) : Step relEnv language source target := by
  obtain ⟨⟨witness, _⟩, member, rfl⟩ := List.mem_map.mp listed
  exact ⟨witness, stepValid_of_mem_stepsAt relEnv language member⟩

/-! ## In place -/

#guard (stepsAt RelationEnv.empty (lambdaWith lamBody) 2 underBinder).map (·.2) == [lam (.bvar 0)]
#guard ContextualStep.reducts (lambdaWith lamBody) 2 underBinder == [lam (.bvar 0)]

/-- **A body steps in place**: `λx. (λy. y) x` steps to `λx. x`. -/
theorem body_steps_in_place : Step RelationEnv.empty (lambdaWith lamBody) underBinder (lam (.bvar 0)) :=
  step_of_mem_targets (fuel := 2) (by decide +kernel)

/-- `LamBody` is aligned, so on this language the reference relation is the least contextual one. -/
theorem lamBody_profile : ReferenceProfile (lambdaWith lamBody) := by
  intro rule member
  simp only [lambdaWith, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide +kernel

/-! ## Explicit binders -/

#guard (stepsAt RelationEnv.empty (lambdaWith lamScoped) 2 underBinder).map (·.2) == [lam (.bvar 0)]
#guard ContextualStep.reducts (lambdaWith lamScoped) 2 underBinder == []

/-- **A body under a premise-local binder steps.** -/
theorem body_steps_under_binder : Step RelationEnv.empty (lambdaWith lamScoped) underBinder (lam (.bvar 0)) :=
  step_of_mem_targets (fuel := 2) (by decide +kernel)

/-- The least contextual relation has no steps from `λx. (λy. y) x` when the body step has a binder:
`Beta` does not match, and the premise with a binder yields nothing. -/
theorem contextual_binder_scope_empty (fuel : ℕ) :
    ContextualStep.rewriteAt (ContextualStep.engineBasePremises RelationEnv.empty) (lambdaWith lamScoped) fuel
      underBinder = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have betaUnmatched : Match.matchPattern beta.left underBinder = [] := by decide +kernel
    have scopedRefused : ∀ (language : LanguageDef) (recursive : Pattern → List Pattern) (bindings : Match.Bindings),
        ContextualStep.premisesUsing (ContextualStep.engineBasePremises RelationEnv.empty) language recursive
          lamScoped.premises bindings = [] := by
      intro language recursive bindings
      simp [lamScoped, bodyStep, ContextualStep.premisesUsing, ContextualStep.premiseStepUsing]
    simp [ContextualStep.rewriteAt, lambdaWith, ContextualStep.applyRuleUsing, betaUnmatched, scopedRefused]

/-- **The least contextual relation refuses it.** -/
theorem contextual_refuses_binder_scope :
    ¬ ContextualStep.Step (ContextualStep.engineBasePremises RelationEnv.empty) (lambdaWith lamScoped) underBinder
      (lam (.bvar 0)) := by
  rintro ⟨fuel, step⟩
  have listed := ContextualStep.mem_rewriteAt_iff_stepAt.mpr step
  rw [contextual_binder_scope_empty fuel] at listed
  cases listed

/-! ## Quantified premises -/

/-- `AllOk {xs…} ~> Ok` when every element is ok. -/
def allOk : RewriteRule :=
  { name := "AllOk", typeContext := [],
    premises := [.forAll "xs" "x" (.relationQuery "ok" [.fvar "x"])],
    left := .apply "AllOk" [.collection .hashBag [] (some "xs")], right := ok }

def okLanguage : LanguageDef :=
  { name := "Ok", types := ["Term"], terms := [], equations := [], rewrites := [allOk] }

/-- `A` and `B` are ok; nothing else is. -/
def okRelation : RelationEnv where
  tuples relation arguments :=
    if relation = "ok" ∧ (arguments = [.apply "A" []] ∨ arguments = [.apply "B" []]) then [arguments] else []

def allOkOf (elements : List Pattern) : Pattern := .apply "AllOk" [.collection .hashBag elements none]

def letterA : Pattern := .apply "A" []
def letterB : Pattern := .apply "B" []
def bad : Pattern := .apply "Bad" []

#guard (stepsAt okRelation okLanguage 1 (allOkOf [letterA, letterB, letterA])).map (·.2) == [ok]
#guard (stepsAt okRelation okLanguage 1 (allOkOf [letterA, bad])).isEmpty
#guard ContextualStep.reductsUsing okRelation okLanguage 1 (allOkOf [letterA, letterB]) == []

/-- **Every element is ok, so the bag steps.** -/
theorem all_ok_steps : Step okRelation okLanguage (allOkOf [letterA, letterB, letterA]) ok :=
  step_of_mem_targets (fuel := 1) (by decide +kernel)

/-! ## Scopes -/

#guard (stepsAt RelationEnv.empty (lambdaWith lamDeeper) 2 underBinder).map (·.2) == [lam (lam (.bvar 1))]
#guard ContextualStep.reducts (lambdaWith lamDeeper) 2 underBinder == [lam (lam (.bvar 0))]

/-- **The stepped body keeps naming the outer binder.** -/
theorem deeper_body_lifted : Step RelationEnv.empty (lambdaWith lamDeeper) underBinder (lam (lam (.bvar 1))) :=
  step_of_mem_targets (fuel := 2) (by decide +kernel)

/-- `LamDeeper` uses a premise-bound name deeper than the premise bound it, so it is not aligned. -/
theorem lamDeeper_not_aligned : ruleAligned lamDeeper = false := by decide +kernel

/-! ## Equations under binders -/

/-- `Shift x = Lam (λ. x)`: an equation that moves its metavariable under a binder. -/
def shiftEquation : Equation :=
  { name := "Shift", typeContext := [], premises := [], left := .apply "Shift" [.fvar "x"],
    right := lam (.fvar "x") }

def shiftLanguage : LanguageDef :=
  { name := "Shift", types := ["Term"], terms := [], equations := [shiftEquation], rewrites := [] }

#guard Match.applyBindingsScoped (captureSitesOf shiftEquation.left []) [("x", .bvar 0)] 0 shiftEquation.right ==
  lam (.bvar 1)
#guard Match.applyBindings [("x", .bvar 0)] shiftEquation.right == lam (.bvar 0)

/-- **The instance keeps the variable's binder.** -/
theorem shift_instance :
    AuthoredEquation RelationEnv.empty shiftLanguage (.apply "Shift" [.bvar 0]) (lam (.bvar 1)) := by
  have instance' := AuthoredEquation.forward (relEnv := RelationEnv.empty) (language := shiftLanguage)
    (equation := shiftEquation) (source := .apply "Shift" [.bvar 0]) (initial := [("x", .bvar 0)])
    (final := [("x", .bvar 0)]) (witnesses := [])
    (by simp [shiftLanguage]) rfl (by decide +kernel) (.nil _)
  have target : Match.applyBindingsScoped (captureSitesOf shiftEquation.left shiftEquation.premises) [("x", .bvar 0)] 0
      shiftEquation.right = lam (.bvar 1) := by decide +kernel
  rw [target] at instance'
  exact instance'

/-- `Shift` moves its metavariable deeper than it captured it, so it is not aligned. -/
theorem shift_not_aligned : equationAligned shiftEquation = false := by decide +kernel

end Mettapedia.OSLF.MeTTaIL.ReferenceStepControls
