import Mettapedia.GSLT.GraphTheory.BudgetedBetaObserver
import Mettapedia.GSLT.Logic.ReflectiveBubble

/-!
# The β-bubble is reflective

λ-terms run on λ-terms by application.  Up to β-conversion, application is
point-surjective onto the polynomial maps: the code of a polynomial is the
abstraction of its translation, and one β-step evaluates it
(`lambdaReflexive`).  With the constant combinator `K`, the λ-terms modulo β
form a reflexive structure whose equivalence is exactly the equality of the
default β-bubble, so that bubble is reflective (`betaReflectiveBubble`).

**Positive reading.**  Every λ-term has a β-fixed point, by the diagonal step
(`lambda_fixedPoint`): the fixed-point combinator, without a primitive for
recursion.

**Negative reading.**
* No λ-term decides β-conversion (`no_lambda_decides_betaConv`).
* Every fragment decision of β-conversion realised by a λ-term excludes an
  explicit diagonal term, and its verdict there is `outsideFragment`
  (`internal_betaDecision_fragment_proper`,
  `internal_betaDecision_diagonal_outside`).

**Controls.**
* A *total* decision of β-conversion exists in the metalanguage, by classical
  logic (`classicalBetaDecision`), and no λ-term realises it
  (`classicalBetaDecision_not_internal`): the diagonal theorem is about
  internal deciders, and the classical decision sits one stage above.
* `I` and `K` are not β-convertible (`identity_not_betaConv_constant`), which
  makes the bubble's equality nontrivial.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.GraphTheory.ReflectiveBeta

open Mettapedia.GSLT
open Mettapedia.GSLT.GraphTheory
open Mettapedia.GSLT.GraphTheory.BudgetedBeta
open Mettapedia.GSLT.ObserverBubble
open Mettapedia.GSLT.Reflection
open Mettapedia.Logic.Diagonal

/-! ## β-conversion facts -/

theorem betaConv_of_parRed {left right : LambdaTerm} (step : left ⇛ right) :
    BetaConv left right :=
  Relation.EqvGen.rel _ _ step

/-- β-conversion is a congruence for application on the right. -/
theorem betaConv_app_right (function : LambdaTerm) {argument argument' : LambdaTerm}
    (convertible : BetaConv argument argument') :
    BetaConv (.app function argument) (.app function argument') := by
  induction convertible with
  | rel first second step => exact Relation.EqvGen.rel _ _ (.app (ParRed.refl function) step)
  | refl term => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ firstIh secondIh => exact Relation.EqvGen.trans _ _ _ firstIh secondIh

/-- One β-step. -/
theorem betaConv_beta (body argument : LambdaTerm) :
    BetaConv (.app (.lam body) argument) (LambdaTerm.subst 0 argument body) :=
  betaConv_of_parRed (beta_to_parRed body argument)

/-- `K a b` converts to `a`. -/
theorem constant_betaConv (first second : LambdaTerm) :
    BetaConv (.app (.app LambdaTerm.K first) second) first := by
  have firstStep : BetaConv (.app LambdaTerm.K first) (.lam (LambdaTerm.shift 1 0 first)) :=
    betaConv_beta (.lam (.var 1)) first
  have secondStep : BetaConv (.app (.lam (LambdaTerm.shift 1 0 first)) second) first := by
    have step := betaConv_beta (LambdaTerm.shift 1 0 first) second
    rwa [LambdaTerm.subst_shift_cancel] at step
  exact betaConv_equivalence.trans (betaConv_app_left second firstStep) secondStep

/-! ## Polynomials as λ-terms -/

/-- The translation of a polynomial: the variable is de Bruijn index `0`, and
constants are shifted past the new binder. -/
def toTerm : AppPolynomial LambdaTerm → LambdaTerm
  | .var => .var 0
  | .const constant => LambdaTerm.shift 1 0 constant
  | .app function argument => .app (toTerm function) (toTerm argument)

theorem subst_toTerm (value : LambdaTerm) :
    ∀ polynomial : AppPolynomial LambdaTerm,
      LambdaTerm.subst 0 value (toTerm polynomial) = polynomial.eval LambdaTerm.app value
  | .var => rfl
  | .const constant => LambdaTerm.subst_shift_cancel value constant
  | .app function argument => by
      change LambdaTerm.app (LambdaTerm.subst 0 value (toTerm function))
          (LambdaTerm.subst 0 value (toTerm argument)) = _
      rw [subst_toTerm value function, subst_toTerm value argument]
      rfl

/-- **λ-terms modulo β form a reflexive structure**: the code of a polynomial
is the abstraction of its translation. -/
def lambdaReflexive : Reflexive LambdaTerm where
  Equiv := BetaConv
  equivalence := betaConv_equivalence
  apply := .app
  apply_congr := fun {_ function' argument _} functionConv argumentConv =>
    betaConv_equivalence.trans (betaConv_app_left argument functionConv)
      (betaConv_app_right function' argumentConv)
  constant := LambdaTerm.K
  constant_law := constant_betaConv
  code polynomial := .lam (toTerm polynomial)
  code_law polynomial value := by
    have step := betaConv_beta (toTerm polynomial) value
    rwa [subst_toTerm] at step

/-- **The default β-bubble is reflective.** -/
def betaReflectiveBubble : ReflectiveBubble betaGSLT applicativeRules ℕ where
  bubble := betaBubble
  reflexive := lambdaReflexive
  equiv_iff _ _ := Iff.rfl

/-! ## The two readings -/

/-- **Every λ-term has a β-fixed point**, by the diagonal step. -/
theorem lambda_fixedPoint (function : LambdaTerm) :
    ∃ fixed, BetaConv fixed (.app function fixed) :=
  ⟨lambdaReflexive.elementFixedPoint function, lambdaReflexive.elementFixedPoint_spec function⟩

/-- `I` and `K` are distinct β-normal forms, hence not convertible. -/
theorem identity_not_betaConv_constant : ¬ BetaConv LambdaTerm.I LambdaTerm.K := by
  intro convertible
  have equal := normalForm_eq_of_betaConv (by decide) (by decide) convertible
  exact absurd equal (by decide)

/-- **No λ-term decides β-conversion.** -/
theorem no_lambda_decides_betaConv (decider : LambdaTerm) :
    ¬ lambdaReflexive.DecidesEquiv decider :=
  betaReflectiveBubble.no_internal_total_decision identity_not_betaConv_constant decider

/-- **Internal carve-outs of β-conversion are proper**: a fragment decision
realised by a λ-term excludes the diagonal of that term against any fragment
term and any term not convertible with it. -/
theorem internal_betaDecision_fragment_proper
    (decision : FragmentDecision betaReflectiveBubble.Equal) {decider : LambdaTerm}
    (realizes : betaReflectiveBubble.InternallyRealizes decision decider)
    {yes no : LambdaTerm} (yesIn : decision.Fragment yes) (distinct : ¬ BetaConv yes no) :
    ¬ decision.Fragment (betaReflectiveBubble.diagonalTerm decider yes no) :=
  betaReflectiveBubble.diagonal_not_mem_fragment decision realizes yesIn distinct

/-- The verdict of such a decision on its diagonal is `outsideFragment`. -/
theorem internal_betaDecision_diagonal_outside
    (decision : FragmentDecision betaReflectiveBubble.Equal) {decider : LambdaTerm}
    (realizes : betaReflectiveBubble.InternallyRealizes decision decider)
    {yes no : LambdaTerm} (yesIn : decision.Fragment yes) (distinct : ¬ BetaConv yes no) :
    decision.verdict (betaReflectiveBubble.diagonalTerm decider yes no) yes =
      .outsideFragment () :=
  betaReflectiveBubble.diagonal_verdict_outside decision realizes yesIn distinct

/-! ## Control: a total decision one stage up -/

/-- **A total decision of β-conversion in the metalanguage**, by classical
logic: its fragment is every term. -/
noncomputable def classicalBetaDecision : FragmentDecision betaReflectiveBubble.Equal where
  Fragment _ := True
  fragmentDecidable _ := isTrue trivial
  answer left right _ _ := @decide (BetaConv left right) (Classical.propDecidable _)
  answer_exact _ _ _ _ := @decide_eq_true_iff _ (Classical.propDecidable _)

/-- **No λ-term realises the classical total decision.** -/
theorem classicalBetaDecision_not_internal (decider : LambdaTerm) :
    ¬ betaReflectiveBubble.InternallyRealizes classicalBetaDecision decider := fun realizes =>
  internal_betaDecision_fragment_proper classicalBetaDecision realizes trivial
    identity_not_betaConv_constant trivial

end Mettapedia.GSLT.GraphTheory.ReflectiveBeta
