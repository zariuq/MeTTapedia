import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mettapedia.UniversalAlgebra.ConservativeExtension

/-!
# Universal-algebra terms with a finite variable bound

An operation interpretation of arity `n` must depend only on its `n` formal
arguments.  `Term.VariablesBelow n` records that condition independently of a
particular variable representation.

The bounded evaluator is defined directly from its proof of boundedness.  It
therefore evaluates a nullary template without requiring an arbitrary default
element of the carrier.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u v

variable {S : Signature.{u}}

namespace Term

open scoped BigOperators

/-- Every variable occurrence in a term has index strictly below `bound`. -/
def VariablesBelow (bound : Nat) : Term S → Prop
  | .var index => index < bound
  | .op _operation arguments => ∀ position, VariablesBelow bound (arguments position)

/-- Increasing the declared finite context preserves boundedness. -/
theorem VariablesBelow.mono {smaller larger : Nat} {term : Term S}
    (bounded : term.VariablesBelow smaller) (included : smaller ≤ larger) :
    term.VariablesBelow larger := by
  induction term with
  | var index => exact Nat.lt_of_lt_of_le bounded included
  | op _operation arguments inductionHypothesis =>
      intro position
      exact inductionHypothesis position (bounded position)

/-- A computable finite context large enough for every variable occurrence in
a term.  Summing branch bounds avoids a special case for nullary operations. -/
def variableBound : Term S → Nat
  | .var index => index + 1
  | .op _operation arguments =>
      ∑ position, variableBound (arguments position)

/-- Every finitary term is bounded by its computed variable context. -/
theorem variablesBelow_variableBound : ∀ term : Term S,
    term.VariablesBelow term.variableBound
  | .var index => Nat.lt_succ_self index
  | .op _operation arguments => by
      intro position
      apply (variablesBelow_variableBound (arguments position)).mono
      simpa only [variableBound] using
        (Finset.single_le_sum
          (f := fun other => variableBound (arguments other))
          (fun _other _member => Nat.zero_le _)
          (Finset.mem_univ position))

/-- A term together with a finite upper bound on all of its variable
occurrences. -/
abbrev Bounded (S : Signature.{u}) (bound : Nat) :=
  { term : Term S // term.VariablesBelow bound }

/-- Substitution depends only on the entries actually occurring below the
declared bound. -/
theorem subst_eq_of_variablesBelow {bound : Nat} {term : Term S}
    (bounded : term.VariablesBelow bound)
    (left right : Nat → Term S)
    (agree : ∀ index, index < bound → left index = right index) :
    term.subst left = term.subst right := by
  induction term with
  | var index =>
      exact agree index bounded
  | op operation arguments ih =>
      simp only [Term.subst_op]
      congr 1
      funext position
      exact ih position (bounded position)

/-- A bounded term remains bounded after a substitution whose relevant images
are bounded. -/
theorem variablesBelow_subst
    {sourceBound targetBound : Nat} {term : Term S}
    (bounded : term.VariablesBelow sourceBound)
    (substitution : Nat → Term S)
    (substitutionBounded : ∀ index, index < sourceBound →
      (substitution index).VariablesBelow targetBound) :
    (term.subst substitution).VariablesBelow targetBound := by
  induction term with
  | var index =>
      exact substitutionBounded index bounded
  | op _operation arguments ih =>
      intro position
      exact ih position (bounded position)

/-- Extend a finite vector of terms to a total substitution.  Values outside
the finite domain are deliberately irrelevant to a bounded template. -/
def finSubstitution {bound : Nat} (arguments : Fin bound → Term S) :
    Nat → Term S :=
  fun index => if below : index < bound then arguments ⟨index, below⟩ else .var index

@[simp] theorem finSubstitution_apply {bound : Nat}
    (arguments : Fin bound → Term S) (position : Fin bound) :
    finSubstitution arguments position.val = arguments position := by
  simp only [finSubstitution, position.isLt, dite_true]

/-- Direct evaluation of a bounded term from a finite valuation. -/
def evaluateBelow {bound : Nat} {Carrier : Type v}
    (model : Model S Carrier) (valuation : Fin bound → Carrier) :
    (term : Term S) → term.VariablesBelow bound → Carrier
  | .var index, bounded => valuation ⟨index, bounded⟩
  | .op operation arguments, bounded =>
      model.interpret operation (fun position =>
        evaluateBelow model valuation (arguments position) (bounded position))

/-- Direct bounded evaluation agrees with ordinary evaluation under every
total valuation extending the finite one. -/
theorem evaluateBelow_eq_evaluate {bound : Nat} {Carrier : Type v}
    (model : Model S Carrier) (finiteValuation : Fin bound → Carrier)
    (totalValuation : Nat → Carrier)
    (agrees : ∀ index (below : index < bound),
      finiteValuation ⟨index, below⟩ = totalValuation index)
    (term : Term S) (bounded : term.VariablesBelow bound) :
    term.evaluateBelow model finiteValuation bounded =
      term.evaluate model totalValuation := by
  induction term with
  | var index =>
      exact agrees index bounded
  | op operation arguments ih =>
      simp only [evaluateBelow, Term.evaluate]
      apply congrArg (model.interpret operation)
      funext position
      exact ih position (bounded position)

/-- Substituting a finite argument vector into a bounded template and then
evaluating is exactly direct bounded evaluation of the template. -/
theorem evaluate_subst_finSubstitution {bound : Nat} {Carrier : Type v}
    (model : Model S Carrier) (valuation : Nat → Carrier)
    (arguments : Fin bound → Term S) (term : Term S)
    (bounded : term.VariablesBelow bound) :
    (term.subst (finSubstitution arguments)).evaluate model valuation =
      term.evaluateBelow model
        (fun position => (arguments position).evaluate model valuation)
        bounded := by
  rw [Term.evaluate_subst]
  symm
  apply evaluateBelow_eq_evaluate
  intro index below
  simp only [finSubstitution, below, dite_true]

end Term

end Mettapedia.UniversalAlgebra
