import Mettapedia.UniversalAlgebra.BoundedTerm

/-!
# Interpretations between finitary algebraic signatures

An interpretation maps each source operation to a target term whose variables
are bounded by the source arity.  The bound is mathematical data: it makes
substitution compositional and permits model reducts even for nullary
operations, without choosing an arbitrary carrier element.

This file concerns signatures and models.  Preservation of a particular
equation system is added separately by `EquationSystem.Interpretation`.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

universe u v w

namespace Signature

/-- A finitary algebraic interpretation sends every source operation to a
target term in precisely the operation's formal variables. -/
structure Interpretation (source : Signature.{u}) (target : Signature.{v}) :
    Type (max u v) where
  operation : (symbol : source.Operation) →
    Term.Bounded target (source.arity symbol)

end Signature

variable {S : Signature.{u}} {T : Signature.{v}} {U : Signature.{w}}

namespace Term

/-- Translate a term along an algebraic signature interpretation. -/
def translate (interpretation : Signature.Interpretation S T) :
    Term S → Term T
  | .var index => .var index
  | .op symbol arguments =>
      (interpretation.operation symbol).1.subst
        (finSubstitution (fun position =>
          translate interpretation (arguments position)))

@[simp] theorem translate_var
    (interpretation : Signature.Interpretation S T) (index : Nat) :
    translate interpretation (.var index) = .var index := rfl

@[simp] theorem translate_op
    (interpretation : Signature.Interpretation S T) (symbol : S.Operation)
    (arguments : Fin (S.arity symbol) → Term S) :
    translate interpretation (.op symbol arguments) =
      (interpretation.operation symbol).1.subst
        (finSubstitution (fun position =>
          translate interpretation (arguments position))) := rfl

/-- Translation preserves every finite upper bound on variables. -/
theorem variablesBelow_translate
    (interpretation : Signature.Interpretation S T) {bound : Nat} :
    ∀ {term : Term S}, term.VariablesBelow bound →
      (term.translate interpretation).VariablesBelow bound
  | .var _index, bounded => bounded
  | .op symbol arguments, bounded => by
      apply variablesBelow_subst (interpretation.operation symbol).2
      intro index below
      simp only [finSubstitution, below, dite_true]
      exact variablesBelow_translate interpretation (bounded ⟨index, below⟩)

/-- Translation commutes with simultaneous substitution. -/
theorem translate_subst (interpretation : Signature.Interpretation S T)
    (substitution : Nat → Term S) :
    ∀ term : Term S,
      (term.subst substitution).translate interpretation =
        (term.translate interpretation).subst
          (fun index => (substitution index).translate interpretation)
  | .var _index => rfl
  | .op symbol arguments => by
      simp only [Term.subst_op, translate_op, Term.subst_subst]
      apply subst_eq_of_variablesBelow (interpretation.operation symbol).2
      intro index below
      simp only [finSubstitution, below, dite_true]
      exact translate_subst interpretation substitution (arguments ⟨index, below⟩)

end Term

namespace Signature.Interpretation

/-- The identity interpretation presents an operation by applying itself to
its formal variables. -/
def id (signature : Signature.{u}) : Interpretation signature signature where
  operation symbol := ⟨.op symbol (fun position => .var position.val), by
    intro position
    exact position.isLt⟩

/-- Interpret source symbols in the intermediate signature and then translate
their defining terms into the target signature. -/
def comp (first : Interpretation S T) (second : Interpretation T U) :
    Interpretation S U where
  operation symbol :=
    ⟨(first.operation symbol).1.translate second,
      Term.variablesBelow_translate second (first.operation symbol).2⟩

end Signature.Interpretation

namespace Term

/-- The identity interpretation acts identically on every term. -/
@[simp] theorem translate_id : ∀ term : Term S,
    term.translate (Signature.Interpretation.id S) = term
  | .var _index => rfl
  | .op symbol arguments => by
      simp only [translate_op, Signature.Interpretation.id, Term.subst_op]
      congr 1
      funext position
      simp only [Term.subst_var, finSubstitution_apply]
      exact translate_id (arguments position)

/-- Translation along a composite interpretation is composition of term
translations. -/
theorem translate_comp (first : Signature.Interpretation S T)
    (second : Signature.Interpretation T U) : ∀ term : Term S,
    term.translate (first.comp second) =
      (term.translate first).translate second
  | .var _index => rfl
  | .op symbol arguments => by
      simp only [translate_op, Signature.Interpretation.comp, translate_subst]
      apply subst_eq_of_variablesBelow
        (variablesBelow_translate second (first.operation symbol).2)
      intro index below
      simp only [finSubstitution, below, dite_true]
      exact translate_comp first second (arguments ⟨index, below⟩)

end Term

namespace Model

/-- Every target model has a reduct along a signature interpretation. -/
def reduct {Carrier : Type w} (interpretation : Signature.Interpretation S T)
    (targetModel : Model T Carrier) : Model S Carrier where
  interpret symbol arguments :=
    (interpretation.operation symbol).1.evaluateBelow targetModel arguments
      (interpretation.operation symbol).2

end Model

/-- Evaluation of a translated term in a target model agrees with evaluation
of the source term in the induced reduct. -/
theorem Term.evaluate_translate {Carrier : Type w}
    (interpretation : Signature.Interpretation S T)
    (targetModel : Model T Carrier) (valuation : Nat → Carrier) :
    ∀ term : Term S,
      (term.translate interpretation).evaluate targetModel valuation =
        term.evaluate (targetModel.reduct interpretation) valuation
  | .var _index => rfl
  | .op symbol arguments => by
      rw [Term.translate_op, Term.evaluate_subst]
      simp only [Term.evaluate, Model.reduct]
      symm
      apply Term.evaluateBelow_eq_evaluate
      intro index below
      simp only [Term.finSubstitution, below, dite_true]
      exact (Term.evaluate_translate interpretation targetModel valuation
        (arguments ⟨index, below⟩)).symm

end Mettapedia.UniversalAlgebra
