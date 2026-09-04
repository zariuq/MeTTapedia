import Mathlib.CategoryTheory.Types.Basic
import Mettapedia.UniversalAlgebra.SyntacticFunctor

/-!
# Models as evaluation functors on the syntactic category

A nonempty model satisfying an equation system evaluates each finite context
as a finite power of its carrier and each syntactic arrow as simultaneous term
evaluation.  The resulting functor preserves the displayed terminal and
binary-product operations by explicit equations.

The nonempty-carrier hypothesis is explicit.  It is used only to extend a
finite valuation to the total natural-number valuation required by the
existing `Model.Satisfies` interface.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAlgebra

open CategoryTheory

universe u v

variable {S : Signature.{u}}

namespace Term

/-- Extend a finite valuation to all natural-number variables using a selected
carrier inhabitant outside the finite context. -/
noncomputable def extendFinite {Carrier : Type v} [Nonempty Carrier]
    {bound : Nat} (valuation : Fin bound → Carrier) : Nat → Carrier :=
  fun index => if below : index < bound then valuation ⟨index, below⟩
    else Classical.choice inferInstance

@[simp] theorem extendFinite_apply {Carrier : Type v} [Nonempty Carrier]
    {bound : Nat} (valuation : Fin bound → Carrier) (position : Fin bound) :
    extendFinite valuation position.val = valuation position := by
  simp only [extendFinite, position.isLt, dite_true]

end Term

namespace BoundedTermTuple

/-- Evaluate every component of a bounded tuple under a finite valuation. -/
def evaluate {Carrier : Type v} (model : Model S Carrier)
    {input output : Nat} (tuple : BoundedTermTuple S input output) :
    (Fin input → Carrier) → (Fin output → Carrier) :=
  fun valuation position =>
    (tuple.component position).1.evaluateBelow model valuation
      (tuple.component position).2

/-- Pointwise generated consequence gives identical tuple evaluations in
every nonempty satisfying model. -/
theorem evaluate_eq_of_equivalent {Carrier : Type v} [Nonempty Carrier]
    (model : Model S Carrier) {system : EquationSystem S}
    (satisfies : model.Satisfies system)
    {input output : Nat} {left right : BoundedTermTuple S input output}
    (equivalent : Equivalent system left right) :
    evaluate model left = evaluate model right := by
  funext valuation position
  let totalValuation : Nat → Carrier := Term.extendFinite valuation
  have consequenceHolds := EquationalConsequence.holdsInModel
    (equivalent position) model satisfies totalValuation
  have leftAgreement := Term.evaluateBelow_eq_evaluate model valuation
    totalValuation (by
      intro index below
      simp only [totalValuation, Term.extendFinite, below, dite_true])
    (left.component position).1 (left.component position).2
  have rightAgreement := Term.evaluateBelow_eq_evaluate model valuation
    totalValuation (by
      intro index below
      simp only [totalValuation, Term.extendFinite, below, dite_true])
    (right.component position).1 (right.component position).2
  exact leftAgreement.trans (consequenceHolds.trans rightAgreement.symm)

/-- Evaluation of raw tuple composition is function composition. -/
theorem evaluate_comp {Carrier : Type v} [Nonempty Carrier]
    (model : Model S Carrier) {first second third : Nat}
    (earlier : BoundedTermTuple S first second)
    (later : BoundedTermTuple S second third) :
    evaluate model (comp earlier later) =
      evaluate model later ∘ evaluate model earlier := by
  funext valuation position
  let totalValuation : Nat → Carrier := Term.extendFinite valuation
  have compositeAgreement := Term.evaluateBelow_eq_evaluate model valuation
    totalValuation (by
      intro index below
      simp only [totalValuation, Term.extendFinite, below, dite_true])
    ((later.component position).1.subst (substitution earlier))
    (Term.variablesBelow_subst (later.component position).2
      (substitution earlier) (by
        intro index below
        simp only [substitution, Term.finSubstitution, below, dite_true]
        exact (earlier.component ⟨index, below⟩).2))
  change Term.evaluateBelow model valuation
      ((later.component position).1.subst (substitution earlier)) _ =
    Term.evaluateBelow model
      (fun earlierPosition => Term.evaluateBelow model valuation
        (earlier.component earlierPosition).1
        (earlier.component earlierPosition).2)
      (later.component position).1 (later.component position).2
  rw [compositeAgreement]
  simp only [substitution]
  rw [Term.evaluate_subst_finSubstitution model totalValuation
    (fun position => (earlier.component position).1)
    (later.component position).1 (later.component position).2]
  congr 1
  funext earlierPosition
  symm
  exact Term.evaluateBelow_eq_evaluate model valuation totalValuation
    (by
      intro index below
      simp only [totalValuation, Term.extendFinite, below, dite_true])
    (earlier.component earlierPosition).1
    (earlier.component earlierPosition).2

/-- Evaluation of the raw identity tuple is the identity function. -/
theorem evaluate_identity {Carrier : Type v} (model : Model S Carrier)
    (size : Nat) :
    evaluate model (identity size) = id := by
  funext valuation position
  rfl

/-- Evaluation sends raw tuple pairing to pointwise concatenation. -/
theorem evaluate_pair {Carrier : Type v} (model : Model S Carrier)
    {input left right : Nat}
    (first : BoundedTermTuple S input left)
    (second : BoundedTermTuple S input right) :
    evaluate model (pair first second) =
      fun valuation => Fin.addCases
        (evaluate model first valuation)
        (evaluate model second valuation) := by
  funext valuation position
  refine Fin.addCases ?_ ?_ position
  · intro firstPosition
    simp only [evaluate, pair, Fin.addCases_left]
  · intro secondPosition
    simp only [evaluate, pair, Fin.addCases_right]

end BoundedTermTuple

namespace Model

/-- Evaluate a quotient arrow in a fixed satisfying model. -/
noncomputable def mapSyntacticHom {Carrier : Type v} [Nonempty Carrier]
    {system : EquationSystem S} (model : Model S Carrier)
    (satisfies : model.Satisfies system) {input output : Nat} :
    SyntacticCategory.Hom system input output →
      ((Fin input → Carrier) → (Fin output → Carrier)) :=
  Quotient.lift
    (BoundedTermTuple.evaluate model)
    (fun _left _right equivalent =>
      BoundedTermTuple.evaluate_eq_of_equivalent model satisfies equivalent)

@[simp] theorem mapSyntacticHom_mk {Carrier : Type v} [Nonempty Carrier]
    {system : EquationSystem S} (model : Model S Carrier)
    (satisfies : model.Satisfies system) {input output : Nat}
    (tuple : BoundedTermTuple S input output) :
    model.mapSyntacticHom satisfies (SyntacticCategory.mk system tuple) =
      BoundedTermTuple.evaluate model tuple := rfl

/-- A nonempty satisfying model evaluates the syntactic category in finite
powers of its carrier. -/
noncomputable def syntacticFunctor {Carrier : Type v} [Nonempty Carrier]
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) :
    SyntacticCategory system ⥤ Type v where
  obj context := Fin (SyntacticCategory.objectSize system context) → Carrier
  map arrow := ↾(model.mapSyntacticHom satisfies arrow)
  map_id context := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    exact BoundedTermTuple.evaluate_identity model _
  map_comp first second := by
    induction first using Quotient.inductionOn with
    | _ first =>
      induction second using Quotient.inductionOn with
      | _ second =>
        apply TypeCat.Hom.ext
        apply TypeCat.Fun.ext
        exact BoundedTermTuple.evaluate_comp model first second

/-- The model functor maps the selected terminal arrow to the unique function
into the empty finite power. -/
theorem syntacticFunctor_map_terminalArrow
    {Carrier : Type v} [Nonempty Carrier]
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) (input : Nat) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.terminalArrow (S := S) system
          (input := input)) =
      ↾(fun (_valuation : Fin input → Carrier) (position : Fin 0) =>
        Fin.elim0 position) := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext _valuation position
  exact Fin.elim0 position

/-- The model functor maps the selected first projection to restriction along
the first finite-context inclusion. -/
theorem syntacticFunctor_map_firstProjection
    {Carrier : Type v} [Nonempty Carrier]
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) (left right : Nat) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.firstProjection system left right) =
      ↾(fun (valuation : Fin (left + right) → Carrier)
          (position : Fin left) => valuation (Fin.castAdd right position)) := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext valuation position
  rfl

/-- The model functor maps the selected second projection to restriction along
the second finite-context inclusion. -/
theorem syntacticFunctor_map_secondProjection
    {Carrier : Type v} [Nonempty Carrier]
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system) (left right : Nat) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.secondProjection system left right) =
      ↾(fun (valuation : Fin (left + right) → Carrier)
          (position : Fin right) => valuation (Fin.natAdd left position)) := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext valuation position
  rfl

/-- The model functor maps syntactic pairing to pointwise concatenation of the
two evaluated tuples. -/
theorem syntacticFunctor_map_pair
    {Carrier : Type v} [Nonempty Carrier]
    (system : EquationSystem S) (model : Model S Carrier)
    (satisfies : model.Satisfies system)
    {input left right : Nat}
    (first : SyntacticCategory.object system input ⟶
      SyntacticCategory.object system left)
    (second : SyntacticCategory.object system input ⟶
      SyntacticCategory.object system right) :
    (model.syntacticFunctor system satisfies).map
        (SyntacticCategory.pair system first second) =
      ↾(fun (valuation : Fin input → Carrier) => Fin.addCases
        ((model.syntacticFunctor system satisfies).map first valuation)
        ((model.syntacticFunctor system satisfies).map second valuation)) := by
  induction first using Quotient.inductionOn with
  | _ first =>
    induction second using Quotient.inductionOn with
    | _ second =>
      apply TypeCat.Hom.ext
      apply TypeCat.Fun.ext
      exact BoundedTermTuple.evaluate_pair model first second

end Model

end Mettapedia.UniversalAlgebra
