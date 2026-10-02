import Mettapedia.GSLT.LanguageDef.BindingSignatureOpenReification
import Mettapedia.OSLF.Syntax.BindingEquationQuotientModel

/-!
# Authored first-order equations as contextual binding axioms

The compiler below searches the actual constructor declarations and the
equation's named schema context. It accepts only premise-free rows without
separate metavariable dependency metadata. Both sides retain exact named
readback. Instantiating their ordinary variables is explicit equation-schema
instantiation; it is not reflective ambient substitution into quoted code.

The resulting quotient uses the existing full binding-clone construction.
Its satisfaction theorem permits arbitrary quotient-valued environments,
including beneath binders. This compiler does not compile collection algebra
metadata or equations with binding metavariables.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.EquationPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.LanguageDef.NamedFreeContext
open Mettapedia.GSLT.LanguageDef.BindingSyntax.OpenReification

/-- A successful constructor search, with its actual authored row retained. -/
structure CompiledRow (language : LanguageDef) (equation : Equation)
    (sort : TypeExpr) where
  premiseFree : equation.premises = []
  noBindingMetadata : equation.bindings = none
  left : Term (signatureOf language) (contextSorts equation.typeContext) sort
  right : Term (signatureOf language) (contextSorts equation.typeContext) sort
  leftAccepted : reifyOpen? language equation.typeContext equation.left sort = some left
  rightAccepted : reifyOpen? language equation.typeContext equation.right sort = some right

/-- Reify both declared sides, without inventing a sort or ignoring premises. -/
def compile? (language : LanguageDef) (equation : Equation) (sort : TypeExpr) :
    Option (CompiledRow language equation sort) :=
  if premiseFree : equation.premises = [] then
    if noBindingMetadata : equation.bindings = none then
      match leftAccepted : reifyOpen? language equation.typeContext equation.left sort with
      | none => none
      | some left =>
          match rightAccepted : reifyOpen? language equation.typeContext equation.right sort with
          | none => none
          | some right =>
              some ⟨premiseFree, noBindingMetadata, left, right,
                leftAccepted, rightAccepted⟩
    else none
  else none

namespace CompiledRow

variable {language : LanguageDef} {equation : Equation} {sort : TypeExpr}

/-- The left side reads back with the original schema-variable names. -/
theorem left_named (row : CompiledRow language equation sort) :
    namedFirstOrderErase? (names equation.typeContext) row.left = some equation.left :=
  reifyOpen?_named row.leftAccepted

/-- The right side reads back with the original schema-variable names. -/
theorem right_named (row : CompiledRow language equation sort) :
    namedFirstOrderErase? (names equation.typeContext) row.right = some equation.right :=
  reifyOpen?_named row.rightAccepted

/-- Ordinary schema parameters are retained as the axiom's sorted context. -/
def toAxiom (row : CompiledRow language equation sort) : EqAxiom (signatureOf language) [] :=
  ⟨contextSorts equation.typeContext, sort, embed row.left, embed row.right⟩

/-- Explicit schema instantiation allows every typed intrinsic replacement.
The empty contextual-body assignment supplies no extra metavariables. -/
theorem instance_eqClosure (row : CompiledRow language equation sort)
    {Γ : Ctx (signatureOf language)}
    (environment : Sub (signatureOf language) (contextSorts equation.typeContext) Γ) :
    EqClosure [row.toAxiom] (bind environment row.left) (bind environment row.right) := by
  let bodies : ContextualAssignment (signatureOf language) [] [] := fun position =>
    Fin.elim0 position
  let ambient : Sub (signatureOf language) [] Γ := fun _ position => nomatch position
  have generated := EqClosure.ax (E := [row.toAxiom]) ⟨0, by simp⟩ bodies ambient environment
  simpa only [List.get_eq_getElem, List.getElem_cons_zero, toAxiom,
    ContextualAssignment.instantiate_embed] using generated

/-- The established equation quotient supplies a full binding algebra. -/
noncomputable abbrev quotient (row : CompiledRow language equation sort) :=
  BindingEquationQuotientModel.algebra [row.toAxiom]

/-- Satisfaction uses arbitrary semantic ordinary and captured environments.
It is inherited from the constructed contextual quotient, not assumed. -/
theorem quotient_satisfies (row : CompiledRow language equation sort) :
    BindingEquationInterpretation.Satisfies row.quotient [row.toAxiom] :=
  BindingEquationQuotientModel.algebra_satisfies [row.toAxiom]

end CompiledRow

end Mettapedia.GSLT.LanguageDef.BindingSyntax.EquationPresentation
