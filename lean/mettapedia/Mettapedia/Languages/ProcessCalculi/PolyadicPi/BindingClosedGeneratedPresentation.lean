import Mettapedia.Languages.ProcessCalculi.PolyadicPi.AllArityBinding
import Mettapedia.OSLF.Syntax.BindingClosedGeneratedEquations
import Mettapedia.OSLF.Syntax.BindingClosedAuthoredPresentation

/-!
# The actual all-arity closed pi equation guest

This guest is generated from independently authored sorts, all finite
communication arities and the seven structural binding schemas. Its own
primitive model is reconstructed from the actual constructor inclusion.
The declared equations earn complete natural-family equality at every
stage and arbitrary supplied function argument.

The runtime unary/binary fragment is a separate signature. No operational
edge generators, compiler map or native-execution theorem are implicit in
this static presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGenerated

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.OSLF.Binding CategoricalBindingModel SecondOrderContext
open Mettapedia.CategoryTheory.RelativeClosedSyntax

universe k

def equationMetas := ClosedPresentation.AuthoredPresentation.schemaAt.{k} AllArity.equations
def equation := ClosedPresentation.AuthoredPresentation.equationAt.{k} AllArity.equations
def signature := ClosedPresentation.AuthoredPresentation.signature.{k} AllArity.equations
abbrev Guest := GeneratedCategory.Object signature.{k}

def theory := ClosedPresentation.AuthoredPresentation.theory.{k} AllArity.equations
def inclusion := ClosedPresentation.AuthoredPresentation.inclusion.{k} AllArity.equations

def operations : ClosedPresentation.Operations AllArity.sig Guest.{k} :=
  ClosedPresentation.GeneratedEquations.operations equationMetas equation

def constructorComparison : inclusion.functor ≅ operations.interpretation.functor :=
  ClosedPresentation.GeneratedEquations.constructorComparison equationMetas equation

theorem equations_satisfied : operations.model.SchemaFamilySatisfaction AllArity.equations := by
  intro origin
  exact ClosedPresentation.GeneratedEquations.satisfied equationMetas equation (ULift.up origin)

theorem complete_equation_values (origin : Fin AllArity.equations.length) (stage : Guest.{k})
    (parameters : stage ⟶ operations.family AllArity.structuralMetas)
    (environment : operations.model.Env stage (AllArity.equations.get origin).ctx) :
    (operations.model.interp AllArity.structuralMetas (AllArity.equations.get origin).lhs).value
        stage parameters environment =
      (operations.model.interp AllArity.structuralMetas (AllArity.equations.get origin).rhs).value
        stage parameters environment :=
  ClosedPresentation.GeneratedEquations.complete_values equationMetas equation (ULift.up origin)
    stage parameters environment

theorem contextual_equations :
    operations.model.Satisfies (authoredEquationPresentation AllArity.sig AllArity.equations) :=
  (operations.model.schema_family_iff_contextual AllArity.equations).mp equations_satisfied

def ownInterpretation := ClosedPresentation.AuthoredPresentation.interpretation AllArity.equations
  operations contextual_equations

theorem complete_constructor_restriction : inclusion.functor ⋙ ownInterpretation.functor =
    operations.interpretation.functor :=
  ClosedPresentation.AuthoredPresentation.complete_restriction AllArity.equations operations contextual_equations

def names : Guest.{k} := operations.sort Srt.nm
def processes : Guest.{k} := operations.sort Srt.pr
def nameTuple (arity : Nat) : Guest.{k} := operations.context (AllArity.names arity)

theorem full_receiver_domain (arity : Nat) :
    operations.family (AllArity.sig.arity (AllArity.Op.inp arity)) =
      ((𝟙_ Guest ⟶[Guest] names) ⊗ ((nameTuple arity ⟶[Guest] processes) ⊗ 𝟙_ Guest)) := rfl

theorem full_sender_domain (arity : Nat) :
    operations.family (AllArity.sig.arity (AllArity.Op.out arity)) =
      (𝟙_ Guest ⟶[Guest] names) ⊗ operations.family (AllArity.nameArguments arity) := rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGenerated
