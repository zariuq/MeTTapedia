import Mettapedia.OSLF.Syntax.CategoricalBindingQuotientEquivalence
import Mettapedia.OSLF.Syntax.CartesianModelLexEventInterpretations

/-!
# Retained events over the binding-equation classifier

An interpretation may carry an arbitrary object of individual firing events
with an endpoint arrow into the pair of interpreted program states. The
binding-equation classifying equivalence lifts to these event-equipped
interpretations without requiring event injectivity, endpoint coverage, or
the existence of a reduction image.

Authored rule actions and the event-path semantics remain separate
extensions of this contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalBindingEventEquivalence

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext

universe u v

variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (Eqs : EquationPresentation S schema)

/-- Evaluation of an equation-class interpretation at the selected program
object, natural in every interpretation map. -/
def programValues (program : EquationContexts Eqs) :
    QuotientStructuredFunctor (D := D) Eqs ⥤ D where
  obj F := F.carrier.obj program
  map τ := τ.app program
  map_id := by intro; rfl
  map_comp := by intros; rfl

/-- The possible source-target pairs of the selected program object. -/
noncomputable def programPairs (program : EquationContexts Eqs) :
    QuotientStructuredFunctor (D := D) Eqs ⥤ D :=
  Mettapedia.OSLF.CartesianContextModels.pairValues (programValues Eqs program)

/-- The binding-equation classifier remains universal after adjoining an
object of individual firing events and its two endpoint maps. The comma
category retains event maps themselves, not merely endpoint existence. -/
noncomputable def retainedEventEquivalence (program : EquationContexts Eqs) :
    Comma (𝟭 D)
      ((bindingEquationEquivalence (D := D) Eqs).functor ⋙ programPairs Eqs program) ≌
    Comma (𝟭 D) (programPairs Eqs program) :=
  Mettapedia.OSLF.CartesianContextModels.liftEventInterpretationEquivalence
    (bindingEquationEquivalence (D := D) Eqs) (programPairs Eqs program)

end Mettapedia.OSLF.Binding.CategoricalBindingEventEquivalence

#print axioms Mettapedia.OSLF.Binding.CategoricalBindingEventEquivalence.retainedEventEquivalence
