import Mettapedia.OSLF.Syntax.CategoricalAuthoredRulePolynomial
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# A free event graph for one premise-free authored rule

Once the binding interpretation and program carrier are fixed, a rule with
no recursive premises generates an event for each parameter assignment.
Its event graph is the rule's parameter object with the authored conclusion
as endpoint arrow. The universal map into any interpretation is that
interpretation's actual firing action.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalAuthoredNullaryFree

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalAuthoredRuleInterpretation
open Mettapedia.OSLF.Binding.CategoricalAuthoredRulePolynomial
open Mettapedia.OSLF.Binding.CategoricalScopedRuleAction
open Mettapedia.OSLF.Binding.CategoricalScopedRuleActionMaps
open Mettapedia.OSLF.Binding

universe u v
variable {S : Signature} {schema : List (MetaArity S)}
variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
  [MonoidalClosed D] [HasPullbacks D]
variable (M : Model S D) (P : ProgramCarrier M)
variable (conclusion : PositionedRewrite (withMetas S schema))

/-- The authored rule with this conclusion and no recursive premise. -/
def nullaryRule : IntrinsicScopedConditionalPolynomial.Rule S schema :=
  ⟨conclusion, []⟩

omit [HasPullbacks D] in
theorem rulePremises_nil (E : D)
    (endpoints : E ⟶ EndpointPairs M P) :
    rulePremises M P E endpoints (nullaryRule conclusion) = [] := rfl

noncomputable def freeNullary : OperationalModel M P [nullaryRule conclusion] where
  event := Parameters (schema := schema) M conclusion.ctx
  endpoints := ruleConclusion M P (nullaryRule conclusion)
  action index := by
    have one : index = ⟨0, by simp⟩ := by
      apply Fin.ext
      have bound : index.val < 1 := index.isLt
      have zero : index.val = 0 := by omega
      simpa only [Fin.val_mk] using zero
    subst index
    exact { fire := 𝟙 _, endpoint_law := by rfl }

/-- The free event for a parameter assignment is interpreted by the
target's actual firing action. -/
noncomputable def freeNullaryHom
    (X : OperationalModel M P [nullaryRule conclusion]) :
    OperationalModel.Hom M P (freeNullary M P conclusion) X := by
  let fire : Parameters (schema := schema) M conclusion.ctx ⟶ X.event :=
    (X.action ⟨0, by simp⟩).fire
  have endpoints : fire ≫ X.endpoints =
      (freeNullary M P conclusion).endpoints := by
    have h : (X.action ⟨0, by simp⟩).fire ≫ X.endpoints =
        (𝟙 (Parameters (schema := schema) M conclusion.ctx)) ≫
          ruleConclusion M P (nullaryRule conclusion) :=
      (X.action ⟨0, by simp⟩).endpoint_law
    exact h.trans (Category.id_comp _)
  refine { event := fire, endpoints := endpoints, action := ?_ }
  intro index
  have one : index = ⟨0, by simp⟩ := by
    apply Fin.ext
    have bound : index.val < 1 := index.isLt
    have zero : index.val = 0 := by omega
    simpa only [Fin.val_mk] using zero
  subst index
  change ((𝟙 _ ≫ 𝟙 _) ≫ fire) = 𝟙 _ ≫ fire
  simp

/-- No target choice remains once the event attached to every parameter
assignment is sent to the target firing of that same authored rule. -/
noncomputable def freeNullaryIsInitial :
    IsInitial (freeNullary M P conclusion) :=
  IsInitial.ofUniqueHom
    (fun X => freeNullaryHom M P conclusion X)
    (by
      intro X f
      apply OperationalModel.Hom.ext
      have h := f.action ⟨0, by simp⟩
      change ((𝟙 (freeNullary M P conclusion).event ≫
          𝟙 (freeNullary M P conclusion).event) ≫
          (X.action ⟨0, by simp⟩).fire) =
        𝟙 (freeNullary M P conclusion).event ≫ f.event at h
      change f.event = (X.action ⟨0, by simp⟩).fire
      have hs : f.event =
          𝟙 (freeNullary M P conclusion).event ≫
            (X.action ⟨0, by simp⟩).fire := by
        simpa using h.symm
      exact hs.trans (Category.id_comp _))

/-- The free nullary firing graph is also the initial algebra of the
authored rule's event-slice endofunctor. This connects the direct universal
construction to the algebraic route used for recursive rules. -/
noncomputable def freeNullaryPolynomialIsInitial :
    IsInitial ((singleRuleToAlgebra M P (nullaryRule conclusion)).obj
      (freeNullary M P conclusion)) :=
  (freeNullaryIsInitial M P conclusion).isInitialObj
    (singleRuleToAlgebra M P (nullaryRule conclusion))
    (freeNullary M P conclusion)

end Mettapedia.OSLF.Binding.CategoricalAuthoredNullaryFree
