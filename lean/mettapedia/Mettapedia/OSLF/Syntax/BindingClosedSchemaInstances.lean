import Mettapedia.OSLF.Syntax.BindingClosedSchemaClassification
import Mettapedia.OSLF.Syntax.CategoricalContextualEquationSoundness
import Mettapedia.OSLF.Syntax.CategoricalBindingEquations

/-!
# Schema-family equality and every contextual equation instance

Complete natural-family satisfaction of an authored schema list is equivalent
to the existing global contextual model contract. The proof uses actual
metavariable instantiation and its semantic restaging law; the reverse direction
uses the genuine generic metavariables and the earned instantiation unit law.
Consequently the generated contextual equation closure preserves the complete
interpretations, including captured ambient parameters.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Binding

open _root_.CategoryTheory

namespace SecondOrderContext

variable {S : Signature} {schema : List (MetaArity S)}

mutual

theorem instantiate_liftSchema (X : Object S)
    (body : (index : Fin schema.length) → Term (withMetas S X.arities)
      (schema.get index).1 (schema.get index).2) :
    {context : Ctx S} → {sort : S.Srt} → (term : Term (withMetas S schema) context sort) →
    instantiate body (liftSchema X term) = instInto body term
  | _, _, .var _ => rfl
  | _, _, .op (Sum.inl operation) arguments =>
      congrArg (Term.op (S := withMetas S X.arities) (Sum.inl operation))
        (instantiate_liftSchemaArgs X body arguments)
  | _, _, .op (Sum.inr (.mk index)) arguments =>
      congrArg (fun assigned => bind (argsToSub assigned) (body index))
        (instantiate_liftSchemaArgs X body arguments)

theorem instantiate_liftSchemaArgs (X : Object S)
    (body : (index : Fin schema.length) → Term (withMetas S X.arities)
      (schema.get index).1 (schema.get index).2) :
    {arities : List (MetaArity S)} → {context : Ctx S} →
    (arguments : Args (withMetas S schema) arities context) →
    instantiateArgs body (liftSchemaArgs X arguments) = instIntoArgs body arguments
  | _, _, .nil => rfl
  | _, _, .cons head rest => congrArg₂ Args.cons
      (instantiate_liftSchema X body head) (instantiate_liftSchemaArgs X body rest)

end

end SecondOrderContext

namespace CategoricalBindingModel.Model

open SecondOrderContext

universe u v

variable {S : Signature} {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
variable (model : CategoricalBindingModel.Model S C)
variable {schema : List (MetaArity S)} (equations : List (EqAxiom S schema))

def SchemaFamilySatisfaction : Prop := ∀ index : Fin equations.length,
  model.interp schema (equations.get index).lhs = model.interp schema (equations.get index).rhs

theorem schema_family_iff_dependency : model.SchemaFamilySatisfaction equations ↔
    model.DependencySatisfies (authoredEquationPresentation S equations) := by
  constructor
  · intro satisfied X index body
    let sourceIndex : Fin equations.length :=
      ⟨index.val, by
        have bound := index.isLt
        change index.val < (equations.map (liftEquation X)).length at bound
        simpa only [List.length_map] using bound⟩
    have selected : (equations.map (liftEquation X)).get index = liftEquation X (equations.get sourceIndex) := by
      have bound : index.val < equations.length := sourceIndex.isLt
      change (equations.map (liftEquation X))[index.val] = liftEquation X (equations[index.val])
      simp
    change model.interp X.arities (instantiate body ((equations.map (liftEquation X)).get index).lhs) =
      model.interp X.arities (instantiate body ((equations.map (liftEquation X)).get index).rhs)
    rw [selected]
    simp only [liftEquation]
    rw [instantiate_liftSchema, instantiate_liftSchema]
    rw [model.interp_instInto body (equations.get sourceIndex).lhs,
      model.interp_instInto body (equations.get sourceIndex).rhs, satisfied sourceIndex]
  · intro satisfied index
    let X : Object S := ⟨schema⟩
    let liftedIndex : Fin (equations.map (liftEquation X)).length :=
      ⟨index.val, by simpa only [List.length_map] using index.isLt⟩
    have selected : (equations.map (liftEquation X)).get liftedIndex = liftEquation X (equations.get index) := by
      change (equations.map (liftEquation X))[index.val] = liftEquation X (equations[index.val])
      simp
    have same := satisfied X liftedIndex (metaVar (M := schema))
    change model.interp schema
        (instantiate (metaVar (M := schema)) ((equations.map (liftEquation X)).get liftedIndex).lhs) =
      model.interp schema
        (instantiate (metaVar (M := schema)) ((equations.map (liftEquation X)).get liftedIndex).rhs) at same
    rw [selected] at same
    simp only [liftEquation] at same
    rw [instantiate_liftSchema, instantiate_liftSchema, instInto_metaVar_id, instInto_metaVar_id] at same
    exact same

theorem schema_family_iff_contextual : model.SchemaFamilySatisfaction equations ↔
    model.Satisfies (authoredEquationPresentation S equations) :=
  (model.schema_family_iff_dependency equations).trans (model.authored_contextualSatisfies_iff equations).symm

theorem schema_family_contextual_closure (satisfied : model.SchemaFamilySatisfaction equations)
    (X : Object S) {context : Ctx S} {sort : S.Srt}
    {first second : Term (withMetas S X.arities) context sort}
    (related : EqClosure ((authoredEquationPresentation S equations).axioms X) first second) :
    model.interp X.arities first = model.interp X.arities second :=
  model.interp_eqClosure ((model.schema_family_iff_contextual equations).mp satisfied X) related

end CategoricalBindingModel.Model

end Mettapedia.OSLF.Binding
