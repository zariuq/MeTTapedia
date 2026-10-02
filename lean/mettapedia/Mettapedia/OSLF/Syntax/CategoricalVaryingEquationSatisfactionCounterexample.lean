import Mettapedia.OSLF.Syntax.SecondOrderVariableAbstractionControls
import Mettapedia.OSLF.Syntax.CategoricalBindingEquationSatisfaction
import Mettapedia.OSLF.Syntax.BindingContextualEquationInterpretation
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Context-varying equation families fail contextual coherence

An equation family that imposes P() = c only at the empty metavariable
context has reflexive dependency-only instances there. Its contextual
instances can distinguish a local variable from the constant. Transporting
one such instance to a fresh metavariable context, where the family has no
equations, rejects the family as a coherent equation presentation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CategoricalVaryingEquationSatisfactionCounterexample

open CategoryTheory
open CategoricalBindingModel
open SecondOrderContext

open CategoryTheory.MonoidalCategory
open SecondOrderVariableAbstraction.Controls
  (signature schemaMetas oldEquations oldConstant oldObject ordinaryVariable freshObject)

abbrev sig := signature
abbrev schema := schemaMetas

/-- There is one equation at the empty metavariable context and none at
contexts with a declared metavariable. -/
def varyingAxioms : (X : Object sig) → List (EqAxiom (withMetas sig X.arities) schema)
  | ⟨[]⟩ => oldEquations
  | ⟨_ :: _⟩ => []

private theorem empty_metaOp_elim {sort : sig.Srt} (op : MetaOp (S := sig) [] sort) : False := by
  cases op with
  | mk i => exact Fin.elim0 i

/-- With no ordinary variables or metavariables, the existing signature
has exactly its single constant as a term. -/
theorem closed_term_unique (term : Term (withMetas sig []) [] ()) :
    term = oldConstant := by
  cases term with
  | var x => nomatch x
  | op op args =>
    cases op with
    | inl op => cases op; cases args; rfl
    | inr metaOp => exact False.elim (empty_metaOp_elim metaOp)

/-- Every admitted old body makes the active schema equation reflexive. -/
theorem closed_instance_equal
    (body : (k : Fin schema.length) →
      Term (withMetas sig []) (schema.get k).1 (schema.get k).2) :
    instantiate body (oldEquations.get ⟨0, by decide⟩).lhs =
      instantiate body (oldEquations.get ⟨0, by decide⟩).rhs := by
  change bind (argsToSub (.nil : Args (withMetas sig []) [] []))
    (body ⟨0, by decide⟩) = oldConstant
  rw [closed_term_unique (body ⟨0, by decide⟩)]
  rfl

universe u v

/-- The dependency-only axiom law accepts the raw family in every
categorical binding model. It is insufficient for contextual coherence. -/
theorem every_model_dependency_satisfies {D : Type u} [Category.{v} D]
    [CartesianMonoidalCategory D] (model : Model sig D) :
    ∀ X, model.DependencySatisfiesAxioms X.arities (varyingAxioms X) := by
  intro X index body
  rcases X with ⟨arities⟩
  cases arities with
  | nil =>
    rcases index with ⟨n, bound⟩
    change n < 1 at bound
    have zero : n = 0 := by omega
    subst n
    change model.interp [] (instantiate body (oldEquations.get ⟨0, by decide⟩).lhs) =
      model.interp [] (instantiate body (oldEquations.get ⟨0, by decide⟩).rhs)
    exact congrArg (model.interp []) (closed_instance_equal body)
  | cons head rest => exact Fin.elim0 index

/-- The same sort has two values and all selected powers are ordinary
functions. The single existing constant is interpreted as false. -/
def boolModel : Model sig Type where
  sort := fun _ => Bool
  power Γ _ := contextOf (S := sig) (fun _ => Bool) Γ → Bool
  eval := fun _ _ => TypeCat.ofHom (fun pair => pair.2 pair.1)
  curry := fun map => TypeCat.ofHom (fun stage context => map (context, stage))
  curry_eval := fun _ => rfl
  curry_unique := by
    intro Γ sort Z map candidate equality
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext stage context
    exact (congrArg (fun arrow : contextOf (S := sig) (fun _ => Bool) Γ ⊗ Z ⟶ Bool =>
      arrow (context, stage)) equality).symm
  op := fun _ => TypeCat.ofHom (fun _ => false)

theorem boolModel_dependency_satisfies :
    ∀ X, boolModel.DependencySatisfiesAxioms X.arities (varyingAxioms X) :=
  every_model_dependency_satisfies boolModel

/-- The schema body reads the separately supplied ambient variable. -/
def openBody : ContextualAssignment (withMetas sig []) schema [()] :=
  fun i => Fin.cases (.var .zero) (fun j => Fin.elim0 j) i

def ambient : Sub (withMetas sig []) [()] [()] := fun _ x => .var x

def ordinary : Sub (withMetas sig []) [] [()] := fun _ x => nomatch x

theorem contextual_left :
    ContextualAssignment.instantiate openBody ambient ordinary
      ((varyingAxioms oldObject).get ⟨0, by decide⟩).lhs =
        ordinaryVariable := rfl

theorem contextual_right :
    ContextualAssignment.instantiate openBody ambient ordinary
      ((varyingAxioms oldObject).get ⟨0, by decide⟩).rhs =
        oldConstant := rfl

/-- The actual generalized interpretations differ at the stage carrying
the value true for the ordinary variable. -/
theorem interp_variable_ne_constant :
    boolModel.interp [] ordinaryVariable ≠ boolModel.interp [] oldConstant := by
  intro equality
  have observed := congrArg
    (fun element : boolModel.Elem [] [()] () =>
      element.value (PUnit : Type) (TypeCat.ofHom (fun _ => PUnit.unit))
        (fun _ _ => TypeCat.ofHom (fun _ => true)) PUnit.unit) equality
  change true = false at observed
  cases observed

/-- Old global satisfaction does not make this actual contextual axiom
instance sound, even in a target with all the selected function objects. -/
theorem contextual_instance_fails :
    boolModel.interp [] (ContextualAssignment.instantiate openBody ambient ordinary
        ((varyingAxioms oldObject).get ⟨0, by decide⟩).lhs) ≠
      boolModel.interp [] (ContextualAssignment.instantiate openBody ambient ordinary
        ((varyingAxioms oldObject).get ⟨0, by decide⟩).rhs) :=
  interp_variable_ne_constant

/-- The contextual semantic law rejects this actual Boolean model,
although the dependency-only axiom law accepts the raw family. -/
theorem global_satisfaction_does_not_imply_contextual :
    (∀ X, boolModel.DependencySatisfiesAxioms X.arities (varyingAxioms X)) ∧
      ¬ BindingContextualEquationInterpretation.Satisfies (boolModel.kripke [])
        (varyingAxioms oldObject) := by
  refine ⟨boolModel_dependency_satisfies, ?_⟩
  intro satisfies
  exact contextual_instance_fails
    (satisfies.interpret_instance ⟨0, by decide⟩ openBody ambient ordinary)

/-- The actual assignment to the empty metavariable context. -/
def eraseFresh : freshObject ⟶ oldObject := fun i => Fin.elim0 i

/-- The captured variable equation cannot be transported to the fresh
source context, whose equation list is empty. -/
theorem contextual_generator_not_stable :
    ¬ EqClosure (varyingAxioms freshObject)
      (instInto eraseFresh (ContextualAssignment.instantiate openBody ambient ordinary
        ((varyingAxioms oldObject).get ⟨0, by decide⟩).lhs))
      (instInto eraseFresh (ContextualAssignment.instantiate openBody ambient ordinary
        ((varyingAxioms oldObject).get ⟨0, by decide⟩).rhs)) := by
  intro related
  have same := eqClosure_empty_eq related
  have observed := congrArg SecondOrderVariableAbstraction.Controls.rootVariable same
  change true = false at observed
  cases observed

/-- The strengthened generator contract excludes the incoherent family;
it cannot be packaged as an actual equation presentation. -/
theorem varying_family_not_presentation :
    ¬ ∃ P : EquationPresentation sig schema, P.axioms = varyingAxioms := by
  rintro ⟨⟨axioms, stable⟩, family⟩
  change axioms = varyingAxioms at family
  subst axioms
  exact contextual_generator_not_stable
    (stable eraseFresh ⟨0, by decide⟩ openBody ambient ordinary)

end Mettapedia.OSLF.Binding.CategoricalVaryingEquationSatisfactionCounterexample
