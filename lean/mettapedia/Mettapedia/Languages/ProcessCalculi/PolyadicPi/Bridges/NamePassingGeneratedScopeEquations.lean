import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedScopeLaws

/-!
# Whole continuation equations from the generated pi scope laws

The source application equations hold on complete generalized values and
reference-body functions. Evaluation at the generic return argument earns
function equality; extrusion and exchange use the independently admitted
target structural schemas. No syntactic representative of a function is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedScopeEquations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open BindingClosedPrimitiveOperations
open NamePassingContinuationOperations NamePassingContinuationValues NamePassingGeneratedScopeLaws
open NamePassingBindingClosedSchemas (call_as_evaluation appliedBody)
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (exchange)

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

theorem call_ext {Z A P : C} {first last : Z ⟶ (A ⟶[C] P)}
    (evaluations : call (fst Z A ≫ first) (snd Z A) =
      call (fst Z A ≫ last) (snd Z A)) : first = last := by
  apply MonoidalClosed.uncurry_injective
  have read := congrArg (fun observed => exchange A Z ≫ observed) evaluations
  have pair (function : Z ⟶ (A ⟶[C] P)) :
      lift (fst A Z) (snd A Z ≫ function) = A ◁ function := by
    apply hom_ext <;> simp
  simpa only [call_as_evaluation, comp_lift_assoc, exchange, lift_fst_assoc, lift_snd_assoc,
    lift_fst, lift_snd, pair, MonoidalClosed.uncurry_eq] using read

variable (binding : ClosedPresentation.Operations AllArity.sig C)

attribute [local irreducible] Operations.application Operations.definition Operations.carrier

theorem application_carrier_evaluation
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (name : Z ⟶ names binding)
    (value body : Z ⟶ (continuation binding).termObject)
    (argument result : Z ⟶ names binding) :
    call (lift (lift name (lift value body) ≫ (continuation binding).carrier) argument ≫
      (continuation binding).application) result =
    call (lift name (lift value (lift body argument ≫ (continuation binding).application)) ≫
      (continuation binding).carrier) result := by
  erw [application_value]
  simp only [comp_lift_assoc, comp_lift]
  erw [carrier_value, carrier_value, application_value]
  erw [fresh_parallel binding satisfied]
  apply congrArg (bindFresh (continuation binding))
  simp only [comp_lift_assoc]
  exact parallel_frame_exchange binding satisfied _ _ _

theorem application_carrier
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (name : Z ⟶ names binding)
    (value body : Z ⟶ (continuation binding).termObject)
    (argument : Z ⟶ names binding) :
    lift (lift name (lift value body) ≫ (continuation binding).carrier) argument ≫
      (continuation binding).application =
    lift name (lift value (lift body argument ≫ (continuation binding).application)) ≫
      (continuation binding).carrier := by
  apply call_ext (A := names binding) (P := processes binding)
  simp only [comp_lift_assoc, comp_lift]
  exact application_carrier_evaluation binding satisfied
    (fst Z (names binding) ≫ name) (fst Z (names binding) ≫ value)
    (fst Z (names binding) ≫ body) (fst Z (names binding) ≫ argument) (snd Z (names binding))

theorem application_definition_evaluation
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (value : Z ⟶ (continuation binding).termObject)
    (body : Z ⟶ (continuation binding).boundBodyObject)
    (argument result : Z ⟶ names binding) :
    call (lift (lift value body ≫ (continuation binding).definition) argument ≫
      (continuation binding).application) result =
    call (lift value (lift body argument ≫ appliedBody (continuation binding)) ≫
      (continuation binding).definition) result := by
  erw [application_value]
  simp only [comp_lift_assoc]
  erw [definition_value, definition_value]
  simp only [comp_lift_assoc]
  erw [appliedBody_value, application_value]
  let active : (Z ⊗ names binding) ⊗ names binding ⟶ processes binding :=
    call (call (fst (Z ⊗ names binding) (names binding) ≫ fst Z (names binding) ≫ body)
      (snd (Z ⊗ names binding) (names binding)))
      (fst (Z ⊗ names binding) (names binding) ≫ snd Z (names binding))
  let message : Z ⊗ names binding ⟶ processes binding :=
    lift (snd Z (names binding))
      (lift (fst Z (names binding) ≫ argument) (fst Z (names binding) ≫ result)) ≫
        (continuation binding).send
  let stored : Z ⊗ names binding ⟶ processes binding :=
    lift (snd Z (names binding)) (fst Z (names binding) ≫ value) ≫
      (continuation binding).input ≫ (continuation binding).replication
  have derived := nested_parallel_scope binding satisfied active message stored
  simpa only [active, message, stored, call, comp_lift_assoc, comp_lift, Category.assoc,
    privateExchange_parameter_assoc, privateExchange_newest, privateExchange_previous,
    Operations.termObject, continuation] using derived

theorem application_definition
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (value : Z ⟶ (continuation binding).termObject)
    (body : Z ⟶ (continuation binding).boundBodyObject)
    (argument : Z ⟶ names binding) :
    lift (lift value body ≫ (continuation binding).definition) argument ≫
      (continuation binding).application =
    lift value (lift body argument ≫ appliedBody (continuation binding)) ≫
      (continuation binding).definition := by
  apply call_ext (A := names binding) (P := processes binding)
  simp only [comp_lift_assoc]
  exact application_definition_evaluation binding satisfied
    (fst Z (names binding) ≫ value) (fst Z (names binding) ≫ body)
    (fst Z (names binding) ≫ argument) (snd Z (names binding))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedScopeEquations
