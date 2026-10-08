import Mettapedia.Languages.ProcessCalculi.PolyadicPi.CategoricalOperationalClosure
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalConstructorReadout

/-!
# Return-indexed native fetch evidence

The complete supplied stored function serves an actual unary COMM request.
The authored firing is curried in the public return name. Both endpoint
arrows compare with the independently constructed continuation operations.
Every future clone substitution acts on the same retained receipt.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperational

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open NamePassingContinuationOperations NamePassingCategoricalCompiler

attribute [local irreducible] Mettapedia.OSLF.Binding.BindingEquationQuotientModel.operation

abbrev events := CategoricalOperational.edges
abbrev source := CategoricalOperational.source
abbrev target := CategoricalOperational.target

/-- A complete endpoint comparison at every future world follows from the
supplied local comparison and the actual answer's naturality. -/
theorem complete_abstraction_endpoint {Z X E P : Ambient}
    (body : Z ⊗ X ⟶ E) (endpoint : E ⟶ P) (answer : Z ⟶ X.functorHom P)
    (comparison : ∀ (world : Base) (parameter : Z.obj world) (argument : X.obj world),
      endpoint.app world (body.app world (parameter,argument)) =
        (answer.app world parameter).app world (𝟙 world) argument) :
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction body ≫
      (ihom X).map endpoint = answer := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro parameter
  apply Functor.functorHom_ext
  intro future change
  apply ConcreteCategory.hom_ext
  intro argument
  change endpoint.app future (body.app future (Z.map change parameter,argument)) =
    (answer.app world parameter).app future change argument
  have transported := congrArg
    (fun function : (X.functorHom P).obj future =>
      function.app future (𝟙 future) argument)
    (answer.naturality_apply change parameter)
  change (answer.app future (Z.map change parameter)).app future (𝟙 future) argument =
    (answer.app world parameter).app future (change ≫ 𝟙 future) argument at transported
  rw [Category.comp_id] at transported
  exact (comparison future (Z.map change parameter) argument).trans transported

/-- Every supplied actual natural arrow transports its complete value. -/
theorem receipt_substitution {X Y : Ambient} (arrow : X ⟶ Y)
    {world future : Base} (change : world ⟶ future) (parameter : X.obj world) :
    Y.map change (arrow.app world parameter) =
      arrow.app future (X.map change parameter) :=
  (arrow.naturality_apply change parameter).symm

abbrev fetchDomain : Ambient := operations.names ⊗ operations.termObject

/-- The independent request carries the name, return and complete stored function. -/
def fetchRequest : fetchDomain ⊗ operations.names ⟶
    operations.names ⊗ (operations.names ⊗ operations.termObject) :=
  lift (fst fetchDomain operations.names ≫ fst operations.names operations.termObject)
    (lift (snd fetchDomain operations.names)
      (fst fetchDomain operations.names ≫ snd operations.names operations.termObject))

def fetchFiring : fetchDomain ⊗ operations.names ⟶ events :=
  fetchRequest ≫ CategoricalOperational.unaryCommunication

def fetch : fetchDomain ⟶ (operations.names.functorHom events) :=
  Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction fetchFiring

def fetchSource : fetchDomain ⟶ operations.termObject :=
  lift (fst operations.names operations.termObject)
    (lift (snd operations.names operations.termObject)
      (fst operations.names operations.termObject ≫ operations.reference)) ≫ operations.carrier

theorem reference_current (world : Base) (name result : operations.names.obj world) :
    ((operations.reference.app world name).app world (𝟙 world)) result =
      operations.output.app world (name,result) :=
  abstraction_current operations.output world name result

theorem carrier_current (world : Base) (name result : operations.names.obj world)
    (value body : operations.termObject.obj world) :
    ((operations.carrier.app world (name,value,body)).app world (𝟙 world)) result =
      operations.parallel.app world
        (body.app world (𝟙 world) result, operations.input.app world (name,value)) := by
  unfold NamePassingContinuationOperations.Operations.carrier
  rw [abstraction_current]
  rfl

theorem fetchFiring_source (world : Base) (name result : operations.names.obj world)
    (value : operations.termObject.obj world) :
    source.app world (fetchFiring.app world ((name,value),result)) =
      (fetchSource.app world (name,value)).app world (𝟙 world) result := by
  change source.app world (CategoricalOperational.unaryEvent world name result value) =
    ((operations.carrier.app world (name,value,operations.reference.app world name)).app
      world (𝟙 world)) result
  rw [carrier_current,reference_current]
  exact CategoricalOperational.unaryEvent_source world name result value

theorem fetchFiring_target (world : Base) (name result : operations.names.obj world)
    (value : operations.termObject.obj world) :
    target.app world (fetchFiring.app world ((name,value),result)) =
      value.app world (𝟙 world) result :=
  CategoricalOperational.unaryEvent_target world name result value

/-- The whole source continuation, including every future return argument. -/
theorem fetch_source : fetch ≫ (ihom operations.names).map source = fetchSource := by
  exact complete_abstraction_endpoint fetchFiring source fetchSource
    (fun world input result => fetchFiring_source world input.1 result input.2)

/-- The receipt's complete target function is precisely the supplied stored value. -/
theorem fetch_target : fetch ≫ (ihom operations.names).map target =
    snd operations.names operations.termObject := by
  exact complete_abstraction_endpoint fetchFiring target
    (snd operations.names operations.termObject)
    (fun world input result => fetchFiring_target world input.1 result input.2)

theorem fetchFiring_substitution {world future : Base} (change : world ⟶ future)
    (name result : operations.names.obj world) (value : operations.termObject.obj world) :
    events.map change (fetchFiring.app world ((name,value),result)) =
      fetchFiring.app future
        ((operations.names.map change name,operations.termObject.map change value),
          operations.names.map change result) :=
  CategoricalOperational.unaryEvent_substitution change name result value

theorem fetch_future (world future : Base) (change : world ⟶ future)
    (parameter : fetchDomain.obj world) (result : operations.names.obj future) :
    ((fetch.app world parameter).app future change) result =
      fetchFiring.app future (fetchDomain.map change parameter,result) := rfl

theorem fetch_substitution {world future : Base} (change : world ⟶ future)
    (parameter : fetchDomain.obj world) :
    (operations.names.functorHom events).map change (fetch.app world parameter) =
      fetch.app future (fetchDomain.map change parameter) :=
  receipt_substitution fetch change parameter

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCategoricalOperational
