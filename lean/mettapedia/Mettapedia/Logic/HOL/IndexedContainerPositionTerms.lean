import Mettapedia.Logic.HOL.IndexedConstructorTerms
import Mettapedia.Logic.HOL.OrderedPositionPrograms
import Mettapedia.TypeTheory.IndexedPositiveContainerPositions

/-!
# Structural count and index programs for registered containers

The compiler retains ordinary data fields and a separate shape field for each
nested container. A nested shape is not a source index variable. Per-entry
count programs are primitive readings; the complete ordered field plan is
generated from the source description rather than supplied as a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates
universe u v w x
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
  {Const : Ty Base → Type w} {parameters : Nat} {Γ Δ : Ctx Base}

structure Reading (I : Interface.{u}) (registry : Registry I) (Const : Ty Base → Type w) where
  indices : IndexedConstructorTerms.Reading I Const
  number : Ty Base
  one : ClosedTerm Const number
  shapeType : (name : String) → (entry : Entry I) → registry.lookup name = some entry → Ty Base
  count : {context : List I.SortCode} → (name : String) → (entry : Entry I) →
    (registered : registry.lookup name = some entry) → entry.OutputExpr context →
    Term Const (context.map indices.sort ++ indices.parameters)
      (shapeType name entry registered ⇒ number)

namespace Reading
variable (reading : Reading I registry Const)

def fields : {context : List I.SortCode} → Code I registry parameters context → List (Ty Base)
  | _, .result _ => []
  | _, .data sort body => reading.indices.sort sort :: fields body
  | _, .recursive _ rest => fields rest
  | _, .nested name entry registered _ _ rest =>
      reading.shapeType name entry registered :: fields rest

def ignoreFields {result : Ty Base} : (fields : List (Ty Base)) →
    {Γ : Ctx Base} → Term Const Γ result → Term Const Γ (FunctionType fields result)
  | [], _, term => term
  | _ :: rest, _, term => .lam (ignoreFields rest (weaken term))

def bindPlan {domain number index : Ty Base} {fields : List (Ty Base)}
    (plan : OrderedPositionPrograms.FieldPlan Const (domain :: Γ) fields number index) :
    OrderedPositionPrograms.FieldPlan Const Γ (domain :: fields) number index :=
  plan.map (fun segment => (.lam segment.1, .lam segment.2))

/-- Source variables and retained shape fields have separate scope maps. -/
def compile : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {Γ : Ctx Base} → Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ →
    OrderedPositionPrograms.FieldPlan Const Γ (reading.fields code) reading.number reading.indices.index
  | _, .result _, _, _ => []
  | _, .data _ body, _, rho => bindPlan (compile body (Subst.lift rho))
  | _, .recursive expression rest, Γ, rho =>
      (ignoreFields (reading.fields rest) (weakenCtx Γ reading.one),
        ignoreFields (reading.fields rest) (HOL.subst rho (reading.indices.term expression))) ::
      compile rest rho
  | _, .nested name entry registered output childIndex rest, _, rho =>
      bindPlan ((ignoreFields (reading.fields rest)
          (.app (weaken (HOL.subst rho (reading.count name entry registered output))) (.var .vz)),
        ignoreFields (reading.fields rest) (weaken (HOL.subst rho (reading.indices.term childIndex)))) ::
        compile rest (fun entry => weaken (rho entry)))

def resultProgram : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {Γ : Ctx Base} → Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ →
    Term Const Γ (FunctionType (reading.fields code) reading.indices.index)
  | _, .result expression, _, rho => HOL.subst rho (reading.indices.term expression)
  | _, .data _ body, _, rho => .lam (resultProgram body (Subst.lift rho))
  | _, .recursive _ rest, _, rho => resultProgram rest rho
  | _, .nested _ _ _ _ _ rest, _, rho =>
      .lam (resultProgram rest (fun entry => weaken (rho entry)))

variable (model : HenkinModel.{v,w,x} Base Const)

theorem ignoreFields_denote {result : Ty Base} (fields : List (Ty Base))
    (term : Term Const Γ result) (values : model.Valuation Γ)
    (data : Env (Ty.denote model.Carrier) fields) :
    applyValues model fields (model.denote (ignoreFields fields term) values) data =
      model.denote term values := by
  induction fields generalizing Γ with
  | nil => rfl
  | cons first rest hypothesis =>
      change applyValues model rest
        (model.denote (ignoreFields rest (weaken term)) (model.extend values data.1)) data.2 = _
      rw [hypothesis, Soundness.denote_weaken]

theorem bindPlan_evaluate {domain number index : Ty Base} {fields : List (Ty Base)}
    (numbers : Nat ≃ Ty.denote model.Carrier number)
    (plan : OrderedPositionPrograms.FieldPlan Const (domain :: Γ) fields number index)
    (values : model.Valuation Γ) (value : Ty.denote model.Carrier domain)
    (data : Env (Ty.denote model.Carrier) fields) :
    OrderedPositionPrograms.evaluateFields model numbers (domain :: fields) values (value, data) (bindPlan plan) =
      OrderedPositionPrograms.evaluateFields model numbers fields (model.extend values value) data plan := by
  simp only [OrderedPositionPrograms.evaluateFields, bindPlan, List.map_map, Function.comp_def]
  rfl

end Reading

/-- Only the primitive source readings are premises. No complete field-plan
or selected-decoder correctness law is part of this interface. -/
structure Realization (reading : Reading I registry Const) (ordered : registry.OrderedFinitary)
    (model : HenkinModel.{v,w,x} Base Const) where
  numbers : Nat ≃ Ty.denote model.Carrier reading.number
  value : ∀ sort, I.Value sort → Ty.denote model.Carrier (reading.indices.sort sort)
  index : I.Index → Ty.denote model.Carrier reading.indices.index
  shape : (name : String) → (entry : Entry I) → (registered : registry.lookup name = some entry) →
    (output : entry.Output) → entry.container.Shape output →
      Ty.denote model.Carrier (reading.shapeType name entry registered)
  parameterValues : model.Valuation reading.indices.parameters
  index_correct : ∀ {context} (expression : I.IndexExpr context) (environment : Env I.Value context),
    model.denote (reading.indices.term expression)
      (reading.indices.valuation model value parameterValues environment) = index (I.evalIndex expression environment)
  one_correct : ∀ values : model.Valuation [], model.denote reading.one values = numbers 1
  count_correct : ∀ {context} (name : String) (entry : Entry I) (registered : registry.lookup name = some entry)
    (output : entry.OutputExpr context) (environment : Env I.Value context)
    (sourceShape : entry.container.Shape (entry.evalOutput output environment)),
    model.denote (reading.count name entry registered output)
      (reading.indices.valuation model value parameterValues environment)
      (shape name entry registered _ sourceShape) =
        numbers ((ordered.containerOrdered name entry registered).positions sourceShape).length

namespace Realization
variable {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
  {model : HenkinModel.{v,w,x} Base Const} (realization : Realization reading ordered model)

def encodeFields : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {environment : Env I.Value context} → {index : I.Index} → Code.Shape code environment index →
      Env (Ty.denote model.Carrier) (reading.fields code)
  | _, .result _, _, _, _ => PUnit.unit
  | _, .data sort body, _, _, sourceShape =>
      (realization.value sort sourceShape.1, encodeFields body sourceShape.2)
  | _, .recursive _ rest, _, _, sourceShape => encodeFields rest sourceShape
  | _, .nested name entry registered output _ rest, environment, _, sourceShape =>
      (realization.shape name entry registered (entry.evalOutput output environment) sourceShape.1,
        encodeFields rest sourceShape.2)

def Represents {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) : Prop :=
  ∀ {type} (entry : Var (context.map reading.indices.sort ++ reading.indices.parameters) type),
    model.denote (rho entry) values =
      (reading.indices.valuation model realization.value realization.parameterValues environment) entry

theorem substituted_denote {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    {type : Ty Base} (term : Term Const (context.map reading.indices.sort ++ reading.indices.parameters) type) :
    model.denote (HOL.subst rho term) values =
      model.denote term (reading.indices.valuation model realization.value realization.parameterValues environment) := by
  rw [Soundness.denote_subst]
  apply congrArg (model.denote term)
  funext type entry
  exact represented entry

theorem represents_lift {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (sort : I.SortCode) (value : I.Value sort) :
    realization.Represents (context := sort :: context) (value, environment) (Subst.lift rho)
      (model.extend values (realization.value sort value)) := by
  intro type entry
  cases entry with
  | vz => rfl
  | vs prior =>
      change model.denote (weaken (rho prior)) (model.extend values (realization.value sort value)) = _
      rw [Soundness.denote_weaken]
      exact represented prior

theorem represents_weaken {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    {domain : Ty Base} (value : Ty.denote model.Carrier domain) :
    realization.Represents environment (fun entry => weaken (rho entry)) (model.extend values value) := by
  intro type entry
  exact (Soundness.denote_weaken model (rho entry) values value).trans (represented entry)

theorem index_denote {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (expression : I.IndexExpr context) :
    model.denote (HOL.subst rho (reading.indices.term expression)) values =
      realization.index (I.evalIndex expression environment) :=
  (realization.substituted_denote environment rho values represented _).trans
    (realization.index_correct expression environment)

theorem one_denote (values : model.Valuation Γ) :
    model.denote (weakenCtx Γ reading.one) values = realization.numbers 1 := by
  rw [model.denote_weakenCtx]
  exact realization.one_correct _

theorem count_denote {context : List I.SortCode} (name : String) (entry : Entry I)
    (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
    (environment : Env I.Value context)
    (sourceShape : entry.container.Shape (entry.evalOutput output environment))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values) :
    model.denote (.app (weaken (HOL.subst rho (reading.count name entry registered output))) (.var .vz))
      (model.extend values (realization.shape name entry registered _ sourceShape)) =
        realization.numbers ((ordered.containerOrdered name entry registered).positions sourceShape).length := by
  change model.denote (weaken (HOL.subst rho (reading.count name entry registered output)))
    (model.extend values (realization.shape name entry registered _ sourceShape)) _ = _
  rw [Soundness.denote_weaken, realization.substituted_denote environment rho values represented]
  exact realization.count_correct name entry registered output environment sourceShape

theorem compile_evaluate : ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ : Ctx Base} (environment : Env I.Value context) {index : I.Index}
    (sourceShape : Code.Shape code environment index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (_represented : realization.Represents environment rho values),
    OrderedPositionPrograms.evaluateFields model realization.numbers (reading.fields code) values
      (realization.encodeFields code sourceShape) (reading.compile code rho) =
      (Code.positionSegments ordered code sourceShape).map
        (fun segment => (segment.1, realization.index segment.2))
  | _, .result _, _, _, _, _, _, _, _ => rfl
  | _, .data sort body, _, environment, _, sourceShape, rho, values, represented => by
      simp only [Reading.fields, encodeFields, Code.positionSegments, Reading.compile]
      rw [Reading.bindPlan_evaluate]
      exact compile_evaluate body (sourceShape.1, environment) sourceShape.2 (Subst.lift rho)
        (model.extend values (realization.value sort sourceShape.1))
        (realization.represents_lift environment rho values represented sort sourceShape.1)
  | _, .recursive expression rest, _, environment, _, sourceShape, rho, values, represented => by
      change (realization.numbers.symm (applyValues model _
          (model.denote (Reading.ignoreFields _ (weakenCtx _ reading.one)) values)
          (realization.encodeFields rest sourceShape)),
        applyValues model _
          (model.denote (Reading.ignoreFields _ (HOL.subst rho (reading.indices.term expression))) values)
          (realization.encodeFields rest sourceShape)) :: _ =
        (1, realization.index (I.evalIndex expression environment)) :: _
      rw [Reading.ignoreFields_denote, Reading.ignoreFields_denote,
        realization.one_denote, Equiv.symm_apply_apply,
        realization.index_denote environment rho values represented expression]
      congr 1
      exact compile_evaluate rest environment sourceShape rho values represented
  | _, .nested name entry registered output childIndex rest, _, environment, _, sourceShape, rho, values, represented => by
      simp only [Reading.fields, encodeFields, Code.positionSegments, Reading.compile]
      rw [Reading.bindPlan_evaluate]
      change (realization.numbers.symm (applyValues model _
          (model.denote (Reading.ignoreFields _
            (.app (weaken (HOL.subst rho (reading.count name entry registered output))) (.var .vz)))
            (model.extend values (realization.shape name entry registered _ sourceShape.1)))
          (realization.encodeFields rest sourceShape.2)),
        applyValues model _
          (model.denote (Reading.ignoreFields _ (weaken (HOL.subst rho (reading.indices.term childIndex))))
            (model.extend values (realization.shape name entry registered _ sourceShape.1)))
          (realization.encodeFields rest sourceShape.2)) :: _ =
        (((ordered.containerOrdered name entry registered).positions sourceShape.1).length,
          realization.index (I.evalIndex childIndex environment)) :: _
      rw [Reading.ignoreFields_denote, Reading.ignoreFields_denote,
        realization.count_denote name entry registered output environment sourceShape.1 rho values represented,
        Equiv.symm_apply_apply, Soundness.denote_weaken,
        realization.index_denote environment rho values represented childIndex]
      congr 1
      exact compile_evaluate rest environment sourceShape.2 (fun entry => weaken (rho entry))
        (model.extend values (realization.shape name entry registered _ sourceShape.1))
        (realization.represents_weaken environment rho values represented _)

theorem resultProgram_denote : ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ : Ctx Base} (environment : Env I.Value context) {index : I.Index}
    (sourceShape : Code.Shape code environment index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (_represented : realization.Represents environment rho values),
    applyValues model (reading.fields code) (model.denote (reading.resultProgram code rho) values)
      (realization.encodeFields code sourceShape) = realization.index index
  | _, .result expression, _, environment, _, sourceShape, rho, values, represented => by
      exact (realization.index_denote environment rho values represented expression).trans
        (congrArg realization.index sourceShape.down.down)
  | _, .data sort body, _, environment, _, sourceShape, rho, values, represented =>
      resultProgram_denote body (sourceShape.1, environment) sourceShape.2 (Subst.lift rho)
        (model.extend values (realization.value sort sourceShape.1))
        (realization.represents_lift environment rho values represented sort sourceShape.1)
  | _, .recursive _ rest, _, environment, _, sourceShape, rho, values, represented =>
      resultProgram_denote rest environment sourceShape rho values represented
  | _, .nested name entry registered _ _ rest, _, environment, _, sourceShape, rho, values, represented =>
      resultProgram_denote rest environment sourceShape.2 (fun entry => weaken (rho entry))
        (model.extend values (realization.shape name entry registered _ sourceShape.1))
        (realization.represents_weaken environment rho values represented _)

/-- The generated graph reads the selected source position, including its
occurrence and child index. It is not a set-membership comparison. -/
theorem fieldGraph_exact (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    (full : model.FullDomains) (arithmeticValues : model.Valuation [])
    (zero_preserved : model.denote zero arithmeticValues = realization.numbers 0)
    (successor_preserved : ∀ n,
      model.denote successor arithmeticValues (realization.numbers n) = realization.numbers (n + 1))
    {context : List I.SortCode} (code : Code I registry parameters context)
    (environment : Env I.Value context) {index : I.Index} (sourceShape : Code.Shape code environment index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (slot : Nat) (target : Ty.denote model.Carrier reading.indices.index) :
    (Mettapedia.TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) (reading.fields code)
      (FiniteConstructorEncoding.handlerEquivalence model _
        (model.denote (OrderedPositionPrograms.fieldGraph zero successor (reading.fields code)
          (reading.compile code rho)) values (realization.numbers slot) target))
      (realization.encodeFields code sourceShape)).down ↔
      ∃ position, ((RecursiveSpaceRepresentation.codePresentation ordered code).coding sourceShape).decode slot =
        some position ∧ realization.index (Code.next code sourceShape position) = target := by
  rw [OrderedPositionPrograms.fieldGraph_denote zero successor model realization.numbers full arithmeticValues
    zero_preserved successor_preserved, Equiv.symm_apply_apply,
    realization.compile_evaluate code environment sourceShape rho values represented,
    Mettapedia.TypeTheory.OrderedPositionSegments.flatten_map, List.getElem?_map, Option.map_eq_some_iff]
  constructor
  · rintro ⟨childIndex, found, same⟩
    obtain ⟨position, decoded, child⟩ :=
      (Code.lookup_positionSegments ordered code sourceShape slot childIndex).mp found
    exact ⟨position, decoded, (congrArg realization.index child).trans same⟩
  · rintro ⟨position, decoded, same⟩
    exact ⟨Code.next code sourceShape position,
      (Code.lookup_positionSegments ordered code sourceShape slot _).mpr ⟨position, decoded, rfl⟩, same⟩

#print axioms compile_evaluate
#print axioms resultProgram_denote
#print axioms fieldGraph_exact

end Realization
end Mettapedia.Logic.HOL.IndexedContainerPositionTerms
