import Mettapedia.Logic.HOL.IndexedContainerPositionTerms
import Mettapedia.Logic.HOL.Syntax.Prefixes

/-!
# Generated field-image guards for registered constructor descriptions

Primitive predicates recognize the chosen images of source values and nested
container shapes. The compiler combines them along the original telescope.
Nested shape fields do not extend the source index environment. Recognition
of the complete field tuple is a theorem of this structural compilation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates FiniteConstructorEncoding
universe u v w x
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
  {Const : Ty Base → Type w} {parameters : Nat} {Γ : Ctx Base}

structure FieldGuards (reading : Reading I registry Const) where
  value : (sort : I.SortCode) → Term Const reading.indices.parameters (reading.indices.sort sort ⇒ .prop)
  shape : {context : List I.SortCode} → (name : String) → (entry : Entry I) →
    (registered : registry.lookup name = some entry) → entry.OutputExpr context →
    Term Const (context.map reading.indices.sort ++ reading.indices.parameters)
      (reading.shapeType name entry registered ⇒ .prop)

namespace Reading
def parameterSubst (reading : Reading I registry Const) {context : List I.SortCode}
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ) :
    Subst Const reading.indices.parameters Γ :=
  fun entry => rho (Rename.weakenPrefix (context.map reading.indices.sort) entry)
end Reading

namespace FieldGuards
variable {reading : Reading I registry Const} (guards : FieldGuards reading)

def compile : {context : List I.SortCode} → (code : Code I registry parameters context) →
    {Γ : Ctx Base} → Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ →
    Term Const Γ (handlerType (reading.fields code))
  | _, .result _, _, _ => .top
  | context, .data sort body, _, rho =>
      .lam (conjoin (reading.fields body)
        (constant (reading.fields body)
          (.app (weaken (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort))) (.var .vz)))
        (compile body (Subst.lift rho)))
  | _, .recursive _ rest, _, rho => compile rest rho
  | _, .nested name entry registered output _ rest, _, rho =>
      .lam (conjoin (reading.fields rest)
        (constant (reading.fields rest)
          (.app (weaken (HOL.subst rho (guards.shape name entry registered output))) (.var .vz)))
        (compile rest (fun entry => weaken (rho entry))))

end FieldGuards

namespace Realization
variable {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
  {model : HenkinModel.{v,w,x} Base Const} (realization : Realization reading ordered model)

theorem parameter_valuation : ∀ {context : List I.SortCode} (environment : Env I.Value context)
    {type : Ty Base} (entry : Var reading.indices.parameters type),
    (reading.indices.valuation model realization.value realization.parameterValues environment)
      (Rename.weakenPrefix (context.map reading.indices.sort) entry) = realization.parameterValues entry
  | [], _, _, _ => rfl
  | _ :: rest, environment, _, entry => parameter_valuation (context := rest) environment.2 entry

theorem parameterSubst_denote {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    {type : Ty Base} (term : Term Const reading.indices.parameters type) :
    model.denote (HOL.subst (reading.parameterSubst (context := context) rho) term) values =
      model.denote term realization.parameterValues := by
  rw [Soundness.denote_subst]
  apply congrArg (model.denote term)
  funext type entry
  exact (represented (Rename.weakenPrefix (context.map reading.indices.sort) entry)).trans
    (realization.parameter_valuation environment entry)
end Realization

/-- Exactness premises concern only primitive value and shape predicates.
Injectivity is separate from image recognition. -/
structure FieldImages {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
    {model : HenkinModel.{v,w,x} Base Const} (realization : Realization reading ordered model)
    (guards : FieldGuards reading) where
  value_correct : ∀ (sort : I.SortCode) (target : Ty.denote model.Carrier (reading.indices.sort sort)),
    (model.denote (guards.value sort) realization.parameterValues target).down ↔
      ∃ source : I.Value sort, realization.value sort source = target
  shape_correct : ∀ {context} (name : String) (entry : Entry I)
    (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
    (environment : Env I.Value context) (target : Ty.denote model.Carrier (reading.shapeType name entry registered)),
    (model.denote (guards.shape name entry registered output)
      (reading.indices.valuation model realization.value realization.parameterValues environment) target).down ↔
      ∃ source : entry.container.Shape (entry.evalOutput output environment),
        realization.shape name entry registered _ source = target

namespace FieldImages
variable {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
  {model : HenkinModel.{v,w,x} Base Const} {realization : Realization reading ordered model}
  {guards : FieldGuards reading} (images : FieldImages realization guards)
include images

theorem value_at (sort : I.SortCode) {context : List I.SortCode} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (target : Ty.denote model.Carrier (reading.indices.sort sort)) :
    (model.denote (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort)) values target).down ↔
      ∃ source : I.Value sort, realization.value sort source = target := by
  rw [realization.parameterSubst_denote environment rho values represented]
  exact images.value_correct sort target

theorem shape_at {context : List I.SortCode} (name : String) (entry : Entry I)
    (registered : registry.lookup name = some entry) (output : entry.OutputExpr context)
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (target : Ty.denote model.Carrier (reading.shapeType name entry registered)) :
    (model.denote (HOL.subst rho (guards.shape name entry registered output)) values target).down ↔
      ∃ source : entry.container.Shape (entry.evalOutput output environment),
        realization.shape name entry registered _ source = target := by
  rw [realization.substituted_denote environment rho values represented]
  exact images.shape_correct name entry registered output environment target

/-- The complete image is derived from the primitive image laws, including
the dependency of each later field on the earlier source data. -/
theorem compile_holds : ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    {Γ : Ctx Base} (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (_represented : realization.Represents environment rho values)
    (data : Env (Ty.denote model.Carrier) (reading.fields code)),
    holds model (reading.fields code) (guards.compile code rho) values data ↔
      ∃ (index : I.Index) (sourceShape : Code.Shape code environment index),
        realization.encodeFields code sourceShape = data
  | _, .result expression, _, environment, _, _, _, data => by
      cases data
      constructor
      · intro _
        exact ⟨I.evalIndex expression environment, ⟨⟨rfl⟩⟩, rfl⟩
      · intro _
        exact True.intro
  | context, .data sort body, _, environment, rho, values, represented, data => by
      change Env (Ty.denote model.Carrier) (reading.indices.sort sort :: reading.fields body) at data
      rcases data with ⟨first, rest⟩
      change holds model (reading.fields body)
        (conjoin (reading.fields body)
          (constant (reading.fields body)
            (.app (weaken (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort))) (.var .vz)))
          (guards.compile body (Subst.lift rho))) (model.extend values first) rest ↔ _
      rw [conjoin_holds, constant_holds]
      change (model.denote (weaken (HOL.subst (reading.parameterSubst (context := context) rho) (guards.value sort)))
        (model.extend values first) first).down ∧ _ ↔ _
      rw [Soundness.denote_weaken, images.value_at sort environment rho values represented first]
      constructor
      · rintro ⟨⟨source, same⟩, bodyValid⟩
        have valid : holds model (reading.fields body) (guards.compile body (Subst.lift rho))
            (model.extend values (realization.value sort source)) rest := by
          simpa only [same] using bodyValid
        obtain ⟨index, sourceShape, encoded⟩ :=
          (compile_holds body (source, environment) (Subst.lift rho)
            (model.extend values (realization.value sort source))
            (realization.represents_lift environment rho values represented sort source) rest).mp valid
        exact ⟨index, ⟨source, sourceShape⟩, Prod.ext same encoded⟩
      · rintro ⟨index, ⟨source, sourceShape⟩, same⟩
        change (realization.value sort source, realization.encodeFields body sourceShape) = (first, rest) at same
        have firstSame : realization.value sort source = first := congrArg Prod.fst same
        have restSame : realization.encodeFields body sourceShape = rest := congrArg Prod.snd same
        refine ⟨⟨source, firstSame⟩, ?_⟩
        have valid := (compile_holds body (source, environment) (Subst.lift rho)
          (model.extend values (realization.value sort source))
          (realization.represents_lift environment rho values represented sort source) rest).mpr
            ⟨index, sourceShape, restSame⟩
        simpa only [firstSame] using valid
  | _, .recursive _ rest, _, environment, rho, values, represented, data =>
      compile_holds rest environment rho values represented data
  | _, .nested name entry registered output _ rest, _, environment, rho, values, represented, data => by
      change Env (Ty.denote model.Carrier) (reading.shapeType name entry registered :: reading.fields rest) at data
      rcases data with ⟨first, tail⟩
      change holds model (reading.fields rest)
        (conjoin (reading.fields rest)
          (constant (reading.fields rest)
            (.app (weaken (HOL.subst rho (guards.shape name entry registered output))) (.var .vz)))
          (guards.compile rest (fun entry => weaken (rho entry)))) (model.extend values first) tail ↔ _
      rw [conjoin_holds, constant_holds]
      change (model.denote (weaken (HOL.subst rho (guards.shape name entry registered output)))
        (model.extend values first) first).down ∧ _ ↔ _
      rw [Soundness.denote_weaken, images.shape_at name entry registered output environment rho values represented]
      rw [compile_holds rest environment (fun entry => weaken (rho entry)) (model.extend values first)
        (realization.represents_weaken environment rho values represented first) tail]
      constructor
      · rintro ⟨⟨source, same⟩, index, sourceShape, encoded⟩
        exact ⟨index, ⟨source, sourceShape⟩, Prod.ext same encoded⟩
      · rintro ⟨index, ⟨source, sourceShape⟩, same⟩
        change (realization.shape name entry registered _ source, realization.encodeFields rest sourceShape) =
          (first, tail) at same
        exact ⟨⟨source, congrArg Prod.fst same⟩, index, sourceShape, congrArg Prod.snd same⟩

theorem compile_result_image {context : List I.SortCode} (code : Code I registry parameters context)
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (data : Env (Ty.denote model.Carrier) (reading.fields code))
    (target : Ty.denote model.Carrier reading.indices.index) :
    (holds model (reading.fields code) (guards.compile code rho) values data ∧
      applyValues model (reading.fields code) (model.denote (reading.resultProgram code rho) values) data = target) ↔
      ∃ (index : I.Index) (sourceShape : Code.Shape code environment index),
        realization.encodeFields code sourceShape = data ∧ realization.index index = target := by
  constructor
  · rintro ⟨allowed, result⟩
    obtain ⟨index, sourceShape, encoded⟩ := (images.compile_holds code environment rho values represented data).mp allowed
    have actual := realization.resultProgram_denote code environment sourceShape rho values represented
    rw [encoded] at actual
    exact ⟨index, sourceShape, encoded, actual.symm.trans result⟩
  · rintro ⟨index, sourceShape, encoded, same⟩
    refine ⟨(images.compile_holds code environment rho values represented data).mpr ⟨index, sourceShape, encoded⟩, ?_⟩
    have actual := realization.resultProgram_denote code environment sourceShape rho values represented
    rw [encoded] at actual
    exact actual.trans same

/-- Index reflection uses index injectivity only. No source field or shape
injectivity is needed for this existential image theorem. -/
theorem compile_at_index (index_injective : Function.Injective realization.index)
    {context : List I.SortCode} (code : Code I registry parameters context)
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (data : Env (Ty.denote model.Carrier) (reading.fields code)) (index : I.Index) :
    (holds model (reading.fields code) (guards.compile code rho) values data ∧
      applyValues model (reading.fields code) (model.denote (reading.resultProgram code rho) values) data = realization.index index) ↔
      ∃ sourceShape : Code.Shape code environment index, realization.encodeFields code sourceShape = data := by
  rw [images.compile_result_image code environment rho values represented data]
  constructor
  · rintro ⟨other, sourceShape, encoded, same⟩
    have indices := index_injective same
    subst other
    exact ⟨sourceShape, encoded⟩
  · rintro ⟨sourceShape, encoded⟩
    exact ⟨index, sourceShape, encoded, rfl⟩

theorem empty_index_refused (index_injective : Function.Injective realization.index)
    {context : List I.SortCode} (code : Code I registry parameters context)
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (data : Env (Ty.denote model.Carrier) (reading.fields code)) (index : I.Index)
    (empty : IsEmpty (Code.Shape code environment index)) :
    ¬ (holds model (reading.fields code) (guards.compile code rho) values data ∧
      applyValues model (reading.fields code) (model.denote (reading.resultProgram code rho) values) data = realization.index index) := by
  intro accepted
  obtain ⟨sourceShape, _⟩ := (images.compile_at_index index_injective code environment rho values represented data index).mp accepted
  exact empty.false sourceShape

#print axioms compile_holds
#print axioms compile_at_index

end FieldImages

/-- Optional reflection of source data and shapes. Image recognition above
does not require these injectivity premises. -/
structure FieldInjective {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
    {model : HenkinModel.{v,w,x} Base Const} (realization : Realization reading ordered model) where
  value : ∀ sort, Function.Injective (realization.value sort)
  shape : ∀ name entry registered output,
    Function.Injective (realization.shape name entry registered output)

namespace FieldInjective
variable {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
  {model : HenkinModel.{v,w,x} Base Const} {realization : Realization reading ordered model}
  (injections : FieldInjective realization)
include injections

theorem encodeFields_heq : ∀ {context : List I.SortCode} (code : Code I registry parameters context)
    {environment : Env I.Value context} {firstIndex secondIndex : I.Index}
    (first : Code.Shape code environment firstIndex) (second : Code.Shape code environment secondIndex),
    realization.encodeFields code first = realization.encodeFields code second →
      firstIndex = secondIndex ∧ HEq first second
  | _, .result _, _, _, _, first, second, _ => by
      have same := first.down.down.symm.trans second.down.down
      cases same
      rcases first with ⟨⟨_⟩⟩
      rcases second with ⟨⟨_⟩⟩
      exact ⟨rfl, HEq.rfl⟩
  | _, .data sort body, _, _, _, first, second, same => by
      rcases first with ⟨firstValue, firstShape⟩
      rcases second with ⟨secondValue, secondShape⟩
      change (realization.value sort firstValue, realization.encodeFields body firstShape) =
        (realization.value sort secondValue, realization.encodeFields body secondShape) at same
      have values := injections.value sort (congrArg Prod.fst same)
      cases values
      obtain ⟨indices, shapes⟩ := encodeFields_heq body firstShape secondShape (congrArg Prod.snd same)
      cases indices
      have sameShape := eq_of_heq shapes
      cases sameShape
      exact ⟨rfl, HEq.rfl⟩
  | _, .recursive _ rest, _, _, _, first, second, same => encodeFields_heq rest first second same
  | _, .nested name entry registered output _ rest, environment, _, _, first, second, same => by
      rcases first with ⟨firstShape, firstRest⟩
      rcases second with ⟨secondShape, secondRest⟩
      change (realization.shape name entry registered _ firstShape, realization.encodeFields rest firstRest) =
        (realization.shape name entry registered _ secondShape, realization.encodeFields rest secondRest) at same
      have shapes := injections.shape name entry registered (entry.evalOutput output environment) (congrArg Prod.fst same)
      cases shapes
      obtain ⟨indices, rests⟩ := encodeFields_heq rest firstRest secondRest (congrArg Prod.snd same)
      cases indices
      have sameRest := eq_of_heq rests
      cases sameRest
      exact ⟨rfl, HEq.rfl⟩

theorem point_injective {context : List I.SortCode} (code : Code I registry parameters context)
    (environment : Env I.Value context) :
    Function.Injective (fun point : Σ index : I.Index, Code.Shape code environment index =>
      realization.encodeFields code point.2) := by
  intro first second same
  obtain ⟨indices, shapes⟩ := injections.encodeFields_heq code first.2 second.2 same
  exact Sigma.ext indices shapes

#print axioms point_injective
end FieldInjective
end Mettapedia.Logic.HOL.IndexedContainerPositionTerms
