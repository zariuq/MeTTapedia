import Mettapedia.Logic.HOL.IndexedContainerFieldGuards

/-!
# Constructor inventories generated from registered-container codes

Field predicates, result functions and ordered position graphs use one source
constructor list and the same field telescope. Original list positions remain
constructor identities, including duplicate descriptions. The image theorems
retain primitive value/shape recognition and the source result-index equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.IndexedContainerPositionTerms

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.IndexedPositiveContainer
open CurriedPredicates FiniteConstructorEncoding IndexedConstructorGuards
universe u v w x
variable {I : Interface.{u}} {registry : Registry I} {Base : Type v}
  {Const : Ty Base → Type w} {parameters : Nat} {context : List I.SortCode} {Γ : Ctx Base}

def codeAt (reading : Reading I registry Const) (codes : List (Code I registry parameters context))
    (occurrence : Fin (codes.map reading.fields).length) : Code I registry parameters context :=
  codes.get ⟨occurrence.val, by simpa only [List.length_map] using occurrence.isLt⟩

theorem fields_get (reading : Reading I registry Const) (codes : List (Code I registry parameters context))
    (occurrence : Fin (codes.map reading.fields).length) :
    (codes.map reading.fields).get occurrence = reading.fields (codeAt reading codes occurrence) := by
  simp only [codeAt, List.get_eq_getElem, List.getElem_map]

namespace FieldGuards
variable {reading : Reading I registry Const} (guards : FieldGuards reading)

def constructors (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) : ConstructorPrograms Const Γ where
  fields := codes.map reading.fields
  number := reading.number
  index := reading.indices.index
  numeral := numeral
  allowed occurrence := (fields_get reading codes occurrence).symm ▸ guards.compile (codeAt reading codes occurrence) rho
  result occurrence := (fields_get reading codes occurrence).symm ▸ reading.resultProgram (codeAt reading codes occurrence) rho

def plans (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (occurrence : Fin (codes.map reading.fields).length) :
    OrderedPositionPrograms.FieldPlan Const Γ ((codes.map reading.fields).get occurrence)
      reading.number reading.indices.index :=
  (fields_get reading codes occurrence).symm ▸ reading.compile (codeAt reading codes occurrence) rho

def positions (codes : List (Code I registry parameters context))
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number)) :
    PositionPrograms (guards.constructors codes rho numeral) :=
  PositionPrograms.ofSegments (guards.constructors codes rho numeral) zero successor (plans codes rho)

end FieldGuards

private theorem holds_transport (model : HenkinModel.{v,w,x} Base Const)
    {first second : List (Ty Base)} (same : first = second)
    (condition : Term Const Γ (handlerType second)) (values : model.Valuation Γ)
    (data : Env (Ty.denote model.Carrier) first) :
    holds model first (same.symm ▸ condition) values data ↔
      holds model second condition values (same ▸ data) := by
  cases same
  rfl

private theorem result_transport (model : HenkinModel.{v,w,x} Base Const)
    {first second : List (Ty Base)} (same : first = second) {result : Ty Base}
    (function : Term Const Γ (FunctionType second result)) (values : model.Valuation Γ)
    (data : Env (Ty.denote model.Carrier) first) :
    applyValues model first (model.denote (same.symm ▸ function) values) data =
      applyValues model second (model.denote function values) (same ▸ data) := by
  cases same
  rfl

private theorem cast_back {first second : List (Ty Base)} (same : first = second)
    (Value : Ty Base → Type x) (data : Env Value second) :
    same ▸ (show Env Value first from same.symm ▸ data) = data := by
  cases same
  rfl

private theorem cast_eq_iff {first second : List (Ty Base)} (same : first = second)
    (Value : Ty Base → Type x) (source : Env Value second) (target : Env Value first) :
    (show Env Value first from same.symm ▸ source) = target ↔ source = same ▸ target := by
  cases same
  rfl

private theorem graph_transport (model : HenkinModel.{v,w,x} Base Const)
    {number index : Ty Base} (zero : ClosedTerm Const number)
    (successor : ClosedTerm Const (number ⇒ number))
    {first second : List (Ty Base)} (same : first = second)
    (plan : OrderedPositionPrograms.FieldPlan Const Γ second number index) (values : model.Valuation Γ)
    (slot : Ty.denote model.Carrier number) (target : Ty.denote model.Carrier index)
    (data : Env (Ty.denote model.Carrier) first) :
    (Mettapedia.TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) first
      (handlerEquivalence model first
        (model.denote (OrderedPositionPrograms.fieldGraph zero successor first (same.symm ▸ plan)) values slot target)) data).down ↔
    (Mettapedia.TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) second
      (handlerEquivalence model second
        (model.denote (OrderedPositionPrograms.fieldGraph zero successor second plan) values slot target)) (same ▸ data)).down := by
  cases same
  rfl

def encodeConstructorData {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
    {model : HenkinModel.{v,w,x} Base Const} (realization : Realization reading ordered model)
    (codes : List (Code I registry parameters context))
    (occurrence : Fin (codes.map reading.fields).length)
    {environment : Env I.Value context} {index : I.Index}
    (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index) :
    Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) (codes.map reading.fields) :=
  ⟨occurrence, (fields_get reading codes occurrence).symm ▸
    realization.encodeFields (codeAt reading codes occurrence) sourceShape⟩

namespace FieldImages
variable {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
  {model : HenkinModel.{v,w,x} Base Const} {realization : Realization reading ordered model}
  {guards : FieldGuards reading} (images : FieldImages realization guards)
include images

theorem inventory_allowed (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    (data : (guards.constructors codes rho numeral).Data model) :
    (guards.constructors codes rho numeral).dataAllowed model values data ↔
      ∃ (index : I.Index) (sourceShape : Code.Shape (codeAt reading codes data.1) environment index),
        realization.encodeFields (codeAt reading codes data.1) sourceShape = fields_get reading codes data.1 ▸ data.2 := by
  change holds model _ ((fields_get reading codes data.1).symm ▸
    guards.compile (codeAt reading codes data.1) rho) values data.2 ↔ _
  rw [holds_transport]
  exact images.compile_holds (codeAt reading codes data.1) environment rho values represented _

theorem inventory_result_image (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    (data : (guards.constructors codes rho numeral).Data model)
    (target : Ty.denote model.Carrier reading.indices.index) :
    ((guards.constructors codes rho numeral).dataAllowed model values data ∧
      (guards.constructors codes rho numeral).resultValue model values data = target) ↔
      ∃ (index : I.Index) (sourceShape : Code.Shape (codeAt reading codes data.1) environment index),
        realization.encodeFields (codeAt reading codes data.1) sourceShape = fields_get reading codes data.1 ▸ data.2 ∧
          realization.index index = target := by
  change (holds model _ ((fields_get reading codes data.1).symm ▸
    guards.compile (codeAt reading codes data.1) rho) values data.2 ∧
    applyValues model _ (model.denote ((fields_get reading codes data.1).symm ▸
      reading.resultProgram (codeAt reading codes data.1) rho) values) data.2 = target) ↔ _
  rw [holds_transport, result_transport]
  exact images.compile_result_image (codeAt reading codes data.1) environment rho values represented _ target

theorem inventory_at_index (index_injective : Function.Injective realization.index)
    (codes : List (Code I registry parameters context)) (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    (data : (guards.constructors codes rho numeral).Data model) (index : I.Index) :
    ((guards.constructors codes rho numeral).dataAllowed model values data ∧
      (guards.constructors codes rho numeral).resultValue model values data = realization.index index) ↔
      ∃ sourceShape : Code.Shape (codeAt reading codes data.1) environment index,
        realization.encodeFields (codeAt reading codes data.1) sourceShape = fields_get reading codes data.1 ▸ data.2 := by
  change (holds model _ ((fields_get reading codes data.1).symm ▸
    guards.compile (codeAt reading codes data.1) rho) values data.2 ∧
    applyValues model _ (model.denote ((fields_get reading codes data.1).symm ▸
      reading.resultProgram (codeAt reading codes data.1) rho) values) data.2 = realization.index index) ↔ _
  rw [holds_transport, result_transport]
  exact images.compile_at_index index_injective (codeAt reading codes data.1) environment rho values represented _ index

theorem encoded_data_allowed (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    (occurrence : Fin (codes.map reading.fields).length) {index : I.Index}
    (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index) :
    (guards.constructors codes rho numeral).dataAllowed model values
      (encodeConstructorData realization codes occurrence sourceShape) := by
  rw [images.inventory_allowed codes environment rho numeral values represented]
  refine ⟨index, sourceShape, ?_⟩
  exact (cast_back (fields_get reading codes occurrence) (Ty.denote model.Carrier) _).symm

omit images in
theorem encoded_data_result (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    (occurrence : Fin (codes.map reading.fields).length) {index : I.Index}
    (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index) :
    (guards.constructors codes rho numeral).resultValue model values
      (encodeConstructorData realization codes occurrence sourceShape) = realization.index index := by
  change applyValues model _ (model.denote ((fields_get reading codes occurrence).symm ▸
    reading.resultProgram (codeAt reading codes occurrence) rho) values)
    ((fields_get reading codes occurrence).symm ▸ realization.encodeFields (codeAt reading codes occurrence) sourceShape) = _
  rw [result_transport model (fields_get reading codes occurrence),
    cast_back (fields_get reading codes occurrence) (Ty.denote model.Carrier)]
  exact realization.resultProgram_denote (codeAt reading codes occurrence) environment sourceShape rho values represented

omit images in
theorem encoded_data_eq (codes : List (Code I registry parameters context))
    {environment : Env I.Value context} {index : I.Index}
    (data : Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote model.Carrier) (codes.map reading.fields))
    (sourceShape : Code.Shape (codeAt reading codes data.1) environment index)
    (same : realization.encodeFields (codeAt reading codes data.1) sourceShape = fields_get reading codes data.1 ▸ data.2) :
    encodeConstructorData realization codes data.1 sourceShape = data := by
  rcases data with ⟨occurrence, fields⟩
  apply congrArg (Sigma.mk occurrence)
  exact (cast_eq_iff (fields_get reading codes occurrence) (Ty.denote model.Carrier) _ _).mpr same

theorem payload_image (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (payload : Ty.denote model.Carrier (payloadType (codes.map reading.fields)))
    (target : Ty.denote model.Carrier reading.indices.index) :
    (∃ data : (guards.constructors codes rho numeral).Data model,
      ((guards.constructors codes rho numeral).dataAllowed model values data ∧
        (guards.constructors codes rho numeral).resultValue model values data = target) ∧
      payloadEquivalence model (codes.map reading.fields) payload =
        Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields) data) ↔
      ∃ (occurrence : Fin (codes.map reading.fields).length) (index : I.Index)
        (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index),
        realization.index index = target ∧
        payloadEquivalence model (codes.map reading.fields) payload =
          Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
            (encodeConstructorData realization codes occurrence sourceShape) := by
  constructor
  · rintro ⟨data, ⟨allowed, result⟩, payloadSame⟩
    obtain ⟨index, sourceShape, fieldsSame, indexSame⟩ :=
      (images.inventory_result_image codes environment rho numeral values represented data _).mp ⟨allowed, result⟩
    have restored := encoded_data_eq codes data sourceShape fieldsSame
    exact ⟨data.1, index, sourceShape, indexSame, by simpa only [restored] using payloadSame⟩
  · rintro ⟨occurrence, index, sourceShape, indexSame, payloadSame⟩
    refine ⟨encodeConstructorData realization codes occurrence sourceShape,
      ⟨images.encoded_data_allowed codes environment rho numeral values represented occurrence sourceShape, ?_⟩, payloadSame⟩
    exact (encoded_data_result codes environment rho numeral values represented occurrence sourceShape).trans indexSame

theorem resultGuard_exact (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (full : model.FullDomains)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (payload : Term Const Γ (payloadType (codes.map reading.fields)))
    (target : Term Const Γ reading.indices.index) :
    (model.denote ((guards.constructors codes rho numeral).resultGuard payload target) values).down ↔
      ∃ (occurrence : Fin (codes.map reading.fields).length) (index : I.Index)
        (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index),
        realization.index index = model.denote target values ∧
        payloadEquivalence model (codes.map reading.fields) (model.denote payload values) =
          Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
            (encodeConstructorData realization codes occurrence sourceShape) :=
  ((guards.constructors codes rho numeral).resultGuard_denote model full payload target values).trans
    (images.payload_image codes environment rho numeral values represented (model.denote payload values) (model.denote target values))

theorem resultProgram_exact (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (full : model.FullDomains)
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (payload : Ty.denote model.Carrier (payloadType (codes.map reading.fields)))
    (target : Ty.denote model.Carrier reading.indices.index) :
    (model.denote (guards.constructors codes rho numeral).resultProgram values payload target).down ↔
      ∃ (occurrence : Fin (codes.map reading.fields).length) (index : I.Index)
        (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index),
        realization.index index = target ∧
        payloadEquivalence model (codes.map reading.fields) payload =
          Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
            (encodeConstructorData realization codes occurrence sourceShape) :=
  ((guards.constructors codes rho numeral).resultProgram_denote model full values payload target).trans
    (images.payload_image codes environment rho numeral values represented payload target)

omit images in
theorem encoded_positions_exact (codes : List (Code I registry parameters context))
    (environment : Env I.Value context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (zero : ClosedTerm Const reading.number)
    (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    (full : model.FullDomains) (arithmeticValues : model.Valuation [])
    (zero_preserved : model.denote zero arithmeticValues = realization.numbers 0)
    (successor_preserved : ∀ n,
      model.denote successor arithmeticValues (realization.numbers n) = realization.numbers (n + 1))
    (values : model.Valuation Γ) (represented : realization.Represents environment rho values)
    (occurrence : Fin (codes.map reading.fields).length) {index : I.Index}
    (sourceShape : Code.Shape (codeAt reading codes occurrence) environment index)
    (slot : Nat) (target : Ty.denote model.Carrier reading.indices.index) :
    (guards.positions codes rho numeral zero successor).related model values
      (encodeConstructorData realization codes occurrence sourceShape) (realization.numbers slot) target ↔
      ∃ position, ((RecursiveSpaceRepresentation.codePresentation ordered (codeAt reading codes occurrence)).coding sourceShape).decode slot =
        some position ∧ realization.index (Code.next (codeAt reading codes occurrence) sourceShape position) = target := by
  change (Mettapedia.TypeTheory.FiniteConstructorEncoding.apply (Ty.denote model.Carrier) _
    (handlerEquivalence model _ (model.denote
      (OrderedPositionPrograms.fieldGraph zero successor _ ((fields_get reading codes occurrence).symm ▸
        reading.compile (codeAt reading codes occurrence) rho)) values (realization.numbers slot) target))
      ((fields_get reading codes occurrence).symm ▸ realization.encodeFields (codeAt reading codes occurrence) sourceShape)).down ↔ _
  rw [graph_transport model zero successor (fields_get reading codes occurrence),
    cast_back (fields_get reading codes occurrence) (Ty.denote model.Carrier)]
  exact realization.fieldGraph_exact zero successor full arithmeticValues zero_preserved successor_preserved
    (codeAt reading codes occurrence) environment sourceShape rho values represented slot target

#print axioms inventory_allowed
#print axioms inventory_at_index
#print axioms resultGuard_exact
#print axioms resultProgram_exact
#print axioms encoded_positions_exact

end FieldImages

abbrev ConstructorPoint (reading : Reading I registry Const)
    (codes : List (Code I registry parameters context)) (environment : Env I.Value context) :=
  Σ occurrence : Fin (codes.map reading.fields).length,
    Σ index : I.Index, Code.Shape (codeAt reading codes occurrence) environment index

namespace FieldInjective
variable {reading : Reading I registry Const} {ordered : registry.OrderedFinitary}
  {model : HenkinModel.{v,w,x} Base Const} {realization : Realization reading ordered model}
  (injections : FieldInjective realization)
include injections

theorem constructorData_injective (codes : List (Code I registry parameters context))
    (environment : Env I.Value context) :
    Function.Injective (fun point : ConstructorPoint reading codes environment =>
      encodeConstructorData realization codes point.1 point.2.2) := by
  intro first second same
  rcases first with ⟨firstOccurrence, first⟩
  rcases second with ⟨secondOccurrence, second⟩
  have occurrences : firstOccurrence = secondOccurrence := congrArg Sigma.fst same
  cases occurrences
  have fields :
      ((fields_get reading codes firstOccurrence).symm ▸ realization.encodeFields (codeAt reading codes firstOccurrence) first.2) =
        (show Env (Ty.denote model.Carrier) ((codes.map reading.fields).get firstOccurrence) from
          (fields_get reading codes firstOccurrence).symm ▸ realization.encodeFields (codeAt reading codes firstOccurrence) second.2) :=
    eq_of_heq (Sigma.mk.inj same).2
  have restored := congrArg
    (fun data : Env (Ty.denote model.Carrier) ((codes.map reading.fields).get firstOccurrence) =>
      (show Env (Ty.denote model.Carrier) (reading.fields (codeAt reading codes firstOccurrence)) from
        fields_get reading codes firstOccurrence ▸ data)) fields
  have sourceFields : realization.encodeFields (codeAt reading codes firstOccurrence) first.2 =
      realization.encodeFields (codeAt reading codes firstOccurrence) second.2 := by
    simpa only [cast_back (fields_get reading codes firstOccurrence) (Ty.denote model.Carrier)] using restored
  have points := injections.point_injective (codeAt reading codes firstOccurrence) environment sourceFields
  cases points
  rfl

theorem constructorPayload_injective (codes : List (Code I registry parameters context))
    (environment : Env I.Value context) :
    Function.Injective (fun point : ConstructorPoint reading codes environment =>
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
        (encodeConstructorData realization codes point.1 point.2.2)) :=
  (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective (Ty.denote model.Carrier) _).comp
    (injections.constructorData_injective codes environment)

#print axioms constructorPayload_injective
end FieldInjective
end Mettapedia.Logic.HOL.IndexedContainerPositionTerms
