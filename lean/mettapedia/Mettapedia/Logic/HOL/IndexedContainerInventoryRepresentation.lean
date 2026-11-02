import Mettapedia.Logic.HOL.IndexedContainerFieldProofs
import Mettapedia.TypeTheory.IndexedPositiveContainerInventory
import Mettapedia.TypeTheory.IndexedPolynomialConstructorClosure
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace
import Mettapedia.Logic.HOL.IndexedConstructorRootProofs

/-!
# HOL representations of complete indexed constructor inventories

One ordered list of actual indexed container codes supplies shapes, fields,
positions and result indices. Primitive field images and constructor separation
derive a generated representation in the chosen HOL model. Container output
expressions retain earlier source data, including dependent Vector lengths.

The inverse is semantic and noncomputable. Source declaration admission,
object-language formation and native implementation refinement remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedContainerInventory

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description

universe u v w x y
variable {I : Interface.{u}} {registry : IndexedPositiveContainer.Registry I} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
  (codes : List (IndexedPositiveContainer.Code I registry parameterCount context))
  {reading : Reading I registry Const}

private theorem transport_heq {first second : Sort y} (same : first = second) (value : second) :
    HEq (same.mpr value) value := by
  cases same
  rfl

def sourceOccurrence (reading : Reading I registry Const)
    (occurrence : Fin (codes.map reading.fields).length) : Fin codes.length :=
  ⟨occurrence.val,by simpa only [List.length_map] using occurrence.isLt⟩

theorem codeAt_source (reading : Reading I registry Const)
    (occurrence : Fin (codes.map reading.fields).length) :
    codeAt reading codes occurrence = codes.get (sourceOccurrence codes reading occurrence) := rfl

def encodedOccurrence (occurrence : Fin codes.length) :
    Fin ((codes.map reading.fields).length) :=
  ⟨occurrence.val, by simpa only [List.length_map] using occurrence.isLt⟩

theorem sourceOccurrence_encoded (occurrence : Fin codes.length) :
    sourceOccurrence codes reading (encodedOccurrence codes (reading := reading) occurrence) = occurrence := rfl

def constructorPoint (environment : Env I.Value context)
    (point : Σ index, (IndexedPositiveContainer.Inventory.polynomial codes).Shape environment index) :
    ConstructorPoint reading codes environment := by
  refine ⟨encodedOccurrence codes point.2.1, point.1, ?_⟩
  rw [codeAt_source]
  exact point.2.2

def sourcePoint (environment : Env I.Value context)
    (point : ConstructorPoint reading codes environment) :
    Σ index, (IndexedPositiveContainer.Inventory.polynomial codes).Shape environment index := by
  refine ⟨point.2.1, sourceOccurrence codes reading point.1, ?_⟩
  rw [← codeAt_source codes reading point.1]
  exact point.2.2

theorem sourcePoint_constructorPoint (environment : Env I.Value context)
    (point : Σ index, (IndexedPositiveContainer.Inventory.polynomial codes).Shape environment index) :
    sourcePoint codes environment (constructorPoint codes (reading := reading) environment point) = point := by
  rcases point with ⟨index, occurrence, shape⟩
  simp only [sourcePoint, constructorPoint, sourceOccurrence_encoded]
  apply congrArg (Sigma.mk index)
  apply congrArg (Sigma.mk occurrence)
  exact eq_of_heq ((transport_heq _ _).trans (transport_heq _ _))

theorem constructorPoint_sourcePoint (environment : Env I.Value context)
    (point : ConstructorPoint reading codes environment) :
    constructorPoint codes environment (sourcePoint codes environment point) = point := by
  rcases point with ⟨occurrence, index, shape⟩
  simp only [sourcePoint, constructorPoint, sourceOccurrence, encodedOccurrence]
  apply congrArg (Sigma.mk occurrence)
  apply congrArg (Sigma.mk index)
  exact eq_of_heq ((transport_heq _ _).trans (transport_heq _ _))

theorem constructorPoint_injective (environment : Env I.Value context) :
    Function.Injective (constructorPoint codes (reading := reading) environment) :=
  Function.LeftInverse.injective (sourcePoint_constructorPoint codes environment)

private theorem applyFields_transport {first second : List (Ty Base)} (same : first = second)
    {result : Ty Base} (function : Term Const Γ (CurriedPredicates.FunctionType second result))
    (arguments : FiniteConstructorEncoding.Arguments Const Γ second) :
    CurriedPredicates.applyFields first (same.symm ▸ function) (same.symm ▸ arguments) =
      CurriedPredicates.applyFields second function arguments := by
  cases same
  rfl

def rootProof {assumptions : List (Formula Const Γ)} (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (children : Term Const Γ (reading.number ⇒ space))
    (occurrence : Fin (codes.map reading.fields).length)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments) :
    ProofSyntax Const assumptions ((guards.constructors codes rho numeral).rootIndex constructorCode
      ((guards.constructors codes rho numeral).constructorValue constructorCode occurrence
        (inventoryArguments reading codes occurrence arguments) children)
      (reading.indexTerm (codeAt reading codes occurrence) rho arguments)) := by
  apply IndexedConstructorGuards.ConstructorPrograms.rootIndex_intro
    (guards.constructors codes rho numeral) constructorCode occurrence
    (inventoryArguments reading codes occurrence arguments) children _
    (guards.inventoryFieldProof codes rho numeral occurrence arguments evidence)
  apply ProofSyntax.castIndices rfl ?_
    (reading.resultProof (codeAt reading codes occurrence) rho arguments)
  simp only [FieldGuards.constructors, inventoryArguments]
  rw [applyFields_transport (fields_get reading codes occurrence)
    (reading.resultProgram (codeAt reading codes occurrence) rho) arguments]

theorem rootProof_free {assumptions : List (Formula Const Γ)} (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (children : Term Const Γ (reading.number ⇒ space))
    (occurrence : Fin (codes.map reading.fields).length)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading codes occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading codes occurrence) rho arguments)
    (free : guards.EvidenceFree assumptions (codeAt reading codes occurrence) rho arguments evidence) :
    (rootProof codes guards rho numeral constructorCode children occurrence arguments evidence).FunctionExtensionalityFree := by
  unfold rootProof
  apply IndexedConstructorGuards.ConstructorPrograms.rootIndex_intro_free
  · exact guards.inventoryFieldProof_free _ _ _ _ _ _ free
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact reading.resultProof_free _ _ _

variable (ordered : registry.OrderedFinitary)
  {model : HenkinModel.{v,w,x} Base Const}
  (realization : IndexedContainerPositionTerms.Realization reading (ordered) model)

def nativePayload (environment : Env I.Value context)
    (point : Σ index, (IndexedPositiveContainer.Inventory.polynomial codes).Shape environment index) :
    Ty.denote model.Carrier (FiniteConstructorEncoding.payloadType (codes.map reading.fields)) :=
  (FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).symm
    (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
      (encodeConstructorData realization codes
        (constructorPoint codes environment point).1
        (constructorPoint codes environment point).2.2))

theorem nativePayload_injective (injections : FieldInjective realization) (environment : Env I.Value context) :
    Function.Injective (nativePayload codes ordered realization environment) :=
  (FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).symm.injective.comp
    ((injections.constructorPayload_injective codes environment).comp
      (constructorPoint_injective codes environment))

private theorem denoteArguments_transport {first second : List (Ty Base)} (same : first = second)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ second) (values : model.Valuation Γ) :
    FiniteConstructorEncoding.denoteArguments model first (same.symm ▸ arguments) values =
      (show Env (Ty.denote model.Carrier) first from
        same.symm ▸ FiniteConstructorEncoding.denoteArguments model second arguments values) := by
  cases same
  rfl

theorem payloadTerm_denote (environment : Env I.Value context)
    (point : ConstructorPoint reading codes environment)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading codes point.1)))
    (values : model.Valuation Γ)
    (fields : FiniteConstructorEncoding.denoteArguments model _ arguments values =
      realization.encodeFields (codeAt reading codes point.1) point.2.2) :
    model.denote (payloadTerm reading codes point.1 arguments) values =
      nativePayload codes ordered realization environment (sourcePoint codes environment point) := by
  apply (FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).injective
  rw [payloadTerm, FiniteConstructorEncoding.encode_denote]
  simp only [nativePayload, Equiv.apply_symm_apply]
  rw [constructorPoint_sourcePoint codes environment point]
  apply congrArg (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) _)
  apply congrArg (Sigma.mk point.1)
  change FiniteConstructorEncoding.denoteArguments model _
    ((fields_get reading codes point.1).symm ▸ arguments) values = _
  rw [denoteArguments_transport (fields_get reading codes point.1) arguments values]
  exact congrArg (fun data => (fields_get reading codes point.1).symm ▸ data) fields

theorem nativePayload_sourcePoint (environment : Env I.Value context)
    (point : ConstructorPoint reading codes environment) :
    nativePayload codes ordered realization environment (sourcePoint codes environment point) =
      (FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).symm
        (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
          (encodeConstructorData realization codes point.1 point.2.2)) := by
  dsimp only [nativePayload]
  rw [constructorPoint_sourcePoint codes environment point]

theorem argumentIndex_denote
    (code : IndexedPositiveContainer.Code I (registry) parameterCount context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (full : model.FullDomains) (environment : Env I.Value context) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    {index : I.Index} (sourceShape : IndexedPositiveContainer.Code.Shape code environment index)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields code))
    (fields : FiniteConstructorEncoding.denoteArguments model _ arguments values = realization.encodeFields code sourceShape) :
    model.denote (reading.indexTerm code rho arguments) values = realization.index index := by
  have compared := Soundness.extDerivation_sound
    (reading.resultProof (assumptions := []) code rho arguments).erase (M := model) (ρ := values)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ _; exact full _ _)
    (by intro _ impossible; nomatch impossible)
  change model.Eqv _ (model.denote (CurriedPredicates.applyFields _ (reading.resultProgram code rho) arguments) values)
    (model.denote (reading.indexTerm code rho arguments) values) at compared
  rw [model.eqv_iff_eq_of_fullDomains full, CurriedPredicates.applyFields_denote, fields] at compared
  exact compared.symm.trans (realization.resultProgram_denote code environment sourceShape rho values represented)

variable {space : Ty Base}
  (bottomCode : Term Const Γ space)
  (constructorCode : Term Const Γ (reading.number ⇒
    FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
  (values : model.Valuation Γ)

def nativeConstructor : Nat →
    Ty.denote model.Carrier (FiniteConstructorEncoding.payloadType (codes.map reading.fields)) →
      (Nat → Ty.denote model.Carrier space) → Ty.denote model.Carrier space :=
  fun tag payload children => model.denote constructorCode values (realization.numbers tag) payload
    (fun slot => children (realization.numbers.symm slot))

noncomputable def nativeAlgebra :
    IndexedPolynomial.Algebra (IndexedPositiveContainer.Inventory.polynomial codes)
      (fun _ _ => Ty.denote model.Carrier space) :=
  IndexedPolynomial.RecursiveSpaceRepresentation.constructorAlgebra
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
    (nativePayload codes ordered realization)
    (fun _ => model.denote bottomCode values)
    (fun _ => nativeConstructor codes ordered realization constructorCode values)

theorem rootMeaning_iff {guards : FieldGuards reading} (images : FieldImages realization guards)
    (index_injective : Function.Injective realization.index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (value : Ty.denote model.Carrier space) (index : I.Index) :
    (guards.constructors codes rho numeral).rootMeaning constructorCode model values value (realization.index index) ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
        (nativePayload codes ordered realization)
        (fun _ => nativeConstructor codes ordered realization constructorCode values)
        environment index value := by
  constructor
  · rintro ⟨data, allowed, result, children, equation⟩
    obtain ⟨sourceShape, fields⟩ := (images.inventory_at_index index_injective codes
      environment rho numeral values represented data index).mp ⟨allowed, result⟩
    let point : ConstructorPoint reading codes environment := ⟨data.1, index, sourceShape⟩
    have restored := FieldImages.encoded_data_eq (realization := realization)
      codes data sourceShape fields
    refine ⟨(sourcePoint codes environment point).2,
      (fun n => children (realization.numbers n)), ?_⟩
    change value =
      nativeConstructor codes ordered realization constructorCode values data.1.val
        (nativePayload codes ordered realization environment (sourcePoint codes environment point))
        (fun n => children (realization.numbers n))
    dsimp only [nativeConstructor]
    rw [nativePayload_sourcePoint codes ordered realization environment point]
    change value = model.denote constructorCode values
      (realization.numbers data.1.val)
      ((FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).symm
        (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields)
          (encodeConstructorData realization codes data.1 sourceShape)))
      (fun slot => children (realization.numbers (realization.numbers.symm slot)))
    rw [restored]
    simp only [Equiv.apply_symm_apply]
    rw [← numeral_meaning data.1.val]
    exact equation
  · rintro ⟨shape, children, equation⟩
    let point := constructorPoint codes (reading := reading) environment ⟨index, shape⟩
    let data := encodeConstructorData realization codes point.1 point.2.2
    refine ⟨data, images.encoded_data_allowed codes environment rho numeral values represented
      point.1 point.2.2, ?_, (fun slot => children (realization.numbers.symm slot)), ?_⟩
    · exact (FieldImages.encoded_data_result (realization := realization) codes
        environment rho numeral values represented point.1 point.2.2)
    · change value = model.denote constructorCode values
        (model.denote (numeral point.1.val) values)
        ((FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).symm
          (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields) data))
        (fun slot => children (realization.numbers.symm slot))
      rw [numeral_meaning]
      exact equation

theorem compiledRoot_iff {guards : FieldGuards reading} (images : FieldImages realization guards)
    (index_injective : Function.Injective realization.index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (full : model.FullDomains)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (valueCode : Term Const Γ space) (indexCode : Term Const Γ reading.indices.index)
    (index : I.Index) (index_meaning : model.denote indexCode values = realization.index index) :
    (model.denote ((guards.constructors codes rho numeral).rootIndex constructorCode valueCode indexCode) values).down ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
        (nativePayload codes ordered realization)
        (fun _ => nativeConstructor codes ordered realization constructorCode values)
        environment index (model.denote valueCode values) := by
  rw [IndexedConstructorGuards.ConstructorPrograms.rootIndex_denote
    (guards.constructors codes rho numeral) constructorCode model full valueCode indexCode values, index_meaning]
  exact rootMeaning_iff codes ordered realization constructorCode values images index_injective
    rho numeral numeral_meaning environment represented _ index

theorem rootMeaning_index_image {guards : FieldGuards reading} (images : FieldImages realization guards)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (value : Ty.denote model.Carrier space) (target : Ty.denote model.Carrier reading.indices.index)
    (root : (guards.constructors codes rho numeral).rootMeaning constructorCode model values value target) :
    ∃ index, realization.index index = target := by
  obtain ⟨data, allowed, result, _, _⟩ := root
  obtain ⟨index, _, _, same⟩ := (images.inventory_result_image codes
    environment rho numeral values represented data target).mp ⟨allowed, result⟩
  exact ⟨index, same⟩

theorem rootMeaning_arbitrary_iff {guards : FieldGuards reading} (images : FieldImages realization guards)
    (index_injective : Function.Injective realization.index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (value : Ty.denote model.Carrier space) (target : Ty.denote model.Carrier reading.indices.index) :
    (guards.constructors codes rho numeral).rootMeaning constructorCode model values value target ↔
      ∃ index, realization.index index = target ∧
        IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
          (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
          (nativePayload codes ordered realization)
          (fun _ => nativeConstructor codes ordered realization constructorCode values) environment index value := by
  constructor
  · intro root
    obtain ⟨index, same⟩ := rootMeaning_index_image codes ordered realization constructorCode values images
      rho numeral environment represented value target root
    refine ⟨index, same, (rootMeaning_iff codes ordered realization constructorCode values images
      index_injective rho numeral numeral_meaning environment represented value index).mp ?_⟩
    simpa only [same] using root
  · rintro ⟨index, same, root⟩
    have interpreted := (rootMeaning_iff codes ordered realization constructorCode values images
      index_injective rho numeral numeral_meaning environment represented value index).mpr root
    simpa only [same] using interpreted

def HOLShapeSeparation : Prop :=
  ∀ environment
    (first second : Σ index, (IndexedPositiveContainer.Inventory.polynomial codes).Shape environment index)
    (children otherChildren : Ty.denote model.Carrier (reading.number ⇒ space)),
    model.denote constructorCode values
      (realization.numbers ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).tag first.2))
      (nativePayload codes ordered realization environment first) children =
        model.denote constructorCode values
          (realization.numbers ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).tag second.2))
          (nativePayload codes ordered realization environment second) otherChildren →
      nativePayload codes ordered realization environment first =
        nativePayload codes ordered realization environment second ∧ children = otherChildren

theorem HOLShapeSeparation.of_raw
    (raw : ∀ tag payload children otherTag otherPayload otherChildren,
      model.denote constructorCode values tag payload children =
        model.denote constructorCode values otherTag otherPayload otherChildren →
          payload = otherPayload ∧ children = otherChildren) :
    HOLShapeSeparation codes ordered realization constructorCode values := by
  intro environment first second children otherChildren same
  exact raw _ _ _ _ _ _ same

variable (injections : FieldInjective realization)
  (constructor_fields : HOLShapeSeparation codes ordered realization constructorCode values)

include injections constructor_fields

omit injections in
theorem nativeConstructor_fields :
    IndexedPolynomial.RecursiveSpaceRepresentation.EncodedShapeSeparation
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
      (nativePayload codes ordered realization)
      (fun _ => nativeConstructor codes ordered realization constructorCode values) := by
  intro environment first second children otherChildren same
  obtain ⟨payloads, branches⟩ := constructor_fields environment first second _ _ same
  refine ⟨payloads, ?_⟩
  funext slot
  simpa only [Equiv.symm_apply_apply] using congrFun branches (realization.numbers slot)

theorem nativeAlgebra_injective (environment : Env I.Value context) (index : I.Index) :
    Function.Injective ((nativeAlgebra codes ordered realization bottomCode constructorCode values).act environment index) := by
  apply IndexedPolynomial.RecursiveSpaceRepresentation.constructorAlgebra_injective
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
    (nativePayload codes ordered realization)
    (fun _ => model.denote bottomCode values)
    (fun _ tag payload children => model.denote constructorCode values (realization.numbers tag) payload
      (fun slot => children (realization.numbers.symm slot)))
    (nativePayload_injective codes ordered realization injections)
  exact nativeConstructor_fields codes ordered realization constructorCode values constructor_fields

theorem nativeLayer_injective (environment : Env I.Value context) :
    Function.Injective (fun layer : Σ index, (IndexedPositiveContainer.Inventory.polynomial codes).Extension
      (fun _ _ => Ty.denote model.Carrier space) environment index =>
      (nativeAlgebra codes ordered realization bottomCode constructorCode values).act environment layer.1 layer.2) :=
  IndexedPolynomial.RecursiveSpaceRepresentation.constructorLayer_injective
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
    (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
    (fun _ => nativeConstructor codes ordered realization constructorCode values)
    (nativePayload_injective codes ordered realization injections)
    (nativeConstructor_fields codes ordered realization constructorCode values constructor_fields) environment

theorem nativeGenerated_index_unique (environment : Env I.Value context)
    (value : Ty.denote model.Carrier space) (first second : I.Index)
    (firstGenerated : IndexedPolynomial.Algebra.Generated
      (nativeAlgebra codes ordered realization bottomCode constructorCode values) environment first value)
    (secondGenerated : IndexedPolynomial.Algebra.Generated
      (nativeAlgebra codes ordered realization bottomCode constructorCode values) environment second value) : first = second := by
  apply IndexedPolynomial.RecursiveSpaceRepresentation.constructorRoot_unique
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
    (nativePayload codes ordered realization)
    (fun _ => nativeConstructor codes ordered realization constructorCode values)
    (nativePayload_injective codes ordered realization injections)
    (nativeConstructor_fields codes ordered realization constructorCode values constructor_fields)
    environment value first second
  · exact IndexedPolynomial.RecursiveSpaceRepresentation.generated_constructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
      (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
      (fun _ => nativeConstructor codes ordered realization constructorCode values)
      environment first value firstGenerated
  · exact IndexedPolynomial.RecursiveSpaceRepresentation.generated_constructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
      (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
      (fun _ => nativeConstructor codes ordered realization constructorCode values)
      environment second value secondGenerated

noncomputable def nativeGeneratedRepresentation :
    IndexedPolynomial.Algebra.Representation (IndexedPositiveContainer.Inventory.polynomial codes)
      (IndexedPolynomial.Algebra.generatedAlgebra
        (nativeAlgebra codes ordered realization bottomCode constructorCode values)) :=
  IndexedPolynomial.Algebra.generatedRepresentation _
    (IndexedPolynomial.Algebra.generatedAlgebra_injective _
      (nativeAlgebra_injective codes ordered realization bottomCode constructorCode values
        injections constructor_fields))

#print axioms nativePayload_injective
#print axioms nativeAlgebra_injective
#print axioms nativeGeneratedRepresentation
#print axioms nativeGenerated_index_unique
#print axioms payloadTerm_denote
#print axioms argumentIndex_denote
#print axioms compiledRoot_iff
#print axioms rootMeaning_iff
#print axioms rootMeaning_arbitrary_iff
#print axioms rootProof
#print axioms rootProof_free
#print axioms nativeLayer_injective

end Mettapedia.Logic.HOL.IndexedContainerInventory
