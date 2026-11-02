import Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
import Mettapedia.TypeTheory.IndexedPolynomialConstructorClosure
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace
import Mettapedia.Logic.HOL.IndexedConstructorRootProofs
import Mettapedia.Logic.HOL.IndexedContainerInventoryRepresentation
import Mettapedia.TypeTheory.IndexedPositiveContainerInventoryAdapters

/-!
# Generated HOL carriers for admitted registered blocks

The original block's registered polynomial supplies its shapes and ordered
recursive slots. Its actual HOL payload encoding preserves constructor
occurrences, dependent data and nested container shapes. Primitive field and
constructor injectivity therefore derive a faithful generated representation
without assuming induction on the ambient HOL carrier.

The semantic inverse is noncomputable. No source reader, byte codec or native
implementation refinement is inferred from this representation theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description

universe u v w x
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
  (block : PositiveInductiveBlock.Admitted source I parameterCount context)
  (registered : block.WellRegistered)
  {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}

def encodedOccurrence (occurrence : Fin block.constructors.length) :
    Fin (((codes block registered).map reading.fields).length) :=
  ⟨occurrence.val, by simpa only [List.length_map, codes, List.length_ofFn] using occurrence.isLt⟩

theorem sourceOccurrence_encoded (occurrence : Fin block.constructors.length) :
    sourceOccurrence block registered reading (encodedOccurrence block registered (reading := reading) occurrence) = occurrence := rfl

def constructorPoint (environment : Env I.Value context)
    (point : Σ index, (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment index) :
    ConstructorPoint reading (codes block registered) environment := by
  refine ⟨encodedOccurrence block registered point.2.1, point.1, ?_⟩
  rw [codeAt_source]
  exact point.2.2

def sourcePoint (environment : Env I.Value context)
    (point : ConstructorPoint reading (codes block registered) environment) :
    Σ index, (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment index := by
  refine ⟨point.2.1, sourceOccurrence block registered reading point.1, ?_⟩
  rw [← codeAt_source block registered reading point.1]
  exact point.2.2

theorem sourcePoint_constructorPoint (environment : Env I.Value context)
    (point : Σ index, (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment index) :
    sourcePoint block registered environment (constructorPoint block registered (reading := reading) environment point) = point := by
  rcases point with ⟨index, occurrence, shape⟩
  simp only [sourcePoint, constructorPoint, sourceOccurrence_encoded]
  apply congrArg (Sigma.mk index)
  apply congrArg (Sigma.mk occurrence)
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

theorem constructorPoint_sourcePoint (environment : Env I.Value context)
    (point : ConstructorPoint reading (codes block registered) environment) :
    constructorPoint block registered environment (sourcePoint block registered environment point) = point := by
  rcases point with ⟨occurrence, index, shape⟩
  simp only [sourcePoint, constructorPoint, sourceOccurrence, encodedOccurrence]
  apply congrArg (Sigma.mk occurrence)
  apply congrArg (Sigma.mk index)
  exact eq_of_heq ((cast_heq _ _).trans (cast_heq _ _))

theorem constructorPoint_injective (environment : Env I.Value context) :
    Function.Injective (constructorPoint block registered (reading := reading) environment) :=
  Function.LeftInverse.injective (sourcePoint_constructorPoint block registered environment)

private theorem transport_heq {first second : Sort _} (same : first = second) (value : second) :
    HEq (same.mpr value) value := by
  cases same
  rfl

theorem constructorPoint_inventory_coherence (environment : Env I.Value context) (index : I.Index)
    (shape : (IndexedPositiveContainer.Inventory.polynomial (codes block registered)).Shape environment index) :
    constructorPoint block registered environment
      ⟨index,(IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index shape⟩ =
      IndexedContainerInventory.constructorPoint (codes block registered) (reading := reading) environment ⟨index,shape⟩ := by
  rcases shape with ⟨occurrence,data⟩
  simp only [constructorPoint,IndexedContainerInventory.constructorPoint,
    IndexedPositiveContainer.Inventory.blockSignatureEquiv]
  dsimp only [Equiv.sigmaCongr,Equiv.sigmaCongrRight,Equiv.sigmaCongrLeft,Equiv.trans,Equiv.cast]
  apply congrArg (Sigma.mk (IndexedContainerInventory.encodedOccurrence (codes block registered) occurrence))
  apply congrArg (Sigma.mk index)
  exact eq_of_heq ((transport_heq _ _).trans ((cast_heq _ data).trans (transport_heq _ data).symm))

def rootProof {assumptions : List (Formula Const Γ)} (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (children : Term Const Γ (reading.number ⇒ space))
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading (codes block registered) occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading (codes block registered) occurrence) rho arguments) :
    ProofSyntax Const assumptions ((inventory block registered guards rho numeral).rootIndex constructorCode
      ((inventory block registered guards rho numeral).constructorValue constructorCode occurrence
        (inventoryArguments reading (codes block registered) occurrence arguments) children)
      (reading.indexTerm (codeAt reading (codes block registered) occurrence) rho arguments)) :=
  IndexedContainerInventory.rootProof (codes block registered) guards rho numeral constructorCode children occurrence arguments evidence

theorem rootProof_free {assumptions : List (Formula Const Γ)} (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (children : Term Const Γ (reading.number ⇒ space))
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading (codes block registered) occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading (codes block registered) occurrence) rho arguments)
    (free : guards.EvidenceFree assumptions (codeAt reading (codes block registered) occurrence) rho arguments evidence) :
    (rootProof block registered guards rho numeral constructorCode children occurrence arguments evidence).FunctionExtensionalityFree :=
  IndexedContainerInventory.rootProof_free (codes block registered) guards rho numeral constructorCode children occurrence arguments evidence free

variable (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
  {model : HenkinModel.{v,w,x} Base Const}
  (realization : IndexedContainerPositionTerms.Realization reading (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) model)

def nativePayload (environment : Env I.Value context)
    (point : Σ index, (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment index) :
    Ty.denote model.Carrier (FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields)) :=
  (FiniteConstructorEncoding.payloadEquivalence model ((codes block registered).map reading.fields)).symm
    (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) ((codes block registered).map reading.fields)
      (encodeConstructorData realization (codes block registered)
        (constructorPoint block registered environment point).1
        (constructorPoint block registered environment point).2.2))

theorem nativePayload_inventory_coherence (environment : Env I.Value context) (index : I.Index)
    (shape : (IndexedPositiveContainer.Inventory.polynomial (codes block registered)).Shape environment index) :
    nativePayload block registered sourceOrder realization environment
      ⟨index,(IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index shape⟩ =
      IndexedContainerInventory.nativePayload (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        realization environment ⟨index,shape⟩ := by
  unfold nativePayload IndexedContainerInventory.nativePayload
  rw [constructorPoint_inventory_coherence]

theorem nativePayload_injective (injections : FieldInjective realization) (environment : Env I.Value context) :
    Function.Injective (nativePayload block registered sourceOrder realization environment) :=
  (FiniteConstructorEncoding.payloadEquivalence model ((codes block registered).map reading.fields)).symm.injective.comp
    ((injections.constructorPayload_injective (codes block registered) environment).comp
      (constructorPoint_injective block registered environment))

theorem payloadTerm_denote (environment : Env I.Value context)
    (point : ConstructorPoint reading (codes block registered) environment)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading (codes block registered) point.1)))
    (values : model.Valuation Γ)
    (fields : FiniteConstructorEncoding.denoteArguments model _ arguments values =
      realization.encodeFields (codeAt reading (codes block registered) point.1) point.2.2) :
    model.denote (payloadTerm reading (codes block registered) point.1 arguments) values =
      nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point) := by
  have actual := IndexedContainerInventory.payloadTerm_denote (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization environment point arguments values fields
  rw [IndexedContainerInventory.nativePayload_sourcePoint] at actual
  dsimp only [nativePayload]
  rw [constructorPoint_sourcePoint block registered environment point]
  exact actual

theorem nativePayload_sourcePoint (environment : Env I.Value context)
    (point : ConstructorPoint reading (codes block registered) environment) :
    nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point) =
      (FiniteConstructorEncoding.payloadEquivalence model ((codes block registered).map reading.fields)).symm
        (TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) ((codes block registered).map reading.fields)
          (encodeConstructorData realization (codes block registered) point.1 point.2.2)) := by
  dsimp only [nativePayload]
  rw [constructorPoint_sourcePoint block registered environment point]

theorem argumentIndex_denote
    (code : IndexedPositiveContainer.Code I (IndexedPositiveContainer.Unindexed.liftRegistry source I) parameterCount context)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (full : model.FullDomains) (environment : Env I.Value context) (values : model.Valuation Γ)
    (represented : realization.Represents environment rho values)
    {index : I.Index} (sourceShape : IndexedPositiveContainer.Code.Shape code environment index)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields code))
    (fields : FiniteConstructorEncoding.denoteArguments model _ arguments values = realization.encodeFields code sourceShape) :
    model.denote (reading.indexTerm code rho arguments) values = realization.index index :=
  IndexedContainerInventory.argumentIndex_denote (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
    realization code rho full environment values represented sourceShape arguments fields

variable {space : Ty Base}
  (bottomCode : Term Const Γ space)
  (constructorCode : Term Const Γ (reading.number ⇒
    FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
  (values : model.Valuation Γ)

def nativeConstructor : Nat →
    Ty.denote model.Carrier (FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields)) →
      (Nat → Ty.denote model.Carrier space) → Ty.denote model.Carrier space :=
  IndexedContainerInventory.nativeConstructor (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
    realization constructorCode values

noncomputable def nativeAlgebra :
    IndexedPolynomial.Algebra (IndexedPositiveContainer.Unindexed.blockPolynomial block registered)
      (fun _ _ => Ty.denote model.Carrier space) :=
  IndexedPolynomial.RecursiveSpaceRepresentation.constructorAlgebra
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder realization)
    (fun _ => model.denote bottomCode values)
    (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values)

theorem nativeAlgebra_inventory_coherence :
    IndexedContainerInventory.nativeAlgebra (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
      realization bottomCode constructorCode values =
      (IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).pullAlgebra
        (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) := by
  apply congrArg IndexedPolynomial.Algebra.mk
  funext environment index layer
  rcases layer with ⟨shape,children⟩
  dsimp only [IndexedContainerInventory.nativeAlgebra, nativeAlgebra, IndexedPolynomial.SignatureEquiv.pullAlgebra,
    IndexedPolynomial.RecursiveSpaceRepresentation.constructorAlgebra]
  simp only [IndexedPolynomial.SignatureEquiv.extensionEquiv_mk]
  have branches :
      ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).position shape).piCongr
        (fun position => Equiv.cast
          (congrArg (fun _ : I.Index => Ty.denote model.Carrier space)
            ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).next_preserved shape position).symm)) children =
        (fun position => children (((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).position shape).symm position)) := by
    funext position
    obtain ⟨original, rfl⟩ := ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).position shape).surjective position
    simp only [Equiv.piCongr_apply_apply, Equiv.cast_apply, cast_eq]
    exact congrArg children
      (((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).position shape).symm_apply_apply original).symm
  rw [branches]
  change nativeConstructor block registered sourceOrder realization constructorCode values
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        (codes block registered)).tag shape)
      (IndexedContainerInventory.nativePayload (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        realization environment ⟨index,shape⟩)
      (((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        (codes block registered)).coding shape).extend (model.denote bottomCode values) children) =
    nativeConstructor block registered sourceOrder realization constructorCode values
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).tag
        ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index shape))
      (nativePayload block registered sourceOrder realization environment
        ⟨index,(IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index shape⟩)
      (((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
        ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index shape)).extend
          (model.denote bottomCode values)
          (fun position => children (((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).position shape).symm position)))
  rw [IndexedPositiveContainer.Inventory.block_tag_coherence,nativePayload_inventory_coherence,
    IndexedPositiveContainer.Inventory.block_extend_coherence]
  rfl

theorem nativeGenerated_inventory_iff (environment : Env I.Value context) (index : I.Index)
    (value : Ty.denote model.Carrier space) :
    IndexedPolynomial.Algebra.Generated
      (IndexedContainerInventory.nativeAlgebra (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        realization bottomCode constructorCode values) environment index value ↔
    IndexedPolynomial.Algebra.Generated
      (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index value := by
  rw [nativeAlgebra_inventory_coherence]
  exact (IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).generated_pull_iff
    (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index value

theorem constructorRoot_inventory_iff (environment : Env I.Value context) (index : I.Index)
    (value : Ty.denote model.Carrier space) :
    IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        (codes block registered))
      (IndexedContainerInventory.nativePayload (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization)
      (fun _ => IndexedContainerInventory.nativeConstructor (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        realization constructorCode values) environment index value ↔
    IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
      (nativePayload block registered sourceOrder realization)
      (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment index value := by
  constructor
  · rintro ⟨shape, children, same⟩
    refine ⟨(IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index shape, children, ?_⟩
    rw [IndexedPositiveContainer.Inventory.block_tag_coherence, nativePayload_inventory_coherence]
    exact same
  · rintro ⟨shape, children, same⟩
    let original := ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index).symm shape
    have restored : (IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index original = shape :=
      ((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment index).apply_symm_apply shape
    refine ⟨original, children, ?_⟩
    rw [← restored, IndexedPositiveContainer.Inventory.block_tag_coherence, nativePayload_inventory_coherence] at same
    exact same

theorem rootMeaning_iff {guards : FieldGuards reading} (images : FieldImages realization guards)
    (index_injective : Function.Injective realization.index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (value : Ty.denote model.Carrier space) (index : I.Index) :
    (inventory block registered guards rho numeral).rootMeaning constructorCode model values value (realization.index index) ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
        (nativePayload block registered sourceOrder realization)
        (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values)
        environment index value := by
  exact (IndexedContainerInventory.rootMeaning_iff (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization constructorCode values images
    index_injective rho numeral numeral_meaning environment represented value index).trans
      (constructorRoot_inventory_iff block registered sourceOrder realization constructorCode values environment index value)

theorem compiledRoot_iff {guards : FieldGuards reading} (images : FieldImages realization guards)
    (index_injective : Function.Injective realization.index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) (full : model.FullDomains)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (valueCode : Term Const Γ space) (indexCode : Term Const Γ reading.indices.index)
    (index : I.Index) (index_meaning : model.denote indexCode values = realization.index index) :
    (model.denote ((inventory block registered guards rho numeral).rootIndex constructorCode valueCode indexCode) values).down ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
        (nativePayload block registered sourceOrder realization)
        (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values)
        environment index (model.denote valueCode values) := by
  rw [IndexedConstructorGuards.ConstructorPrograms.rootIndex_denote
    (inventory block registered guards rho numeral) constructorCode model full valueCode indexCode values, index_meaning]
  exact rootMeaning_iff block registered sourceOrder realization constructorCode values images index_injective
    rho numeral numeral_meaning environment represented _ index

theorem rootMeaning_index_image {guards : FieldGuards reading} (images : FieldImages realization guards)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (value : Ty.denote model.Carrier space) (target : Ty.denote model.Carrier reading.indices.index)
    (root : (inventory block registered guards rho numeral).rootMeaning constructorCode model values value target) :
    ∃ index, realization.index index = target := by
  exact IndexedContainerInventory.rootMeaning_index_image (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization constructorCode values images
    rho numeral environment represented value target root

theorem rootMeaning_arbitrary_iff {guards : FieldGuards reading} (images : FieldImages realization guards)
    (index_injective : Function.Injective realization.index)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (environment : Env I.Value context) (represented : realization.Represents environment rho values)
    (value : Ty.denote model.Carrier space) (target : Ty.denote model.Carrier reading.indices.index) :
    (inventory block registered guards rho numeral).rootMeaning constructorCode model values value target ↔
      ∃ index, realization.index index = target ∧
        IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
          (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
          (nativePayload block registered sourceOrder realization)
          (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment index value := by
  refine (IndexedContainerInventory.rootMeaning_arbitrary_iff (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization constructorCode values images
    index_injective rho numeral numeral_meaning environment represented value target).trans ?_
  exact exists_congr fun index => and_congr_right fun _ =>
    constructorRoot_inventory_iff block registered sourceOrder realization constructorCode values environment index value

def HOLShapeSeparation : Prop :=
  ∀ environment
    (first second : Σ index, (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Shape environment index)
    (children otherChildren : Ty.denote model.Carrier (reading.number ⇒ space)),
    model.denote constructorCode values
      (realization.numbers ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).tag first.2))
      (nativePayload block registered sourceOrder realization environment first) children =
        model.denote constructorCode values
          (realization.numbers ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).tag second.2))
          (nativePayload block registered sourceOrder realization environment second) otherChildren →
      nativePayload block registered sourceOrder realization environment first =
        nativePayload block registered sourceOrder realization environment second ∧ children = otherChildren

theorem HOLShapeSeparation.of_raw
    (raw : ∀ tag payload children otherTag otherPayload otherChildren,
      model.denote constructorCode values tag payload children =
        model.denote constructorCode values otherTag otherPayload otherChildren →
          payload = otherPayload ∧ children = otherChildren) :
    HOLShapeSeparation block registered sourceOrder realization constructorCode values := by
  intro environment first second children otherChildren same
  exact raw _ _ _ _ _ _ same

theorem HOLShapeSeparation.inventory
    (separation : HOLShapeSeparation block registered sourceOrder realization constructorCode values) :
    IndexedContainerInventory.HOLShapeSeparation (codes block registered)
      (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization constructorCode values := by
  intro environment first second children otherChildren
  have mapped := separation environment
    ⟨first.1,(IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment first.1 first.2⟩
    ⟨second.1,(IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment second.1 second.2⟩
    children otherChildren
  rw [IndexedPositiveContainer.Inventory.block_tag_coherence, IndexedPositiveContainer.Inventory.block_tag_coherence,
    nativePayload_inventory_coherence, nativePayload_inventory_coherence] at mapped
  exact mapped

variable (injections : FieldInjective realization)
  (constructor_fields : HOLShapeSeparation block registered sourceOrder realization constructorCode values)

include injections constructor_fields

omit injections in
theorem nativeConstructor_fields :
    IndexedPolynomial.RecursiveSpaceRepresentation.EncodedShapeSeparation
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
      (nativePayload block registered sourceOrder realization)
      (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) := by
  intro environment first second children otherChildren same
  obtain ⟨payloads, branches⟩ := constructor_fields environment first second _ _ same
  refine ⟨payloads, ?_⟩
  funext slot
  simpa only [Equiv.symm_apply_apply] using congrFun branches (realization.numbers slot)

theorem nativeAlgebra_injective (environment : Env I.Value context) (index : I.Index) :
    Function.Injective ((nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values).act environment index) := by
  apply IndexedPolynomial.RecursiveSpaceRepresentation.constructorAlgebra_injective
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder realization)
    (fun _ => model.denote bottomCode values)
    (fun _ tag payload children => model.denote constructorCode values (realization.numbers tag) payload
      (fun slot => children (realization.numbers.symm slot)))
    (nativePayload_injective block registered sourceOrder realization injections)
  exact nativeConstructor_fields block registered sourceOrder realization constructorCode values constructor_fields

theorem nativeLayer_injective (environment : Env I.Value context) :
    Function.Injective (fun layer : Σ index, (IndexedPositiveContainer.Unindexed.blockPolynomial block registered).Extension
      (fun _ _ => Ty.denote model.Carrier space) environment index =>
      (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values).act environment layer.1 layer.2) :=
  IndexedPolynomial.RecursiveSpaceRepresentation.constructorLayer_injective
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
    (nativePayload block registered sourceOrder realization) (fun _ => model.denote bottomCode values)
    (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values)
    (nativePayload_injective block registered sourceOrder realization injections)
    (nativeConstructor_fields block registered sourceOrder realization constructorCode values constructor_fields) environment

theorem nativeGenerated_index_unique (environment : Env I.Value context)
    (value : Ty.denote model.Carrier space) (first second : I.Index)
    (firstGenerated : IndexedPolynomial.Algebra.Generated
      (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment first value)
    (secondGenerated : IndexedPolynomial.Algebra.Generated
      (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment second value) : first = second := by
  exact IndexedContainerInventory.nativeGenerated_index_unique (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization bottomCode constructorCode values injections
    (HOLShapeSeparation.inventory block registered sourceOrder realization constructorCode values constructor_fields)
    environment value first second
    ((nativeGenerated_inventory_iff block registered sourceOrder realization bottomCode constructorCode values
      environment first value).mpr firstGenerated)
    ((nativeGenerated_inventory_iff block registered sourceOrder realization bottomCode constructorCode values
      environment second value).mpr secondGenerated)

noncomputable def nativeGeneratedRepresentation :
    IndexedPolynomial.Algebra.Representation (IndexedPositiveContainer.Unindexed.blockPolynomial block registered)
      (IndexedPolynomial.Algebra.generatedAlgebra
        (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values)) :=
  IndexedPolynomial.Algebra.generatedRepresentation _
    (IndexedPolynomial.Algebra.generatedAlgebra_injective _
      (nativeAlgebra_injective block registered sourceOrder realization bottomCode constructorCode values
        injections constructor_fields))

noncomputable def generatedBlockEquivalence (environment : Env I.Value context) (index : I.Index) :
    block.Family environment index ≃
      IndexedPolynomial.Algebra.GeneratedCarrier
        (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index :=
  (IndexedPositiveContainer.Unindexed.blockFamilyEquiv block registered environment index).trans
    ((nativeGeneratedRepresentation block registered sourceOrder realization bottomCode constructorCode values
      injections constructor_fields).toEquiv environment index)

theorem generatedBlockEquivalence_recursor (environment : Env I.Value context) (index : I.Index)
    (tree : block.Family environment index) :
    ((generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
      injections constructor_fields environment index) tree).val =
      block.recursor ((IndexedPositiveContainer.Unindexed.blockSignatureEquiv block registered).pullAlgebra
        (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values)) environment index tree :=
  (IndexedPositiveContainer.Unindexed.blockSignatureEquiv block registered).fold_toFix
    (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index tree

theorem generatedBlockEncoding_injective (environment : Env I.Value context) :
    Function.Injective (fun tree : Σ index, block.Family environment index =>
      ((generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
        injections constructor_fields environment tree.1) tree.2).val) := by
  rintro ⟨firstIndex, first⟩ ⟨secondIndex, second⟩ same
  change ((generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
    injections constructor_fields environment firstIndex) first).val =
      ((generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
        injections constructor_fields environment secondIndex) second).val at same
  have indices := nativeGenerated_index_unique block registered sourceOrder realization bottomCode constructorCode values
    injections constructor_fields environment _ firstIndex secondIndex
    ((generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
      injections constructor_fields environment firstIndex) first).property
    (same.symm ▸ ((generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
      injections constructor_fields environment secondIndex) second).property)
  cases indices
  apply congrArg (Sigma.mk firstIndex)
  exact (generatedBlockEquivalence block registered sourceOrder realization bottomCode constructorCode values
    injections constructor_fields environment firstIndex).injective (Subtype.ext same)

#print axioms nativePayload_injective
#print axioms nativeAlgebra_injective
#print axioms nativeGeneratedRepresentation
#print axioms nativeGenerated_index_unique
#print axioms generatedBlockEquivalence
#print axioms payloadTerm_denote
#print axioms argumentIndex_denote
#print axioms compiledRoot_iff
#print axioms rootMeaning_iff
#print axioms rootMeaning_arbitrary_iff
#print axioms rootProof
#print axioms rootProof_free
#print axioms nativeLayer_injective
#print axioms generatedBlockEquivalence_recursor
#print axioms generatedBlockEncoding_injective

end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
