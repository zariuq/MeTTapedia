import Mettapedia.GSLT.LanguageDef.AdmittedContainerGenerated
import Mettapedia.Logic.HOL.ContextualRecursiveSpacePredicate
import Mettapedia.Logic.HOL.IndexedContainerInventoryPredicate

/-!
# Compiled recursive predicates for admitted constructor families

The actual shape, activity and child-edge programs share their encoded data
witness. Their source positions retain the selected order and child index.
Open HOL parameters remain in the contextual positive operator.
These are semantic Henkin correspondences. Retained constructor and induction
programs for complete membership and external native checking remain separate
consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description

universe u v w x
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
  (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
  (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
  {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
  {model : HenkinModel.{v,w,x} Base Const}
  (realization : IndexedContainerPositionTerms.Realization reading (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) model)
  {guards : FieldGuards reading} (images : FieldImages realization guards)
  (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
  (numeral : Nat → Term Const Γ reading.number)
  (values : model.Valuation Γ) (environment : Env I.Value context)
  (represented : realization.Represents environment rho values)

private theorem sourcePoint_inventory_coherence
    (point : ConstructorPoint reading (codes block registered) environment) :
    sourcePoint block registered environment point =
      ⟨(IndexedContainerInventory.sourcePoint (codes block registered) environment point).1,
        (IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).shape environment
        (IndexedContainerInventory.sourcePoint (codes block registered) environment point).1
        (IndexedContainerInventory.sourcePoint (codes block registered) environment point).2⟩ := by
  apply constructorPoint_injective block registered environment
  rw [constructorPoint_sourcePoint, constructorPoint_inventory_coherence]
  exact (IndexedContainerInventory.constructorPoint_sourcePoint (codes block registered) environment point).symm

private theorem nativePayload_sourcePoint_inventory
    (point : ConstructorPoint reading (codes block registered) environment) :
    nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point) =
      IndexedContainerInventory.nativePayload (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        realization environment (IndexedContainerInventory.sourcePoint (codes block registered) environment point) := by
  rw [sourcePoint_inventory_coherence, nativePayload_inventory_coherence]

private theorem sourcePoint_decoded_iff
    (point : ConstructorPoint reading (codes block registered) environment) (slot : Nat) (property : I.Index → Prop) :
    (∃ position,
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
        (sourcePoint block registered environment point).2).decode slot = some position ∧
      property ((IndexedPositiveContainer.Unindexed.blockPolynomial block registered).next
        (sourcePoint block registered environment point).2 position)) ↔
    ∃ position,
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
        (codes block registered)).coding (IndexedContainerInventory.sourcePoint (codes block registered) environment point).2).decode slot = some position ∧
      property ((IndexedPositiveContainer.Inventory.polynomial (codes block registered)).next
        (IndexedContainerInventory.sourcePoint (codes block registered) environment point).2 position) := by
  rw [sourcePoint_inventory_coherence, IndexedPositiveContainer.Inventory.block_decoded_iff]
  apply exists_congr
  intro position
  apply and_congr_right
  intro _
  rw [IndexedPolynomial.SignatureEquiv.next_preserved]
  rfl

private theorem sourcePoint_canonical_iff
    (point : ConstructorPoint reading (codes block registered) environment)
    {Target : Type _} (default : Target) (children : Nat → Target) :
    ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      (sourcePoint block registered environment point).2).Canonical default children ↔
    ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
      (codes block registered)).coding (IndexedContainerInventory.sourcePoint (codes block registered) environment point).2).Canonical default children := by
  rw [sourcePoint_inventory_coherence, IndexedPositiveContainer.Inventory.block_canonical_iff]
  rfl

theorem nativePayload_matches (point : ConstructorPoint reading (codes block registered) environment)
    (data : (inventory block registered guards rho numeral).Data model) :
    FiniteConstructorEncoding.payloadEquivalence model ((codes block registered).map reading.fields)
      (nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point)) =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) ((codes block registered).map reading.fields) data ↔
        encodeConstructorData realization (codes block registered) point.1 point.2.2 = data := by
  rw [nativePayload_sourcePoint_inventory]
  exact IndexedContainerInventory.nativePayload_matches (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization (guards := guards) rho numeral environment point data

include images represented

theorem shapeProgram_exact (full : model.FullDomains)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (tag : Ty.denote model.Carrier reading.number)
    (payload : Ty.denote model.Carrier (FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields))) :
    (model.denote (inventory block registered guards rho numeral).shapeProgram values tag payload).down ↔
      ∃ point : ConstructorPoint reading (codes block registered) environment,
        tag = realization.numbers point.1.val ∧
        nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point) = payload := by
  have checked := IndexedContainerInventory.shapeProgram_exact (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    full numeral_meaning tag payload
  apply checked.trans
  exact exists_congr fun point => and_congr_right fun _ => by rw [nativePayload_sourcePoint_inventory]

variable (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
  (full : model.FullDomains) (arithmeticValues : model.Valuation [])
  (zero_meaning : model.denote zero arithmeticValues = realization.numbers 0)
  (successor_meaning : ∀ n, model.denote successor arithmeticValues (realization.numbers n) = realization.numbers (n+1))

include full zero_meaning successor_meaning

omit images in
theorem sourcePoint_positions (point : ConstructorPoint reading (codes block registered) environment)
    (slot : Nat) (target : Ty.denote model.Carrier reading.indices.index) :
    (guards.positions (codes block registered) rho numeral zero successor).related model values
      (encodeConstructorData realization (codes block registered) point.1 point.2.2) (realization.numbers slot) target ↔
      ∃ position,
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
          (sourcePoint block registered environment point).2).decode slot = some position ∧
        realization.index ((IndexedPositiveContainer.Unindexed.blockPolynomial block registered).next
          (sourcePoint block registered environment point).2 position) = target := by
  exact (IndexedContainerInventory.sourcePoint_positions (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning point slot target).trans
    (sourcePoint_decoded_iff block registered sourceOrder environment point slot
      (fun index => realization.index index = target)).symm

theorem activeProgram_exact (point : ConstructorPoint reading (codes block registered) environment) (slot : Nat) :
    (model.denote (guards.positions (codes block registered) rho numeral zero successor).activeProgram values
      (nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point))
      (realization.numbers slot)).down ↔
      ∃ position,
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
          (sourcePoint block registered environment point).2).decode slot = some position := by
  rw [nativePayload_sourcePoint_inventory]
  have checked := IndexedContainerInventory.activeProgram_exact (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning point slot
  apply checked.trans
  simpa only [and_true] using (sourcePoint_decoded_iff block registered sourceOrder environment point slot (fun _ => True)).symm

theorem edgeProgram_exact (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (point : ConstructorPoint reading (codes block registered) environment) (slot : Nat)
    (child : Ty.denote model.Carrier space) :
    (model.denote ((guards.positions (codes block registered) rho numeral zero successor).edgeProgram constructorCode) values
      (nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point))
      (realization.numbers slot) child).down ↔
      ∃ position,
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
          (sourcePoint block registered environment point).2).decode slot = some position ∧
        IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
          (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
          (nativePayload block registered sourceOrder realization)
          (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment
          ((IndexedPositiveContainer.Unindexed.blockPolynomial block registered).next
            (sourcePoint block registered environment point).2 position) child := by
  rw [nativePayload_sourcePoint_inventory]
  have checked := IndexedContainerInventory.edgeProgram_exact (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning index_injective numeral_meaning constructorCode point slot child
  have compared := sourcePoint_decoded_iff block registered sourceOrder environment point slot
    (fun index => IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
      (nativePayload block registered sourceOrder realization)
      (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment index child)
  refine checked.trans (Iff.trans ?_ compared.symm)
  exact exists_congr fun position => and_congr_right fun _ =>
    constructorRoot_inventory_iff block registered sourceOrder realization constructorCode values environment _ child

variable {space : Ty Base} (bottomCode : Term Const Γ space)
  (constructorCode : Term Const Γ (reading.number ⇒
    FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))

def recursiveSignature : RecursiveSpacePredicate.Contextual Const Γ :=
  IndexedContainerInventory.recursiveSignature (codes block registered) (guards := guards)
    rho numeral zero successor bottomCode constructorCode

theorem operator_point_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (predicate : Ty.denote model.Carrier (space ⇒ .prop)) (value : Ty.denote model.Carrier space) :
    (model.denote (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
      values predicate value).down ↔
      ∃ (point : ConstructorPoint reading (codes block registered) environment) (children : Nat → Ty.denote model.Carrier space),
        value = nativeConstructor block registered sourceOrder realization constructorCode values point.1.val
          (nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point)) children ∧
        (∀ slot position,
          ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
            (sourcePoint block registered environment point).2).decode slot = some position →
          IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
            (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
            (nativePayload block registered sourceOrder realization)
            (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment
            ((IndexedPositiveContainer.Unindexed.blockPolynomial block registered).next
              (sourcePoint block registered environment point).2 position) (children slot) ∧ (predicate (children slot)).down) ∧
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
          (sourcePoint block registered environment point).2).Canonical (model.denote bottomCode values) children := by
  have checked := IndexedContainerInventory.operator_point_iff (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode index_injective numeral_meaning predicate value
  refine checked.trans (exists_congr fun point => exists_congr fun children => ?_)
  apply and_congr
  · rw [nativePayload_sourcePoint_inventory]
    rfl
  · apply and_congr
    · symm
      rw [sourcePoint_inventory_coherence]
      apply forall_congr'
      intro slot
      rw [IndexedPositiveContainer.Inventory.block_forall_decoded_iff]
      apply forall_congr'
      intro position
      apply imp_congr_right
      intro _
      rw [IndexedPolynomial.SignatureEquiv.next_preserved]
      exact and_congr (constructorRoot_inventory_iff block registered sourceOrder realization constructorCode values
        environment _ (children slot)).symm Iff.rfl
    · exact (sourcePoint_canonical_iff block registered sourceOrder environment point (model.denote bottomCode values) children).symm

theorem operator_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (predicate : Ty.denote model.Carrier (space ⇒ .prop)) (value : Ty.denote model.Carrier space) :
    (model.denote (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
      values predicate value).down ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.GuardedConstructorStep
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
        (nativePayload block registered sourceOrder realization) (fun _ => model.denote bottomCode values)
        (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values)
        environment (fun child => (predicate child).down) value := by
  rw [operator_point_iff block registered sourceOrder realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode index_injective numeral_meaning]
  constructor
  · rintro ⟨point, children, equation, conditions, canonical⟩
    exact ⟨point.2.1, (sourcePoint block registered environment point).2, children, equation, conditions, canonical⟩
  · rintro ⟨index, shape, children, equation, conditions, canonical⟩
    let point := constructorPoint block registered (reading := reading) environment ⟨index, shape⟩
    refine ⟨point, children, ?_, ?_, ?_⟩
    · dsimp only [point]
      rw [sourcePoint_constructorPoint block registered environment ⟨index, shape⟩]
      exact equation
    · dsimp only [point]
      rw [sourcePoint_constructorPoint block registered environment ⟨index, shape⟩]
      exact conditions
    · dsimp only [point]
      rw [sourcePoint_constructorPoint block registered environment ⟨index, shape⟩]
      exact canonical

variable (injections : FieldInjective realization)
  (constructor_fields : HOLShapeSeparation block registered sourceOrder realization constructorCode values)
include injections constructor_fields

theorem least_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (value : Ty.denote model.Carrier space) :
    (model.denote (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).least
      values value).down ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorFamily
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
        (nativePayload block registered sourceOrder realization) (fun _ => model.denote bottomCode values)
        (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment value := by
  have checked := IndexedContainerInventory.least_iff (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections
    (constructor_fields.inventory block registered sourceOrder realization constructorCode values)
    index_injective numeral_meaning value
  apply checked.trans
  change (∃ index, IndexedPolynomial.Algebra.Generated
      (IndexedContainerInventory.nativeAlgebra (codes block registered)
        (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization bottomCode constructorCode values)
      environment index value) ↔
    ∃ index, IndexedPolynomial.Algebra.Generated
      (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index value
  apply exists_congr
  intro index
  exact nativeGenerated_inventory_iff block registered sourceOrder realization bottomCode constructorCode values
    environment index value

def memberProgram : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop) :=
  IndexedContainerInventory.memberProgram (codes block registered) (guards := guards)
    rho numeral zero successor bottomCode constructorCode

omit injections constructor_fields zero_meaning successor_meaning in
theorem memberProgram_index_image (value : Ty.denote model.Carrier space)
    (target : Ty.denote model.Carrier reading.indices.index)
    (member : (model.denote (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value target).down) : ∃ index, realization.index index = target := by
  exact IndexedContainerInventory.memberProgram_index_image (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full bottomCode constructorCode value target member

omit injections constructor_fields zero_meaning successor_meaning in
theorem memberProgram_junk_index_refused (value : Ty.denote model.Carrier space)
    (target : Ty.denote model.Carrier reading.indices.index)
    (outside : ∀ index, realization.index index ≠ target) :
    ¬ (model.denote (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value target).down := by
  intro member
  obtain ⟨index, same⟩ := memberProgram_index_image block registered sourceOrder realization images rho numeral values
    environment represented zero successor full bottomCode constructorCode value target member
  exact outside index same

theorem memberProgram_denote (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (value : Ty.denote model.Carrier space) (index : I.Index) :
    (model.denote (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value (realization.index index)).down ↔
      IndexedPolynomial.Algebra.Generated
        (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index value := by
  have checked := IndexedContainerInventory.memberProgram_denote (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections
    (constructor_fields.inventory block registered sourceOrder realization constructorCode values)
    index_injective numeral_meaning value index
  exact checked.trans (nativeGenerated_inventory_iff block registered sourceOrder realization bottomCode constructorCode values
    environment index value)

theorem memberProgram_arbitrary_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (value : Ty.denote model.Carrier space) (target : Ty.denote model.Carrier reading.indices.index) :
    (model.denote (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value target).down ↔
      ∃ index, realization.index index = target ∧
        IndexedPolynomial.Algebra.Generated
          (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index value := by
  refine (IndexedContainerInventory.memberProgram_arbitrary_iff (codes block registered)
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections
    (constructor_fields.inventory block registered sourceOrder realization constructorCode values)
    index_injective numeral_meaning value target).trans ?_
  exact exists_congr fun index => and_congr_right fun _ =>
    nativeGenerated_inventory_iff block registered sourceOrder realization bottomCode constructorCode values environment index value

noncomputable def nativeFamilyEquivalence (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n) (index : I.Index) :
    block.Family environment index ≃
      {value : Ty.denote model.Carrier space //
        (model.denote (memberProgram block registered (guards := guards) rho numeral zero successor bottomCode constructorCode)
          values value (realization.index index)).down} := by
  exact (IndexedPositiveContainer.Unindexed.blockFamilyEquiv block registered environment index).trans
    (((IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered).fixEquiv environment index).symm.trans
      (IndexedContainerInventory.nativeFamilyEquivalence (codes block registered)
        (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) realization images rho numeral values environment represented
        zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections
        (constructor_fields.inventory block registered sourceOrder realization constructorCode values)
        index_injective numeral_meaning index))

theorem nativeFamilyEquivalence_recursor (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (index : I.Index) (tree : block.Family environment index) :
    ((nativeFamilyEquivalence block registered sourceOrder realization images rho numeral values environment represented
      zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections constructor_fields
      index_injective numeral_meaning index) tree).val =
      block.recursor ((IndexedPositiveContainer.Unindexed.blockSignatureEquiv block registered).pullAlgebra
        (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values)) environment index tree := by
  let comparison := IndexedPositiveContainer.Inventory.blockSignatureEquiv block registered
  let sourceTree := IndexedPositiveContainer.Unindexed.blockFamilyEquiv block registered environment index tree
  have transported := comparison.fold_toFix
    (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index
    (comparison.fromFix environment index sourceTree)
  rw [IndexedPolynomial.SignatureEquiv.toFix_fromFix] at transported
  change IndexedPolynomial.Fix.fold (IndexedPositiveContainer.Inventory.polynomial (codes block registered))
    (IndexedContainerInventory.nativeAlgebra (codes block registered) (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder)
      realization bottomCode constructorCode values).act environment index
      (comparison.fromFix environment index sourceTree) = _
  rw [nativeAlgebra_inventory_coherence]
  exact transported.symm.trans
    ((IndexedPositiveContainer.Unindexed.blockSignatureEquiv block registered).fold_toFix
      (nativeAlgebra block registered sourceOrder realization bottomCode constructorCode values) environment index tree)

#print axioms nativePayload_matches
#print axioms shapeProgram_exact
#print axioms sourcePoint_positions
#print axioms activeProgram_exact
#print axioms edgeProgram_exact
#print axioms operator_point_iff
#print axioms operator_iff
#print axioms least_iff
#print axioms memberProgram_denote
#print axioms memberProgram_arbitrary_iff
#print axioms memberProgram_junk_index_refused
#print axioms nativeFamilyEquivalence_recursor

end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
