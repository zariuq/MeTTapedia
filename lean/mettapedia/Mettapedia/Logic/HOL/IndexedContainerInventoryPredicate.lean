import Mettapedia.Logic.HOL.IndexedContainerInventoryRepresentation
import Mettapedia.Logic.HOL.ContextualRecursiveSpacePredicate

/-!
# Recursive predicates for complete indexed container inventories

The same indexed code list supplies the shape, activity, child-edge and root
programs. Its original output expressions retain data-dependent container
lengths. The contextual least predicate recognizes the generated family;
root-index refinement keeps the original index and rejects foreign indices.

The semantic inverse is noncomputable. Declaration formation, textual source
adequacy and native implementation refinement remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedContainerInventory

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description

universe u v w x
variable {I : Interface.{u}} {registry : IndexedPositiveContainer.Registry I} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
  (codes : List (IndexedPositiveContainer.Code I registry parameterCount context))
  (ordered : registry.OrderedFinitary)
  {reading : Reading I (registry) Const}
  {model : HenkinModel.{v,w,x} Base Const}
  (realization : IndexedContainerPositionTerms.Realization reading (ordered) model)
  {guards : FieldGuards reading} (images : FieldImages realization guards)
  (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
  (numeral : Nat → Term Const Γ reading.number)
  (values : model.Valuation Γ) (environment : Env I.Value context)
  (represented : realization.Represents environment rho values)

theorem nativePayload_matches (point : ConstructorPoint reading codes environment)
    (data : (guards.constructors codes rho numeral).Data model) :
    FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)
      (nativePayload codes ordered realization environment (sourcePoint codes environment point)) =
      TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) (codes.map reading.fields) data ↔
        encodeConstructorData realization codes point.1 point.2.2 = data := by
  rw [nativePayload_sourcePoint codes ordered realization environment point, Equiv.apply_symm_apply]
  exact ⟨fun same => TypeTheory.FiniteConstructorEncoding.encode_injective (Ty.denote model.Carrier)
    (codes.map reading.fields) same, congrArg _⟩

include images represented

theorem shapeProgram_exact (full : model.FullDomains)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (tag : Ty.denote model.Carrier reading.number)
    (payload : Ty.denote model.Carrier (FiniteConstructorEncoding.payloadType (codes.map reading.fields))) :
    (model.denote (guards.constructors codes rho numeral).shapeProgram values tag payload).down ↔
      ∃ point : ConstructorPoint reading codes environment,
        tag = realization.numbers point.1.val ∧
        nativePayload codes ordered realization environment (sourcePoint codes environment point) = payload := by
  rw [IndexedConstructorGuards.ConstructorPrograms.shapeProgram_denote _ model full]
  constructor
  · rintro ⟨data, ⟨allowed, tagEqual⟩, payloadEqual⟩
    obtain ⟨index, shape, fields⟩ := (images.inventory_allowed codes
      environment rho numeral values represented data).mp allowed
    have restored := FieldImages.encoded_data_eq (realization := realization) codes data shape fields
    refine ⟨⟨data.1, index, shape⟩, tagEqual.trans (numeral_meaning _), ?_⟩
    apply (FiniteConstructorEncoding.payloadEquivalence model (codes.map reading.fields)).injective
    rw [nativePayload_sourcePoint codes ordered realization environment ⟨data.1, index, shape⟩,
      Equiv.apply_symm_apply]
    exact (congrArg _ restored).trans payloadEqual.symm
  · rintro ⟨point, tagEqual, payloadEqual⟩
    refine ⟨encodeConstructorData realization codes point.1 point.2.2,
      ⟨images.encoded_data_allowed codes environment rho numeral values represented point.1 point.2.2,
        tagEqual.trans (numeral_meaning point.1.val).symm⟩, ?_⟩
    rw [← payloadEqual]
    exact (nativePayload_matches codes ordered realization (guards := guards) rho numeral environment point _).mpr rfl

omit images represented in
private theorem sourcePoint_shape_heq (point : ConstructorPoint reading codes environment) :
    HEq (sourcePoint codes environment point).2.2 point.2.2 := by
  rcases point with ⟨occurrence, index, shape⟩
  dsimp only [sourcePoint]
  rfl

omit images represented in
private theorem decoded_transport
    (first second : IndexedPositiveContainer.Code I (registry) parameterCount context)
    (same : first = second) {index : I.Index}
    (firstShape : IndexedPositiveContainer.Code.Shape first environment index)
    (secondShape : IndexedPositiveContainer.Code.Shape second environment index)
    (shapes : HEq firstShape secondShape) (slot : Nat) (target : Ty.denote model.Carrier reading.indices.index) :
    (∃ position,
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation
        (ordered) first).coding firstShape).decode slot = some position ∧
      realization.index (IndexedPositiveContainer.Code.next first firstShape position) = target) ↔
    (∃ position,
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation
        (ordered) second).coding secondShape).decode slot = some position ∧
      realization.index (IndexedPositiveContainer.Code.next second secondShape position) = target) := by
  cases same
  cases eq_of_heq shapes
  rfl

variable (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
  (full : model.FullDomains) (arithmeticValues : model.Valuation [])
  (zero_meaning : model.denote zero arithmeticValues = realization.numbers 0)
  (successor_meaning : ∀ n, model.denote successor arithmeticValues (realization.numbers n) = realization.numbers (n+1))

include full zero_meaning successor_meaning

omit images in
theorem sourcePoint_positions (point : ConstructorPoint reading codes environment)
    (slot : Nat) (target : Ty.denote model.Carrier reading.indices.index) :
    (guards.positions codes rho numeral zero successor).related model values
      (encodeConstructorData realization codes point.1 point.2.2) (realization.numbers slot) target ↔
      ∃ position,
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
          (sourcePoint codes environment point).2).decode slot = some position ∧
        realization.index ((IndexedPositiveContainer.Inventory.polynomial codes).next
          (sourcePoint codes environment point).2 position) = target := by
  rw [FieldImages.encoded_positions_exact (realization := realization) (guards := guards)
    codes environment rho numeral zero successor full
    arithmeticValues zero_meaning successor_meaning values represented point.1 point.2.2 slot target]
  exact decoded_transport ordered realization environment _ _
    (codeAt_source codes reading point.1) point.2.2
    (sourcePoint codes environment point).2.2
    (sourcePoint_shape_heq codes environment point).symm slot target

theorem activeProgram_exact (point : ConstructorPoint reading codes environment) (slot : Nat) :
    (model.denote (guards.positions codes rho numeral zero successor).activeProgram values
      (nativePayload codes ordered realization environment (sourcePoint codes environment point))
      (realization.numbers slot)).down ↔
      ∃ position,
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
          (sourcePoint codes environment point).2).decode slot = some position := by
  rw [IndexedConstructorGuards.PositionPrograms.activeProgram_denote _ model full]
  constructor
  · rintro ⟨data, ⟨_, target, related⟩, payloadAgreement⟩
    have same := (nativePayload_matches codes ordered realization (guards := guards)
      rho numeral environment point data).mp payloadAgreement
    rw [← same] at related
    obtain ⟨position, decoded, _⟩ := (sourcePoint_positions codes ordered realization
      rho numeral values environment represented zero successor full arithmeticValues zero_meaning successor_meaning
      point slot target).mp related
    exact ⟨position, decoded⟩
  · rintro ⟨position, decoded⟩
    refine ⟨encodeConstructorData realization codes point.1 point.2.2,
      ⟨images.encoded_data_allowed codes environment rho numeral values represented point.1 point.2.2,
        realization.index ((IndexedPositiveContainer.Inventory.polynomial codes).next
          (sourcePoint codes environment point).2 position), ?_⟩, ?_⟩
    · exact (sourcePoint_positions codes ordered realization rho numeral values environment represented
        zero successor full arithmeticValues zero_meaning successor_meaning point slot _).mpr ⟨position, decoded, rfl⟩
    · exact (nativePayload_matches codes ordered realization (guards := guards)
        rho numeral environment point _).mpr rfl

theorem edgeProgram_exact (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (point : ConstructorPoint reading codes environment) (slot : Nat)
    (child : Ty.denote model.Carrier space) :
    (model.denote ((guards.positions codes rho numeral zero successor).edgeProgram constructorCode) values
      (nativePayload codes ordered realization environment (sourcePoint codes environment point))
      (realization.numbers slot) child).down ↔
      ∃ position,
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
          (sourcePoint codes environment point).2).decode slot = some position ∧
        IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
          (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
          (nativePayload codes ordered realization)
          (fun _ => nativeConstructor codes ordered realization constructorCode values) environment
          ((IndexedPositiveContainer.Inventory.polynomial codes).next
            (sourcePoint codes environment point).2 position) child := by
  rw [IndexedConstructorGuards.PositionPrograms.edgeProgram_denote _ _ model full]
  constructor
  · rintro ⟨data, _, payloadAgreement, target, related, root⟩
    have same := (nativePayload_matches codes ordered realization (guards := guards)
      rho numeral environment point data).mp payloadAgreement
    rw [← same] at related
    obtain ⟨position, decoded, indexEqual⟩ := (sourcePoint_positions codes ordered realization
      rho numeral values environment represented zero successor full arithmeticValues zero_meaning successor_meaning
      point slot target).mp related
    rw [← indexEqual] at root
    exact ⟨position, decoded, (rootMeaning_iff codes ordered realization constructorCode values images
      index_injective rho numeral numeral_meaning environment represented child _).mp root⟩
  · rintro ⟨position, decoded, root⟩
    refine ⟨encodeConstructorData realization codes point.1 point.2.2,
      images.encoded_data_allowed codes environment rho numeral values represented point.1 point.2.2,
      (nativePayload_matches codes ordered realization (guards := guards) rho numeral environment point _).mpr rfl,
      realization.index ((IndexedPositiveContainer.Inventory.polynomial codes).next
        (sourcePoint codes environment point).2 position), ?_, ?_⟩
    · exact (sourcePoint_positions codes ordered realization rho numeral values environment represented
        zero successor full arithmeticValues zero_meaning successor_meaning point slot _).mpr ⟨position, decoded, rfl⟩
    · exact (rootMeaning_iff codes ordered realization constructorCode values images
        index_injective rho numeral numeral_meaning environment represented child _).mpr root

variable {space : Ty Base} (bottomCode : Term Const Γ space)
  (constructorCode : Term Const Γ (reading.number ⇒
    FiniteConstructorEncoding.payloadType (codes.map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))

def recursiveSignature : RecursiveSpacePredicate.Contextual Const Γ :=
  (guards.positions codes rho numeral zero successor).contextual bottomCode constructorCode

theorem operator_point_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (predicate : Ty.denote model.Carrier (space ⇒ .prop)) (value : Ty.denote model.Carrier space) :
    (model.denote (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
      values predicate value).down ↔
      ∃ (point : ConstructorPoint reading codes environment) (children : Nat → Ty.denote model.Carrier space),
        value = nativeConstructor codes ordered realization constructorCode values point.1.val
          (nativePayload codes ordered realization environment (sourcePoint codes environment point)) children ∧
        (∀ slot position,
          ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
            (sourcePoint codes environment point).2).decode slot = some position →
          IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
            (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
            (nativePayload codes ordered realization)
            (fun _ => nativeConstructor codes ordered realization constructorCode values) environment
            ((IndexedPositiveContainer.Inventory.polynomial codes).next
              (sourcePoint codes environment point).2 position) (children slot) ∧ (predicate (children slot)).down) ∧
        ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
          (sourcePoint codes environment point).2).Canonical (model.denote bottomCode values) children := by
  rw [(recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).operator_meaning
    model full values predicate value]
  dsimp only [recursiveSignature, IndexedConstructorGuards.PositionPrograms.contextual]
  constructor
  · rintro ⟨tag, payload, nativeChildren, shape, equation, conditions⟩
    obtain ⟨point, tagEqual, payloadEqual⟩ := (shapeProgram_exact codes ordered realization images
      rho numeral values environment represented full numeral_meaning tag payload).mp shape
    rw [tagEqual, ← payloadEqual] at equation
    rw [← payloadEqual] at conditions
    let children := fun n => nativeChildren (realization.numbers n)
    refine ⟨point, children, ?_, ?_, ?_⟩
    · change value = model.denote constructorCode values (realization.numbers point.1.val)
        (nativePayload codes ordered realization environment (sourcePoint codes environment point))
        (fun slot => nativeChildren (realization.numbers (realization.numbers.symm slot)))
      simpa only [Equiv.apply_symm_apply] using equation
    · intro slot position decoded
      have active := (activeProgram_exact codes ordered realization images rho numeral values environment
        represented zero successor full arithmeticValues zero_meaning successor_meaning point slot).mpr ⟨position, decoded⟩
      obtain ⟨edge, present⟩ := (conditions (realization.numbers slot)).1 active
      obtain ⟨otherPosition, otherDecoded, root⟩ := (edgeProgram_exact codes ordered realization images
        rho numeral values environment represented zero successor full arithmeticValues zero_meaning successor_meaning
        index_injective numeral_meaning constructorCode point slot (children slot)).mp edge
      have same : otherPosition = position := Option.some.inj (otherDecoded.symm.trans decoded)
      cases same
      exact ⟨root, present⟩
    · intro slot absent
      apply (conditions (realization.numbers slot)).2
      intro active
      obtain ⟨position, decoded⟩ := (activeProgram_exact codes ordered realization images rho numeral values
        environment represented zero successor full arithmeticValues zero_meaning successor_meaning point slot).mp active
      rw [absent] at decoded
      cases decoded
  · rintro ⟨point, children, equation, conditions, canonical⟩
    refine ⟨realization.numbers point.1.val,
      nativePayload codes ordered realization environment (sourcePoint codes environment point),
      (fun slot => children (realization.numbers.symm slot)), ?_, equation, ?_⟩
    · exact (shapeProgram_exact codes ordered realization images rho numeral values environment
        represented full numeral_meaning _ _).mpr ⟨point, rfl, rfl⟩
    · intro nativeSlot
      let slot := realization.numbers.symm nativeSlot
      constructor
      · intro active
        have atSlot := (activeProgram_exact codes ordered realization images rho numeral values environment
          represented zero successor full arithmeticValues zero_meaning successor_meaning point slot).mp
          (by simpa only [slot, Equiv.apply_symm_apply] using active)
        obtain ⟨position, decoded⟩ := atSlot
        obtain ⟨root, present⟩ := conditions slot position decoded
        refine ⟨?_, present⟩
        have edge := (edgeProgram_exact codes ordered realization images rho numeral values environment
          represented zero successor full arithmeticValues zero_meaning successor_meaning index_injective numeral_meaning
          constructorCode point slot (children slot)).mpr ⟨position, decoded, root⟩
        simpa only [slot, Equiv.apply_symm_apply] using edge
      · intro inactive
        have absent : ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
            (sourcePoint codes environment point).2).decode slot = none := by
          cases decoded : ((IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes).coding
              (sourcePoint codes environment point).2).decode slot with
          | none => rfl
          | some position =>
            apply False.elim
            apply inactive
            have active := (activeProgram_exact codes ordered realization images rho numeral values environment
              represented zero successor full arithmeticValues zero_meaning successor_meaning point slot).mpr ⟨position, decoded⟩
            simpa only [slot, Equiv.apply_symm_apply] using active
        exact canonical slot absent

theorem operator_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (predicate : Ty.denote model.Carrier (space ⇒ .prop)) (value : Ty.denote model.Carrier space) :
    (model.denote (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).operator
      values predicate value).down ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.GuardedConstructorStep
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
        (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
        (fun _ => nativeConstructor codes ordered realization constructorCode values)
        environment (fun child => (predicate child).down) value := by
  rw [operator_point_iff codes ordered realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode index_injective numeral_meaning]
  constructor
  · rintro ⟨point, children, equation, conditions, canonical⟩
    exact ⟨point.2.1, (sourcePoint codes environment point).2, children, equation, conditions, canonical⟩
  · rintro ⟨index, shape, children, equation, conditions, canonical⟩
    let point := constructorPoint codes (reading := reading) environment ⟨index, shape⟩
    refine ⟨point, children, ?_, ?_, ?_⟩
    · dsimp only [point]
      rw [sourcePoint_constructorPoint codes environment ⟨index, shape⟩]
      exact equation
    · dsimp only [point]
      rw [sourcePoint_constructorPoint codes environment ⟨index, shape⟩]
      exact conditions
    · dsimp only [point]
      rw [sourcePoint_constructorPoint codes environment ⟨index, shape⟩]
      exact canonical

variable (injections : FieldInjective realization)
  (constructor_fields : HOLShapeSeparation codes ordered realization constructorCode values)
include injections constructor_fields

theorem least_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (value : Ty.denote model.Carrier space) :
    (model.denote (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least
      values value).down ↔
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorFamily
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
        (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
        (fun _ => nativeConstructor codes ordered realization constructorCode values) environment value := by
  rw [RecursiveSpacePredicate.Contextual.least, PredicateFixedPoint.least_denote]
  constructor
  · intro least
    let property : Ty.denote model.Carrier (space ⇒ .prop) := fun point => .up
      (IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorFamily
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
        (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
        (fun _ => nativeConstructor codes ordered realization constructorCode values) environment point)
    exact least property (full _ _) (by
      intro point _ step
      apply (IndexedPolynomial.RecursiveSpaceRepresentation.constructorFamily_fixed
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
        (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
        (fun _ => nativeConstructor codes ordered realization constructorCode values)
        (nativePayload_injective codes ordered realization injections)
        (nativeConstructor_fields codes ordered realization constructorCode values constructor_fields)
        environment point).mpr
      exact (operator_iff codes ordered realization images rho numeral values environment represented
        zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode
        index_injective numeral_meaning property point).mp step)
  · intro generated property _ closed
    apply IndexedPolynomial.RecursiveSpaceRepresentation.constructorFamily_least
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
      (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
      (fun _ => nativeConstructor codes ordered realization constructorCode values)
      environment (fun point => (property point).down) ?_ value generated
    intro point step
    exact closed point (full _ _) ((operator_iff codes ordered realization images rho numeral values
      environment represented zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode
      index_injective numeral_meaning property point).mpr step)

def memberProgram : Term Const Γ (space ⇒ reading.indices.index ⇒ .prop) :=
  .lam (.lam (.and
    (.app (weaken (weaken (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least))
      (.var (.vs .vz)))
    (.app (.app (weaken (weaken ((guards.constructors codes rho numeral).rootProgram constructorCode)))
      (.var (.vs .vz))) (.var .vz))))

omit injections constructor_fields zero_meaning successor_meaning in
theorem memberProgram_index_image (value : Ty.denote model.Carrier space)
    (target : Ty.denote model.Carrier reading.indices.index)
    (member : (model.denote (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value target).down) : ∃ index, realization.index index = target := by
  change
    (model.denote (weaken (weaken (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least))
      (model.extend (model.extend values value) target) value).down ∧
    (model.denote (weaken (weaken ((guards.constructors codes rho numeral).rootProgram constructorCode)))
      (model.extend (model.extend values value) target) value target).down at member
  have interpreted : (model.denote ((guards.constructors codes rho numeral).rootProgram constructorCode)
      values value target).down := by simpa only [Soundness.denote_weaken] using member.2
  have root := (IndexedConstructorGuards.ConstructorPrograms.rootProgram_denote
    (guards.constructors codes rho numeral) constructorCode model full values value target).mp interpreted
  exact rootMeaning_index_image codes ordered realization constructorCode values images rho numeral
    environment represented value target root

omit injections constructor_fields zero_meaning successor_meaning in
theorem memberProgram_junk_index_refused (value : Ty.denote model.Carrier space)
    (target : Ty.denote model.Carrier reading.indices.index)
    (outside : ∀ index, realization.index index ≠ target) :
    ¬ (model.denote (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value target).down := by
  intro member
  obtain ⟨index, same⟩ := memberProgram_index_image codes ordered realization images rho numeral values
    environment represented zero successor full bottomCode constructorCode value target member
  exact outside index same

theorem memberProgram_denote (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (value : Ty.denote model.Carrier space) (index : I.Index) :
    (model.denote (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value (realization.index index)).down ↔
      IndexedPolynomial.Algebra.Generated
        (nativeAlgebra codes ordered realization bottomCode constructorCode values) environment index value := by
  change
    (model.denote (weaken (weaken (recursiveSignature codes (guards := guards) rho numeral zero successor bottomCode constructorCode).least))
      (model.extend (model.extend values value) (realization.index index)) value).down ∧
    (model.denote (weaken (weaken ((guards.constructors codes rho numeral).rootProgram constructorCode)))
      (model.extend (model.extend values value) (realization.index index)) value (realization.index index)).down ↔ _
  simp only [Soundness.denote_weaken]
  have family := least_iff codes ordered realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections constructor_fields
    index_injective numeral_meaning value
  have root := (IndexedConstructorGuards.ConstructorPrograms.rootProgram_denote
    (guards.constructors codes rho numeral) constructorCode model full values value (realization.index index)).trans
    (rootMeaning_iff codes ordered realization constructorCode values images index_injective rho numeral
      numeral_meaning environment represented value index)
  exact (and_congr family root).trans (IndexedPolynomial.RecursiveSpaceRepresentation.generated_iff_constructorFamily_root
    (IndexedPositiveContainer.RecursiveSpaceRepresentation.inventoryPresentation ordered codes)
    (nativePayload codes ordered realization) (fun _ => model.denote bottomCode values)
    (fun _ => nativeConstructor codes ordered realization constructorCode values)
    (nativePayload_injective codes ordered realization injections)
    (nativeConstructor_fields codes ordered realization constructorCode values constructor_fields)
    environment index value).symm

theorem memberProgram_arbitrary_iff (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
    (value : Ty.denote model.Carrier space) (target : Ty.denote model.Carrier reading.indices.index) :
    (model.denote (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode)
      values value target).down ↔
      ∃ index, realization.index index = target ∧
        IndexedPolynomial.Algebra.Generated
          (nativeAlgebra codes ordered realization bottomCode constructorCode values) environment index value := by
  constructor
  · intro member
    obtain ⟨index, same⟩ := memberProgram_index_image codes ordered realization images rho numeral values
      environment represented zero successor full bottomCode constructorCode value target member
    refine ⟨index, same, (memberProgram_denote codes ordered realization images rho numeral values environment
      represented zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections
      constructor_fields index_injective numeral_meaning value index).mp ?_⟩
    simpa only [same] using member
  · rintro ⟨index, same, generated⟩
    have member := (memberProgram_denote codes ordered realization images rho numeral values environment
      represented zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections
      constructor_fields index_injective numeral_meaning value index).mpr generated
    simpa only [same] using member

noncomputable def nativeFamilyEquivalence (index_injective : Function.Injective realization.index)
    (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n) (index : I.Index) :
    IndexedPolynomial.Fix (IndexedPositiveContainer.Inventory.polynomial codes) environment index ≃
      {value : Ty.denote model.Carrier space //
        (model.denote (memberProgram codes (guards := guards) rho numeral zero successor bottomCode constructorCode)
          values value (realization.index index)).down} := by
  let original := (nativeGeneratedRepresentation codes ordered realization bottomCode constructorCode values
    injections constructor_fields).toEquiv environment index
  let checked := memberProgram_denote codes ordered realization images rho numeral values environment represented
    zero successor full arithmeticValues zero_meaning successor_meaning bottomCode constructorCode injections constructor_fields
    index_injective numeral_meaning
  exact {
    toFun := fun tree => ⟨(original tree).val, (checked _ index).mpr (original tree).property⟩
    invFun := fun value => original.symm ⟨value.val, (checked _ index).mp value.property⟩
    left_inv := fun tree => original.symm_apply_apply tree
    right_inv := by
      intro value
      apply Subtype.ext
      exact congrArg (fun argument : IndexedPolynomial.Algebra.GeneratedCarrier
        (nativeAlgebra codes ordered realization bottomCode constructorCode values) environment index => argument.val)
        (original.apply_symm_apply ⟨value.val, (checked _ index).mp value.property⟩) }

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
#print axioms nativeFamilyEquivalence

end Mettapedia.Logic.HOL.IndexedContainerInventory
