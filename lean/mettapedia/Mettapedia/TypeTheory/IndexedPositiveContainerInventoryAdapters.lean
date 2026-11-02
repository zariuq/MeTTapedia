import Mettapedia.TypeTheory.IndexedPositiveContainerInventory

/-!
# Signature comparisons for indexed constructor inventories

A singleton inventory retains its one code exactly. Inventories obtained
from the established admitted-block embedding retain the same constructor
ordinals, shapes, recursive positions and child indices.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.IndexedPositiveContainer.Inventory
open IndexedPolynomial IndexedPolynomial.Description
universe u t
variable {I : Interface.{u}} {registry : Registry I} {parameters : Nat} {context : List I.SortCode}

private theorem singletonOrdinal (code : Code I registry parameters context) (occurrence : Fin [code].length) :
    occurrence = (0 : Fin 1) := by
  apply Fin.ext
  change occurrence.val = 0
  have bound := occurrence.isLt
  change occurrence.val < 1 at bound
  omega

def singletonSignatureEquiv (code : Code I registry parameters context) :
    SignatureEquiv (polynomial [code]) (Code.polynomial code) where
  shape := fun environment index =>
    { toFun := fun point => by
        rcases point with ⟨occurrence,data⟩
        have only : occurrence = (0 : Fin 1) := singletonOrdinal code occurrence
        cases only
        exact data
      invFun := fun data => ⟨0,data⟩
      left_inv := by
        rintro ⟨occurrence,data⟩
        have only : occurrence = (0 : Fin 1) := singletonOrdinal code occurrence
        cases only
        rfl
      right_inv := by intro data; rfl }
  position := fun point => by
    rcases point with ⟨occurrence,data⟩
    have only : occurrence = (0 : Fin 1) := singletonOrdinal code occurrence
    cases only
    exact Equiv.refl _
  next_preserved := fun point position => by
    rcases point with ⟨occurrence,data⟩
    have only : occurrence = (0 : Fin 1) := singletonOrdinal code occurrence
    cases only
    rfl

variable {source : PositiveInductiveBlock.Registry}

def blockCodes (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered) :
    List (Code I (Unindexed.liftRegistry source I) parameters context) := List.ofFn (Unindexed.blockCode block registered)

def blockOrdinals (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered) :
    Fin (blockCodes block registered).length ≃ Fin block.constructors.length where
  toFun index := ⟨index.val,by simpa only [blockCodes,List.length_ofFn] using index.isLt⟩
  invFun index := ⟨index.val,by simpa only [blockCodes,List.length_ofFn] using index.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

theorem blockCode_at (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    (index : Fin (blockCodes block registered).length) :
    (blockCodes block registered).get index = Unindexed.blockCode block registered ((blockOrdinals block registered) index) := by
  simp only [blockCodes,List.get_eq_getElem,List.getElem_ofFn,blockOrdinals]
  rfl

private def enumeratedPolynomial (enumeration : Σ count : Nat, Fin count → Code I registry parameters context) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := fun environment index => Σ occurrence : Fin enumeration.1, Code.Shape (enumeration.2 occurrence) environment index
  Position := fun shape => Code.Position (enumeration.2 shape.1) shape.2
  next := fun shape position => Code.next (enumeration.2 shape.1) shape.2 position

private theorem enumeration_eq {first second : Nat} (same : first = second)
    (left : Fin first → Code I registry parameters context) (right : Fin second → Code I registry parameters context)
    (points : ∀ index, left index = right (Fin.cast same index)) :
    (⟨first,left⟩ : Σ count : Nat, Fin count → Code I registry parameters context) = ⟨second,right⟩ := by
  cases same
  apply congrArg (Sigma.mk first)
  funext index
  exact points index

private theorem blockEnumeration_eq (block : PositiveInductiveBlock.Admitted source I parameters context)
    (registered : block.WellRegistered) :
    (⟨(blockCodes block registered).length,fun occurrence => (blockCodes block registered).get occurrence⟩ :
      Σ count : Nat, Fin count → Code I (Unindexed.liftRegistry source I) parameters context) =
      ⟨block.constructors.length,Unindexed.blockCode block registered⟩ := by
  apply enumeration_eq (by simp only [blockCodes,List.length_ofFn])
  intro index
  simp only [blockCodes,List.get_eq_getElem,List.getElem_ofFn]
  apply congrArg (Unindexed.blockCode block registered)
  apply Fin.ext
  rfl

theorem blockPolynomial_eq (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered) :
    Unindexed.blockPolynomial block registered = polynomial (blockCodes block registered) := by
  exact congrArg enumeratedPolynomial (blockEnumeration_eq block registered).symm

private noncomputable def enumeratedPresentation (ordered : registry.OrderedFinitary)
    (enumeration : Σ count : Nat, Fin count → Code I registry parameters context) :
    IndexedPolynomial.RecursiveSpaceRepresentation.Presentation (Base := Env I.Value context) (Index := fun _ => I.Index) where
  polynomial := enumeratedPolynomial enumeration
  coding := fun shape => (RecursiveSpaceRepresentation.codePresentation ordered (enumeration.2 shape.1)).coding shape.2
  tag := fun shape => shape.1.val

theorem blockPresentation_eq
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered) :
    RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered =
      RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered) := by
  exact congrArg (enumeratedPresentation (Unindexed.liftOrdered sourceOrder)) (blockEnumeration_eq block registered).symm

private def castPosition {first second : Code I registry parameters context} (same : first = second)
    {environment : Env I.Value context} {index : I.Index} (shape : Code.Shape first environment index) :
    Code.Position first shape ≃ Code.Position second (cast (congrArg (fun code => Code.Shape code environment index) same) shape) := by
  cases same
  exact Equiv.refl _

private theorem castNext {first second : Code I registry parameters context} (same : first = second)
    {environment : Env I.Value context} {index : I.Index} (shape : Code.Shape first environment index)
    (position : Code.Position first shape) :
    Code.next second (cast (congrArg (fun code => Code.Shape code environment index) same) shape)
      (castPosition same shape position) = Code.next first shape position := by
  cases same
  rfl

def blockSignatureEquiv (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered) :
    SignatureEquiv (polynomial (blockCodes block registered)) (Unindexed.blockPolynomial block registered) where
  shape := fun environment index => Equiv.sigmaCongr (blockOrdinals block registered) fun occurrence =>
    Equiv.cast (congrArg (fun code => Code.Shape code environment index) (blockCode_at block registered occurrence))
  position := fun point => by
    rcases point with ⟨occurrence,shape⟩
    exact castPosition (blockCode_at block registered occurrence) shape
  next_preserved := fun point position => by
    rcases point with ⟨occurrence,shape⟩
    exact castNext (blockCode_at block registered occurrence) shape position

private theorem code_extend_cast (ordered : registry.OrderedFinitary)
    {first second : Code I registry parameters context} (same : first = second)
    {environment : Env I.Value context} {index : I.Index} (shape : Code.Shape first environment index)
    {Target : Type t} (default : Target) (children : Code.Position first shape → Target) :
    ((RecursiveSpaceRepresentation.codePresentation ordered second).coding
      (cast (congrArg (fun code => Code.Shape code environment index) same) shape)).extend default
        (fun position => children ((castPosition same shape).symm position)) =
      ((RecursiveSpaceRepresentation.codePresentation ordered first).coding shape).extend default children := by
  cases same
  rfl

theorem block_extend_coherence
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (polynomial (blockCodes block registered)).Shape environment index)
    {Target : Type t} (default : Target) (children : (polynomial (blockCodes block registered)).Position shape → Target) :
    ((RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      ((blockSignatureEquiv block registered).shape environment index shape)).extend default
        (fun position => children (((blockSignatureEquiv block registered).position shape).symm position)) =
      ((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).extend
        default children := by
  rcases shape with ⟨occurrence,data⟩
  exact code_extend_cast (Unindexed.liftOrdered sourceOrder) (blockCode_at block registered occurrence) data default children

theorem block_tag_coherence
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (polynomial (blockCodes block registered)).Shape environment index) :
    (RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).tag
      ((blockSignatureEquiv block registered).shape environment index shape) =
      (RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).tag shape := rfl

private theorem code_decode_cast (ordered : registry.OrderedFinitary)
    {first second : Code I registry parameters context} (same : first = second)
    {environment : Env I.Value context} {index : I.Index} (shape : Code.Shape first environment index) (slot : Nat) :
    ((RecursiveSpaceRepresentation.codePresentation ordered second).coding
      (cast (congrArg (fun code => Code.Shape code environment index) same) shape)).decode slot =
      Option.map (castPosition same shape)
        (((RecursiveSpaceRepresentation.codePresentation ordered first).coding shape).decode slot) := by
  cases same
  change ((RecursiveSpaceRepresentation.codePresentation ordered first).coding shape).decode slot =
    Option.map id (((RecursiveSpaceRepresentation.codePresentation ordered first).coding shape).decode slot)
  exact (congrFun Option.map_id _).symm

theorem block_decode_coherence
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (polynomial (blockCodes block registered)).Shape environment index) (slot : Nat) :
    ((RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      ((blockSignatureEquiv block registered).shape environment index shape)).decode slot =
      Option.map ((blockSignatureEquiv block registered).position shape)
        (((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).decode slot) := by
  rcases shape with ⟨occurrence,data⟩
  exact code_decode_cast (Unindexed.liftOrdered sourceOrder) (blockCode_at block registered occurrence) data slot

theorem block_decoded_iff
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (polynomial (blockCodes block registered)).Shape environment index) (slot : Nat)
    (property : (Unindexed.blockPolynomial block registered).Position
      ((blockSignatureEquiv block registered).shape environment index shape) → Prop) :
    (∃ position, ((RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      ((blockSignatureEquiv block registered).shape environment index shape)).decode slot = some position ∧ property position) ↔
    ∃ position, ((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).decode slot = some position ∧
      property ((blockSignatureEquiv block registered).position shape position) := by
  rw [block_decode_coherence]
  cases ((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).decode slot <;> simp

theorem block_forall_decoded_iff
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (polynomial (blockCodes block registered)).Shape environment index) (slot : Nat)
    (property : (Unindexed.blockPolynomial block registered).Position
      ((blockSignatureEquiv block registered).shape environment index shape) → Prop) :
    (∀ position, ((RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      ((blockSignatureEquiv block registered).shape environment index shape)).decode slot = some position → property position) ↔
    ∀ position, ((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).decode slot = some position →
      property ((blockSignatureEquiv block registered).position shape position) := by
  rw [block_decode_coherence]
  cases ((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).decode slot <;> simp

theorem block_canonical_iff
    (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
    (block : PositiveInductiveBlock.Admitted source I parameters context) (registered : block.WellRegistered)
    {environment : Env I.Value context} {index : I.Index}
    (shape : (polynomial (blockCodes block registered)).Shape environment index)
    {Target : Type t} (default : Target) (children : Nat → Target) :
    ((RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      ((blockSignatureEquiv block registered).shape environment index shape)).Canonical default children ↔
    ((RecursiveSpaceRepresentation.inventoryPresentation (Unindexed.liftOrdered sourceOrder) (blockCodes block registered)).coding shape).Canonical default children := by
  unfold IndexedPolynomial.SlotEncoding.Canonical
  simp only [block_decode_coherence, Option.map_eq_none_iff]

#print axioms singletonSignatureEquiv
#print axioms blockPolynomial_eq
#print axioms blockPresentation_eq
#print axioms blockSignatureEquiv
end Mettapedia.TypeTheory.IndexedPositiveContainer.Inventory
