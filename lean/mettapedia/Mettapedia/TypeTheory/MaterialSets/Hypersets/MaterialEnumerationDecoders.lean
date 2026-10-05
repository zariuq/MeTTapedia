import Mettapedia.TypeTheory.MaterialSets.Hypersets.Operations
import Mettapedia.TypeTheory.ContextualImageFactorization

/-!
# Material decoders from small receipt enumerations

A surjective small receipt map to the actual members of a material set
constructs a small carrier of saturated receipt predicates. Bounded
separation forms the singleton material row identified by each predicate;
union returns its unique value. Encoding and decoding are actual inverse
functions, without selecting a receipt or a graph presentation.

The carrier uses every proposition-valued subset of the receipt type. This
uses full powerset strength rather than only exponentiation. Neither an
arbitrary host-type inverse nor a uniform family of enumeration data is
inferred from pointwise existence of enumerations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialEnumerationDecoders

open Mettapedia.TypeTheory.ContextualImageFactorization

universe u v

abbrev Members (X : HSet.{u}) := {value : HSet.{u} // value ∈ X}

variable {X Y Z : HSet.{u}}

def receiptFibre (enumeration : Enumeration.{u, u + 1} (Members X))
    (member : Members X) : Set enumeration.Carrier :=
  fun receipt => enumeration.value receipt = member

abbrev Code (enumeration : Enumeration.{u, u + 1} (Members X)) : Type u :=
  {predicate : Set enumeration.Carrier // ∃ member, predicate = receiptFibre enumeration member}

def encode (enumeration : Enumeration.{u, u + 1} (Members X)) (member : Members X) :
    Code enumeration := ⟨receiptFibre enumeration member, member, rfl⟩

/-- The complete bounded row is computed independently of a class witness. -/
def row (enumeration : Enumeration.{u, u + 1} (Members X))
    (predicate : Set enumeration.Carrier) : HSet.{u} :=
  HSet.sep (fun value => ∀ receipt,
    predicate receipt ↔ (enumeration.value receipt).val = value) X

theorem row_encode (enumeration : Enumeration.{u, u + 1} (Members X)) (member : Members X) :
    row enumeration (encode enumeration member).val = {member.val} := by
  apply HSet.ext
  intro value
  rw [row, HSet.mem_sep, HSet.mem_singleton]
  constructor
  · rintro ⟨_available, sameFibre⟩
    obtain ⟨receipt, represents⟩ := enumeration.covered member
    have rowValue := (sameFibre receipt).mp represents
    exact rowValue.symm.trans (congrArg Subtype.val represents)
  · intro same
    refine ⟨same.symm ▸ member.property, ?_⟩
    intro receipt
    change enumeration.value receipt = member ↔ (enumeration.value receipt).val = value
    rw [same]
    exact ⟨congrArg Subtype.val, Subtype.ext⟩

def decodeValue (enumeration : Enumeration.{u, u + 1} (Members X))
    (predicate : Set enumeration.Carrier) : HSet.{u} :=
  HSet.sUnion (row enumeration predicate)

theorem decodeValue_encode (enumeration : Enumeration.{u, u + 1} (Members X))
    (member : Members X) : decodeValue enumeration (encode enumeration member).val = member.val := by
  rw [decodeValue, row_encode, HSet.sUnion_singleton]

theorem decodeValue_mem (enumeration : Enumeration.{u, u + 1} (Members X)) (code : Code enumeration) :
    decodeValue enumeration code.val ∈ X := by
  obtain ⟨member, same⟩ := code.property
  rw [same]
  exact (decodeValue_encode enumeration member).symm ▸ member.property

def decode (enumeration : Enumeration.{u, u + 1} (Members X)) (code : Code enumeration) : Members X :=
  ⟨decodeValue enumeration code.val, decodeValue_mem enumeration code⟩

theorem decode_encode (enumeration : Enumeration.{u, u + 1} (Members X)) (member : Members X) :
    decode enumeration (encode enumeration member) = member :=
  Subtype.ext (decodeValue_encode enumeration member)

theorem encode_decode (enumeration : Enumeration.{u, u + 1} (Members X)) (code : Code enumeration) :
    encode enumeration (decode enumeration code) = code := by
  obtain ⟨member, same⟩ := code.property
  have codeEq : code = encode enumeration member := Subtype.ext same
  rw [codeEq, decode_encode]

def memberEquiv (enumeration : Enumeration.{u, u + 1} (Members X)) : Code enumeration ≃ Members X where
  toFun := decode enumeration
  invFun := encode enumeration
  left_inv := encode_decode enumeration
  right_inv := decode_encode enumeration

theorem encode_eq_iff (enumeration : Enumeration.{u, u + 1} (Members X)) (first second : Members X) :
    encode enumeration first = encode enumeration second ↔ first = second := by
  constructor
  · intro same
    exact (decode_encode enumeration first).symm.trans
      ((congrArg (decode enumeration) same).trans (decode_encode enumeration second))
  · intro same
    exact congrArg (encode enumeration) same

def receiptCode (enumeration : Enumeration.{u, u + 1} (Members X)) (receipt : enumeration.Carrier) :
    Code enumeration := encode enumeration (enumeration.value receipt)

theorem receiptCode_eq_iff (enumeration : Enumeration.{u, u + 1} (Members X))
    (first second : enumeration.Carrier) : receiptCode enumeration first = receiptCode enumeration second ↔
      enumeration.value first = enumeration.value second :=
  encode_eq_iff enumeration _ _

theorem receiptCode_surjective (enumeration : Enumeration.{u, u + 1} (Members X)) :
    Function.Surjective (receiptCode enumeration) := by
  intro code
  obtain ⟨receipt, same⟩ := enumeration.covered (decode enumeration code)
  exact ⟨receipt, (congrArg (encode enumeration) same).trans (encode_decode enumeration code)⟩

/-- Material transport decodes, applies the authored member function and
encodes its result. Target receipt coverage is used only by inverse laws. -/
def transport (source : Enumeration.{u, u + 1} (Members X))
    (target : Enumeration.{u, u + 1} (Members Y)) (operation : Members X → Members Y) :
    Code source → Code target := fun code => encode target (operation (decode source code))

theorem decode_transport (source : Enumeration.{u, u + 1} (Members X))
    (target : Enumeration.{u, u + 1} (Members Y)) (operation : Members X → Members Y)
    (code : Code source) : decode target (transport source target operation code) =
      operation (decode source code) := decode_encode target _

theorem transport_encode (source : Enumeration.{u, u + 1} (Members X))
    (target : Enumeration.{u, u + 1} (Members Y)) (operation : Members X → Members Y)
    (member : Members X) : transport source target operation (encode source member) =
      encode target (operation member) := by
  unfold transport
  rw [decode_encode]

theorem transport_id (enumeration : Enumeration.{u, u + 1} (Members X)) (code : Code enumeration) :
    transport enumeration enumeration id code = code := encode_decode enumeration code

theorem transport_comp (source : Enumeration.{u, u + 1} (Members X))
    (middle : Enumeration.{u, u + 1} (Members Y)) (target : Enumeration.{u, u + 1} (Members Z))
    (earlier : Members X → Members Y) (later : Members Y → Members Z) (code : Code source) :
    transport source target (later ∘ earlier) code =
      transport middle target later (transport source middle earlier code) := by
  unfold transport
  rw [decode_encode]
  rfl

/-! ## Separated material fibres of an arbitrary typed function -/

variable {T : Type v}

abbrev TypedFibre (operation : Members X → T) (parameter : T) :=
  {member : Members X // operation member = parameter}

def fibreSet (operation : Members X → T) (parameter : T) : HSet.{u} :=
  HSet.sep (fun value => ∃ available : value ∈ X, operation ⟨value, available⟩ = parameter) X

def fibreMember (operation : Members X → T) (parameter : T) (receipt : TypedFibre operation parameter) :
    Members (fibreSet operation parameter) :=
  ⟨receipt.val.val, HSet.mem_sep.mpr ⟨receipt.val.property, receipt.val.property, receipt.property⟩⟩

def memberFibre (operation : Members X → T) (parameter : T)
    (member : Members (fibreSet operation parameter)) : TypedFibre operation parameter :=
  ⟨⟨member.val, (HSet.mem_sep.mp member.property).1⟩, by
    obtain ⟨available, same⟩ := (HSet.mem_sep.mp member.property).2
    exact same⟩

theorem memberFibre_fibreMember (operation : Members X → T) (parameter : T)
    (receipt : TypedFibre operation parameter) :
    memberFibre operation parameter (fibreMember operation parameter receipt) = receipt :=
  Subtype.ext (Subtype.ext rfl)

theorem fibreMember_memberFibre (operation : Members X → T) (parameter : T)
    (member : Members (fibreSet operation parameter)) :
    fibreMember operation parameter (memberFibre operation parameter member) = member := Subtype.ext rfl

def fibreEquiv (operation : Members X → T) (parameter : T) :
    TypedFibre operation parameter ≃ Members (fibreSet operation parameter) where
  toFun := fibreMember operation parameter
  invFun := memberFibre operation parameter
  left_inv := memberFibre_fibreMember operation parameter
  right_inv := fibreMember_memberFibre operation parameter

def fibreEnumeration (operation : Members X → T) (parameter : T)
    (enumeration : Enumeration.{u, u + 1} (TypedFibre operation parameter)) :
    Enumeration.{u, u + 1} (Members (fibreSet operation parameter)) :=
  enumeration.transport (fibreEquiv operation parameter)

abbrev FibreCode (operation : Members X → T) (parameter : T)
    (enumeration : Enumeration.{u, u + 1} (TypedFibre operation parameter)) : Type u :=
  Code (fibreEnumeration operation parameter enumeration)

def fibreCodeEquiv (operation : Members X → T) (parameter : T)
    (enumeration : Enumeration.{u, u + 1} (TypedFibre operation parameter)) :
    FibreCode operation parameter enumeration ≃ TypedFibre operation parameter :=
  (memberEquiv (fibreEnumeration operation parameter enumeration)).trans (fibreEquiv operation parameter).symm

theorem fibreCodeEquiv_value (operation : Members X → T) (parameter : T)
    (enumeration : Enumeration.{u, u + 1} (TypedFibre operation parameter))
    (code : FibreCode operation parameter enumeration) :
    (fibreCodeEquiv operation parameter enumeration code).val.val =
      decodeValue (fibreEnumeration operation parameter enumeration) code.val := rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialEnumerationDecoders
