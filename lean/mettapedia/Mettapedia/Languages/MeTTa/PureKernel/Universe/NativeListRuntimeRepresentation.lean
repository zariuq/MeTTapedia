import Mettapedia.Languages.MeTTa.PureKernel.Universe.NativeIndexedFamilies
import Mettapedia.Languages.MeTTa.OSLFCore.MinimalOps

/-!
# Native List representation at the MeTTa runtime seam

Prime's native List is the fixed point of a strictly-positive polynomial.  A
runtime expression is a flat sequence of atoms.  This module proves the exact
semantic seam between those two representations:

* `nil` is the empty expression;
* `cons` prepends one encoded atom;
* `consAtom` realizes constructor introduction;
* `deconsAtom` realizes the partial head/tail observation; and
* a lawful element codec makes list encoding and decoding a partial
  equivalence, excluding malformed and non-expression atoms.

This is a representation theorem, not a cost theorem.  It licenses direct
implementation against the runtime expression carrier, but makes no claim
that object-language elimination and runtime work have the same cost or
demand.  That stronger correspondence remains a separate performance gate.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.Universe
namespace NativeListRuntimeRepresentation

open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.Languages.MeTTa.OSLFCore

universe u

abbrev NativeList (Element : Type u) :=
  ListExample.ListP Element

/-- A lossless partial codec for elements stored in runtime expressions.
Atoms outside the image are permitted and rejected by `decode`. -/
structure ElementCodec (Element : Type u) where
  encode : Element → Atom
  decode : Atom → Option Element
  decode_encode : ∀ element, decode (encode element) = some element
  encode_decode : ∀ {atom element}, decode atom = some element →
    encode element = atom

namespace ElementCodec

variable {Element : Type u} (codec : ElementCodec Element)

/-- Decode a flat sequence element by element, retaining the first precise
failure rather than accepting a partially decoded runtime expression. -/
def decodeAtoms : List Atom → Option (List Element)
  | [] => some []
  | atom :: atoms => do
      let element ← codec.decode atom
      let elements ← decodeAtoms atoms
      pure (element :: elements)

@[simp] theorem decodeAtoms_map_encode (elements : List Element) :
    codec.decodeAtoms (elements.map codec.encode) = some elements := by
  induction elements with
  | nil => rfl
  | cons head tail hypothesis =>
      simp [decodeAtoms, codec.decode_encode, hypothesis]

private theorem encode_of_decodeAtoms
    {atoms : List Atom} {elements : List Element}
    (decoded : codec.decodeAtoms atoms = some elements) :
    elements.map codec.encode = atoms := by
  induction atoms generalizing elements with
  | nil =>
      simp [decodeAtoms] at decoded
      subst elements
      rfl
  | cons atom atoms hypothesis =>
      cases decodedHead : codec.decode atom with
      | none => simp [decodeAtoms, decodedHead] at decoded
      | some element =>
          cases decodedTail : codec.decodeAtoms atoms with
          | none => simp [decodeAtoms, decodedHead, decodedTail] at decoded
          | some tail =>
              simp [decodeAtoms, decodedHead, decodedTail] at decoded
              subst elements
              simp only [List.map_cons]
              rw [codec.encode_decode decodedHead, hypothesis decodedTail]

/-- Encode a polynomial List as the flat runtime expression containing its
encoded elements in spine order. -/
noncomputable def encodeList (list : NativeList Element) : Atom :=
  .expression ((ListExample.toList list).map codec.encode)

/-- Decode exactly the runtime-expression image of native Lists. -/
def decodeList : Atom → Option (NativeList Element)
  | .expression atoms => (codec.decodeAtoms atoms).map ListExample.ofList
  | _ => none

@[simp] theorem decodeList_encodeList (list : NativeList Element) :
    codec.decodeList (codec.encodeList list) = some list := by
  simp [decodeList, encodeList, ListExample.ofList_toList]

/-- Successful decoding is exact: re-encoding recovers the original runtime
atom rather than merely an observationally equivalent sequence. -/
theorem encodeList_decodeList {atom : Atom} {list : NativeList Element}
    (decoded : codec.decodeList atom = some list) :
    codec.encodeList list = atom := by
  cases atom with
  | symbol name => simp [decodeList] at decoded
  | var name => simp [decodeList] at decoded
  | grounded value => simp [decodeList] at decoded
  | expression atoms =>
      unfold decodeList at decoded
      cases decodedElements : codec.decodeAtoms atoms with
      | none => simp [decodedElements] at decoded
      | some elements =>
          simp only [decodedElements, Option.map_some, Option.some.injEq]
            at decoded
          subst list
          have encodedElements : elements.map codec.encode = atoms :=
            codec.encode_of_decodeAtoms decodedElements
          simp [encodeList, encodedElements]

theorem encodeList_injective : Function.Injective codec.encodeList := by
  intro first second equality
  have decodedEquality := congrArg codec.decodeList equality
  simpa using decodedEquality

/-- The graph of encoding is the exact successful-decoding relation. -/
def Represents (list : NativeList Element) (atom : Atom) : Prop :=
  codec.encodeList list = atom

theorem represents_iff_decode (list : NativeList Element) (atom : Atom) :
    codec.Represents list atom ↔ codec.decodeList atom = some list := by
  constructor
  · intro represented
    rw [← represented]
    exact codec.decodeList_encodeList list
  · exact codec.encodeList_decodeList

@[simp] theorem encodeList_nil :
    codec.encodeList (ListExample.nil : NativeList Element) =
      .expression [] := by
  simp [encodeList]

@[simp] theorem encodeList_cons (head : Element) (tail : NativeList Element) :
    codec.encodeList (ListExample.cons head tail) =
      .expression (codec.encode head ::
        (ListExample.toList tail).map codec.encode) := by
  simp [encodeList]

/-- Runtime `cons-atom` is constructor introduction for the represented
native List. -/
@[simp] theorem consAtom_encodeList (head : Element)
    (tail : NativeList Element) :
    consAtom (codec.encode head) (codec.encodeList tail) =
      some (codec.encodeList (ListExample.cons head tail)) := by
  simp [consAtom, encodeList]

/-- Runtime `decons-atom` returns precisely the represented head and tail of
a native `cons`. -/
@[simp] theorem deconsAtom_encodeList_cons (head : Element)
    (tail : NativeList Element) :
    deconsAtom (codec.encodeList (ListExample.cons head tail)) =
      some (codec.encode head, codec.encodeList tail) := by
  simp [deconsAtom, encodeList]

/-- The empty native List has no head/tail decomposition. -/
@[simp] theorem deconsAtom_encodeList_nil :
    deconsAtom (codec.encodeList (ListExample.nil : NativeList Element)) =
      none := by
  simp [deconsAtom, encodeList]

/-! ## Negative representation controls -/

@[simp] theorem decodeList_symbol (name : String) :
    codec.decodeList (.symbol name) = none :=
  rfl

theorem symbol_not_represented (name : String) (list : NativeList Element) :
    ¬ codec.Represents list (.symbol name) := by
  intro represented
  have decoded := (codec.represents_iff_decode list (.symbol name)).mp
    represented
  simp at decoded

theorem undecodable_singleton_not_represented (atom : Atom)
    (undecodable : codec.decode atom = none) (list : NativeList Element) :
    ¬ codec.Represents list (.expression [atom]) := by
  intro represented
  have decoded := (codec.represents_iff_decode list (.expression [atom])).mp
    represented
  have cannotDecode : codec.decodeList (.expression [atom]) = none := by
    simp [decodeList, decodeAtoms, undecodable]
  rw [cannotDecode] at decoded
  cases decoded

end ElementCodec

/-! ## A concrete, non-vacuous element codec -/

/-- Symbols form a losslessly encoded runtime element class.  Other atom
constructors remain outside this codec's image. -/
def symbolCodec : ElementCodec String where
  encode := .symbol
  decode
    | .symbol name => some name
    | _ => none
  decode_encode := by
    intro name
    rfl
  encode_decode := by
    intro atom name decoded
    cases atom <;> simp_all

@[simp] theorem symbolCodec_represents_pair :
    symbolCodec.Represents
      (ListExample.ofList ["left", "right"])
      (.expression [.symbol "left", .symbol "right"]) := by
  simp [ElementCodec.Represents, ElementCodec.encodeList, symbolCodec]

@[simp] theorem symbolCodec_rejects_variable :
    symbolCodec.decodeList (.expression [.var "x"]) = none := by
  simp [ElementCodec.decodeList, ElementCodec.decodeAtoms, symbolCodec]

end NativeListRuntimeRepresentation
end Mettapedia.Languages.MeTTa.PureKernel.Universe
