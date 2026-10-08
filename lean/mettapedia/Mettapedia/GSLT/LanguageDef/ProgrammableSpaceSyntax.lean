import Mettapedia.GSLT.LanguageDef.CertificateGSLTWireFormat
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Authored syntax as inert data in a shared atom space

The existing lossless pattern wire format is embedded in the ordinary MeTTa
atom datatype. In particular, bound-variable indices, binder metadata and
collection remainder names survive. The `authored-rewrite` tag requests this
language; its payload does not become an MM2 template merely by being stored.
This is a symbolic data boundary, not a textual parser theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ProgrammableSpaceSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

mutual
  def wireAtom : WireTerm → Atom
    | .symbol name => .symbol name
    | .natural value => .grounded (.int (.ofNat value))
    | .list items => .expression (wireAtoms items)
  termination_by structural value => value

  def wireAtoms : List WireTerm → List Atom
    | [] => []
    | first :: rest => wireAtom first :: wireAtoms rest
  termination_by structural values => values
end

mutual
  def atomWire : Atom → Option WireTerm
    | .symbol name => some (.symbol name)
    | .grounded (.int (.ofNat value)) => some (.natural value)
    | .expression items => .list <$> atomsWire items
    | _ => none
  termination_by structural value => value

  def atomsWire : List Atom → Option (List WireTerm)
    | [] => some []
    | first :: rest => do return (← atomWire first) :: (← atomsWire rest)
  termination_by structural values => values
end

mutual
  @[simp] theorem atomWire_wireAtom (value : WireTerm) :
      atomWire (wireAtom value) = some value := by
    cases value with
    | symbol name => simp only [wireAtom, atomWire]
    | natural value => simp only [wireAtom, atomWire]
    | list items =>
        simp only [wireAtom, atomWire, atomsWire_wireAtoms items]
        rfl
  termination_by structural value

  @[simp] theorem atomsWire_wireAtoms (values : List WireTerm) :
      atomsWire (wireAtoms values) = some values := by
    cases values with
    | nil => simp only [wireAtoms, atomsWire]
    | cons first rest =>
        simp only [wireAtoms, atomsWire, atomWire_wireAtom first, atomsWire_wireAtoms rest]
        rfl
  termination_by structural values
end

theorem wireAtom_injective : Function.Injective wireAtom := by
  intro first second same
  have decoded := congrArg atomWire same
  simpa only [atomWire_wireAtom, Option.some.injEq] using decoded

def encode (term : Pattern) : Atom :=
  .expression [.symbol "authored-rewrite", wireAtom (encodePattern term)]

def decode : Atom → Option Pattern
  | .expression [.symbol "authored-rewrite", payload] => do
      decodePattern (← atomWire payload)
  | _ => none

@[simp] theorem decode_encode (term : Pattern) : decode (encode term) = some term := by
  simp [decode, encode]

theorem encode_injective : Function.Injective encode := by
  intro first second same
  have decoded := congrArg decode same
  simpa only [decode_encode, Option.some.injEq] using decoded

theorem another_language_stays_data (priority inputs outputs : Atom) :
    decode (.expression [.symbol "exec", priority, inputs, outputs]) = none := rfl

theorem bound_and_free_distinct (index : Nat) (name : String) :
    encode (.bvar index) ≠ encode (.fvar name) := by
  intro same
  cases encode_injective same

theorem collection_remainder_retained (kind : CollType) (items : List Pattern)
    (name : String) :
    encode (.collection kind items none) ≠ encode (.collection kind items (some name)) := by
  intro same
  cases encode_injective same

end Mettapedia.GSLT.LanguageDef.ProgrammableSpaceSyntax
