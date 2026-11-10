import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationPayloads
import Mettapedia.GSLT.LanguageDef.PatternABTCarrier
import Mettapedia.GSLT.LanguageDef.SignatureIndexedABTHeadMap
import Mathlib.Logic.Equiv.List
import Mathlib.Tactic.DeriveEncodable

/-! # Authored binding patterns in the transform head representation

This interpretation uses injective natural codes, not hashes. Schematic
free names use the distinct hole tag; object variables remain ABT indices.
Encoding a name does not assign it a value. A runtime symbol table may use a
different representation after proving its own correspondence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Binding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open InferenceSupportIndexedABTLowering (PatternABTHead)
open SignatureIndexedABT

private def scalarCode (text : String) : List Nat := text.toList.map Char.toNat
private def scalarRead (points : List Nat) : Option String := some (String.ofList (points.map Char.ofNat))

private theorem scalarRead_code (text : String) : scalarRead (scalarCode text) = some text := by
  simp [scalarRead, scalarCode, List.map_map, Function.comp_def]

private instance stringEncoding : Encodable String :=
  Encodable.ofLeftInjection scalarCode scalarRead scalarRead_code

deriving instance Encodable for CollType
deriving instance Encodable for PatternABTHead

def encodeHead : PatternABTHead → Payloads.Head
  | .free name => .hole (Encodable.encode name)
  | head => .symbol (Encodable.encode head)

def decodeHead : Payloads.Head → Option PatternABTHead
  | .hole code => PatternABTHead.free <$> Encodable.decode code
  | .symbol code => do
      let head ← (Encodable.decode code : Option PatternABTHead)
      match head with
      | .free _ => none
      | _ => some head
  | _ => none

theorem decode_encode_head (head : PatternABTHead) : decodeHead (encodeHead head) = some head := by
  cases head <;> simp [encodeHead, decodeHead]

theorem encodeHead_injective : Function.Injective encodeHead := by
  intro first second same
  have decoded := congrArg decodeHead same
  simpa only [decode_encode_head, Option.some.injEq] using decoded

def lowerPattern (pattern : Pattern) : Payloads.Term :=
  mapHeads encodeHead (PatternABTCarrier.lower pattern)

theorem lowerPattern_eq_iff_alpha (first second : Pattern) :
    lowerPattern first = lowerPattern second ↔ first.AlphaEquiv second := by
  constructor
  · intro same
    exact (PatternABTCarrier.lower_eq_iff_alpha first second).mp
      (mapHeads_injective encodeHead encodeHead_injective _ _ same)
  · intro same
    exact congrArg (mapHeads encodeHead) ((PatternABTCarrier.lower_eq_iff_alpha first second).mpr same)

theorem lowerPattern_scope (depth : Nat) (pattern : Pattern) :
    Term.supportedAt depth (lowerPattern pattern) = pattern.isWellScopedAt depth := by
  rw [lowerPattern, mapHeads_scope, PatternABTCarrier.lower_scope]

theorem lowerPattern_substitution
    (assignment : Mettapedia.OSLF.MeTTaIL.ContextSubstitution.Assignment) (pattern : Pattern) :
    lowerPattern (Mettapedia.OSLF.MeTTaIL.ContextSubstitution.substitute assignment pattern) =
      Term.substituteMany (fun index => lowerPattern (assignment index)) (lowerPattern pattern) := by
  rw [lowerPattern, PatternABTCarrier.lower_substitute, mapHeads_substitute]
  rfl

theorem object_variable_is_not_schema_hole (index : Nat) (name : String) :
    lowerPattern (.bvar index) ≠ lowerPattern (.fvar name) := by
  intro same
  have alpha := (lowerPattern_eq_iff_alpha _ _).mp same
  simp [Pattern.AlphaEquiv, Pattern.eraseBinderMetadata] at alpha

theorem schema_hole_is_not_quoted_handle (name : String) (handle : Nat) :
    encodeHead (.free name) ≠ Payloads.Head.quotedRule handle := by
  simp [encodeHead]

theorem alpha_renamed_binder_agrees (first second : String) (body : Pattern) :
    lowerPattern (.lambda (some first) body) = lowerPattern (.lambda (some second) body) := by
  apply (lowerPattern_eq_iff_alpha _ _).mpr
  simp [Pattern.AlphaEquiv, Pattern.eraseBinderMetadata]

#print axioms encodeHead_injective
#print axioms lowerPattern_substitution
#print axioms lowerPattern_eq_iff_alpha

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Binding
