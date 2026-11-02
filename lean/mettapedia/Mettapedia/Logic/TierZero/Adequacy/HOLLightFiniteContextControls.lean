import Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextSource
import Mettapedia.Languages.HOLLight.MeTTa.TypeDefinitionTables

/-!
# Exact finite context roundtrips and malformed-data controls

The positive controls include the existing full primitive context and the
original constant/type declaration table constructors. Negative controls
refuse missing names, conflicting declaration identities and undeclared
constant-schema operators. Identical repeated rows are harmless data.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextControls

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SignatureFormation
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.HOLLight.MeTTa
open HOLLightFiniteContextData HOLLightFiniteContextSource

local instance : DecidableEq TypeOp := SyntaxEncoding.typeOpCodec.decEq
local instance : DecidableEq Const := SyntaxEncoding.constantCodec.decEq
local instance : DecidableEq Ty := SyntaxEncoding.tyCodec.decEq

theorem original_primitive_context_roundtrips :
    (codec.get (codec.put (ofTable DeclarationTable.primitive))).bind decode = some SourceProfile.primitiveContext :=
  wire_decode_ofTable DeclarationTable.primitive

theorem every_original_constant_extension_roundtrips {context : TheoryContext}
    (before : DeclarationTable.Table context) (constant : Const) (schema : Ty)
    (formed : TypeFormed context.signature schema)
    (fresh : .constant (constantName constant) ∉ context.names) :
    (codec.get (codec.put (ofTable (DeclarationTable.addConstant before constant schema formed fresh)))).bind decode =
      some (context.addConstant constant schema formed fresh) :=
  wire_decode_ofTable (DeclarationTable.addConstant before constant schema formed fresh)

theorem every_original_type_extension_roundtrips {context : TheoryContext}
    (before : DeclarationTable.Table context) (request : TypeOperatorDefinitionRequest) (represented : Ty)
    (functionArity : context.signature.typeOperators TypeOp.function = some 2)
    (representedFormed : TypeFormed context.signature represented)
    (fresh : TypeNamesFresh context.names request) :
    (codec.get (codec.put (ofTable (TypeDefinitionTables.extension context before request represented
      functionArity representedFormed fresh)))).bind decode =
        some (context.typeDefinitionExtension request represented functionArity representedFormed fresh) :=
  wire_decode_ofTable (TypeDefinitionTables.extension context before request represented functionArity representedFormed fresh)

def missingName : ContextData := ⟨∅, [(TypeOp.bool, 0)], []⟩
def conflictingArity : ContextData :=
  ⟨{.typeOperator (operatorName TypeOp.bool)}, [(TypeOp.bool, 0), (TypeOp.bool, 1)], []⟩
def repeatedIdentical : ContextData :=
  ⟨{.typeOperator (operatorName TypeOp.bool)}, [(TypeOp.bool, 0), (TypeOp.bool, 0)], []⟩
def shadowProvenance : TypeOp :=
  .mk (operatorName TypeOp.bool) (.defined (.var (Name.global "x") Ty.bool) [])
def conflictingProvenance : ContextData :=
  ⟨{.typeOperator (operatorName TypeOp.bool)}, [(TypeOp.bool, 0), (shadowProvenance, 0)], []⟩
def unknownSchema : ContextData :=
  ⟨{.constant (constantName Const.equality)}, [], [(Const.equality, Ty.bool)]⟩

theorem missing_name_refused : valid missingName = false := by decide
theorem conflicting_arity_refused : valid conflictingArity = false := by decide
theorem conflicting_provenance_refused : valid conflictingProvenance = false := by decide
theorem undeclared_schema_refused : valid unknownSchema = false := by
  simp [valid, unknownSchema, typeFormedB, Ty.bool, signature, HOLLightFiniteSignatureLookup.rowLookup]
theorem identical_repeated_rows_accepted : valid repeatedIdentical = true := by decide

theorem identical_repeated_rows_decode : (decode repeatedIdentical).isSome = true :=
  (decode_isSome_iff repeatedIdentical).mpr ((valid_iff repeatedIdentical).mp identical_repeated_rows_accepted)

end Mettapedia.Logic.TierZero.Adequacy.HOLLightFiniteContextControls
