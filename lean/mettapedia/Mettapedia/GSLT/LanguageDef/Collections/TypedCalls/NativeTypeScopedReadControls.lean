import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeFreshReadControls

/-! # Scoped read instances and occurrence controls -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts
open NativeTypeRecursiveControls (world ops)

theorem same_polymorphic_subject_is_instantiated_twice :
    NativeTypeRecursiveDriver.publishTypes
      (evaluate ops NativeTypeFreshReadControls.source world 4 NativeTypeFreshReadControls.call ⟨[], 0⟩).1 =
        some [Atom.symbol "R"] := by cbv

theorem missing_depth_is_not_empty_typing :
    (evaluate ops NativeTypeFreshReadControls.source world 0 NativeTypeFreshReadControls.call ⟨[], 0⟩).1 = none ∧
    (evaluate ops NativeTypeFreshReadControls.source world 0 NativeTypeFreshReadControls.call ⟨[], 0⟩).1 ≠
      some (.types []) := by simp [evaluate]

def tupleSource : Source :=
  { NativeTypeFreshReadControls.source with rows :=
    NativeTypeFreshReadControls.source.rows ++
      [NativeTypeRecursiveControls.row "tuple-head" (.symbol "TupleTag"),
       NativeTypeRecursiveControls.row "consume-tuple"
         (NativeTypeRecursiveControls.arrow
           [.expression [.symbol "TupleTag", NativeTypeFreshReadControls.list (.symbol "Number"),
             NativeTypeFreshReadControls.list (.symbol "String")]] (.symbol "R"))] }

def tupleCall : Call := .infer true (.expression [.symbol "consume-tuple",
  .expression [.symbol "tuple-head", .symbol "ScopeNil", .symbol "ScopeNil"]])

theorem tuple_parts_get_independent_instances :
    NativeTypeRecursiveDriver.publishTypes (evaluate ops tupleSource world 6 tupleCall ⟨[], 0⟩).1 =
      some [.symbol "R"] ∧
    NativeTypeRecursiveDriver.publishTypes
      (NativeTypeRecursiveDriver.evaluate ops (NativeTypeSourcePorts.primitive tupleSource world) 6 tupleCall) =
      some [] := by cbv

def sharedSource : Source :=
  { NativeTypeFreshReadControls.source with rows :=
    [NativeTypeRecursiveControls.row "heterogeneous" (.expression [.symbol "Pair", .symbol "Number", .symbol "String"]),
     NativeTypeRecursiveControls.row "requires-same"
       (NativeTypeRecursiveControls.arrow [.expression [.symbol "Pair", .var "element", .var "element"]]
         (.symbol "R"))] }

theorem within_signature_equality_is_not_freshened_apart :
    NativeTypeRecursiveDriver.publishTypes (evaluate ops sharedSource world 4
      (.infer true (.expression [.symbol "requires-same", .symbol "heterogeneous"])) ⟨[], 0⟩).1 =
      some [] := by cbv

def subtypeInput : Atom := .expression [.symbol "Pair", .symbol "String", .var "element"]
def subtypeRows : List Atom :=
  [.expression [.symbol ":<", .expression [.symbol "Pair", .var "element", .symbol "Number"],
    .expression [.symbol "Out", .var "element"]]]

theorem subtype_row_does_not_capture_input_variable :
    (ScopedSubtypeReads.query world subtypeRows "result" subtypeInput ⟨[], 0⟩).1 =
      [.expression [.symbol "Out", .symbol "String"]] ∧
    TypeScopeClosure.subtypeQuery world subtypeInput "result" subtypeRows = [] := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads.Controls
