import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEncodingTyping
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlVariableLookup
import Mettapedia.OSLF.MeTTaIL.GeneralTypedVectorRuleAdmission

/-! A source-schema typing witness for generated O0 capture names. This
assignment is used only in proofs; emitted declarations and inference are
unchanged. Fresh pattern and lookup captures inhabit the value sort.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def captureSort (name : String) : TypeExpr :=
  if name = "ml:environment" ∨ name = "ml:tail" then .base "MlEnvironment"
  else if name = "ml:continuation" then .base "MlContinuation"
  else if name = "ml:body" then .base "MlCode"
  else if name = "ml:later" then .base "MlClauses"
  else .base "MlValue"

def captureContext : FreeTypeContext := fun name => some (captureSort name)

theorem capture_hole_typed (language : LanguageDef) (bound : List TypeExpr) (name : String) :
    HasType language captureContext bound (hole name) (captureSort ("ml:" ++ name)) := .fvar rfl

theorem environment_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "environment") (.base "MlEnvironment") := by
  simpa [captureSort] using capture_hole_typed language bound "environment"

theorem continuation_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "continuation") (.base "MlContinuation") := by
  simpa [captureSort] using capture_hole_typed language bound "continuation"

theorem body_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "body") (.base "MlCode") := by
  simpa [captureSort] using capture_hole_typed language bound "body"

theorem later_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "later") (.base "MlClauses") := by
  simpa [captureSort] using capture_hole_typed language bound "later"

theorem argument_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "argument") (.base "MlValue") := by
  simpa [captureSort] using capture_hole_typed language bound "argument"

theorem variable_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "variable") (.base "MlValue") := by
  simpa [captureSort] using capture_hole_typed language bound "variable"

theorem tail_capture_typed (language : LanguageDef) (bound : List TypeExpr) :
    HasType language captureContext bound (hole "tail") (.base "MlEnvironment") := by
  simpa [captureSort] using capture_hole_typed language bound "tail"

theorem captureSort_default (name : String) (byte : UInt8)
    (head : name.toByteArray.data[3]? = some byte)
    (environment : byte ≠ 101) (tail : byte ≠ 116) (continuation : byte ≠ 99)
    (body : byte ≠ 98) (later : byte ≠ 108) : captureSort name = .base "MlValue" := by
  have different (reserved : String) (value : UInt8)
      (position : reserved.toByteArray.data[3]? = some value) (distinct : byte ≠ value) : name ≠ reserved := by
    intro same
    apply distinct
    exact Option.some.inj (head.symm.trans (same ▸ position))
  have noEnvironment := different "ml:environment" 101 rfl environment
  have noTail := different "ml:tail" 116 rfl tail
  have noContinuation := different "ml:continuation" 99 rfl continuation
  have noBody := different "ml:body" 98 rfl body
  have noLater := different "ml:later" 108 rfl later
  simp only [captureSort, noEnvironment, noTail, noContinuation, noBody, noLater, or_self, if_false]

theorem pattern_capture_typed (language : LanguageDef) (bound : List TypeExpr) (index : Nat) :
    HasType language captureContext bound (hole ("pattern:" ++ toString index)) (.base "MlValue") := by
  have head : ("ml:" ++ ("pattern:" ++ toString index)).toByteArray.data[3]? = some (112 : UInt8) := by
    simp only [String.toByteArray_append, ByteArray.data_append]
    change (#[109, 108, 58] ++ (#[112, 97, 116, 116, 101, 114, 110, 58] ++ (toString index).toByteArray.data))[3]? = _
    simp
  rw [← captureSort_default _ 112 head (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact capture_hole_typed language bound _

theorem skip_capture_typed (language : LanguageDef) (bound : List TypeExpr) (index : Nat) :
    HasType language captureContext bound (hole ("skip:" ++ toString index)) (.base "MlValue") := by
  have head : ("ml:" ++ ("skip:" ++ toString index)).toByteArray.data[3]? = some (115 : UInt8) := by
    simp only [String.toByteArray_append, ByteArray.data_append]
    change (#[109, 108, 58] ++ (#[115, 107, 105, 112, 58] ++ (toString index).toByteArray.data))[3]? = _
    simp
  rw [← captureSort_default _ 115 head (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact capture_hole_typed language bound _

theorem extend_schema_typed (language : LanguageDef) (terms : language.terms = baseLanguage.terms)
    (free : FreeTypeContext) (bound : List TypeExpr) (bindings : List Pattern) (captured : Pattern)
    (items : ∀ item ∈ bindings, HasType language free bound item (.base "MlValue"))
    (environment : HasType language free bound captured (.base "MlEnvironment")) :
    HasType language free bound (extend bindings captured) (.base "MlEnvironment") := by
  induction bindings generalizing captured with
  | nil => exact environment
  | cons first rest ih =>
      apply ih _ (fun item member => items item (List.mem_cons_of_mem first member))
      exact nonbare_constructor_typed terms [("head", .base "MlValue"), ("tail", .base "MlEnvironment")] _
        (by decide +kernel) (.cons (items first List.mem_cons_self) (.cons environment .nil))

theorem grammar_labels_unique (language : LanguageDef) (terms : language.terms = baseLanguage.terms) :
    (language.terms.map GrammarRule.label).Nodup := by
  rw [terms]
  decide +kernel

#print axioms captureSort_default
#print axioms pattern_capture_typed
#print axioms skip_capture_typed
#print axioms extend_schema_typed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
