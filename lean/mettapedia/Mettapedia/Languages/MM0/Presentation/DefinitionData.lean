import Mettapedia.Languages.MM0.Presentation.ContextData
import Mettapedia.Languages.MM0.Kernel.Unfolding
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalLookupProgram

/-! # MM0 definition bodies retain dummy sorts and the authored expression -/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions

open Kernel ComputationalContext
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

abbrev DefinitionTable := List (Nat × Definition.Body)

def definitionsOf (table : DefinitionTable) : Definition.Signature := fun symbol => table.lookup symbol

def encodeBody (body : Definition.Body) : Term :=
  .list [.sym "MM0:Definition", encodeNaturals body.dummies, encode body.expression]

def decodeBody : Term → Option Definition.Body
  | .list [.sym "MM0:Definition", dummies, expression] => do
      let dummies ← decodeNaturals dummies
      let expression ← decode expression
      pure ⟨dummies, expression⟩
  | _ => none

@[simp] theorem decodeBody_encode (body : Definition.Body) : decodeBody (encodeBody body) = some body := by
  cases body
  simp [encodeBody, decodeBody]

theorem encodeBody_injective : Function.Injective encodeBody := by
  intro first second same
  have decoded := congrArg decodeBody same
  simpa using decoded

def encodeDefinitions (table : DefinitionTable) : Term := encodeNaturalTable encodeBody table

def encodeBodyResult (body : Option Definition.Body) : Term := encodeLookupResult (body.map encodeBody)

theorem body_kind_is_checked :
    decodeBody (.list [.sym "MM0:TermDecl", encodeNaturals [], encode (.term 0)]) = none := rfl

theorem dummy_order_is_preserved :
    decodeBody (encodeBody ⟨[0, 1, 0], .var 2⟩) = some ⟨[0, 1, 0], .var 2⟩ := decodeBody_encode _

end Mettapedia.Languages.MM0.Presentation.ComputationalDefinitions
