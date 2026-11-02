import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTermCodec
import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeTyping
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.Languages.Maude.Examples

/-! Static preparation, retained algebra and portable core controls. These
do not supply executable equation certificates or claim a native Maude core.
The source equation theory remains wider than any currently selected finite
binding or equality-service profile. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.Controls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

def prepared : List Prepared := Maude.Examples.theories.filterMap fun theory => (prepare theory).toOption

#guard prepared.length == 6
#guard prepared.map (fun entry => entry.language.equations.length) == [4, 7, 5, 5, 4, 5]
#guard prepared.all fun entry => entry.equationOrigins.length == entry.language.equations.length &&
  entry.ruleOrigins.length == entry.language.rewrites.length
#guard prepared.all fun entry => entry.language.validate.isEmpty

theorem core_payload_roundtrip (prepared : Prepared) :
    ModuleAlgebra.NativeAuthoring.Wire.language?
      (ModuleAlgebra.NativeAuthoring.Wire.language prepared.language) = some prepared.language :=
  ModuleAlgebra.NativeAuthoring.Wire.language_roundtrip prepared.language

def conditional : Prepared := (prepare Maude.Examples.conditional).toOption.get (by decide_cbv)

/- The condition compares full equational meanings. It is not a child rule
step, and it keeps the Boolean sort of the selected source comparison. -/
#guard (conditional.language.equations[3]?).map (·.premises) == some
  [.relationQuery "maude:equivalent:Bool"
    [.apply "max.le" [.fvar "M", .fvar "N"], .apply "max.true" []]]

#guard checkHasType conditional.language FreeTypeContext.empty []
  (encode (Maude.Examples.numeral "max" 3)) (.base "Nat")
#guard !(checkHasType conditional.language FreeTypeContext.empty [] (.apply "max.true" []) (.base "Nat"))
#guard !(checkHasType conditional.language FreeTypeContext.empty []
  (.apply "max.le" [encode (Maude.Examples.numeral "max" 3)]) (.base "Bool"))

def compoundUnit : Maude.Term := .app "compound.unit" [.app "compound.zero" []]
def compound : Maude.Theory := {
  name := "GOLD-COMPOUND-UNIT"
  signature := ⟨["Element"],
    [⟨"compound.zero", "zero", [], "Element", {constructor := true}⟩,
     ⟨"compound.unit", "unit", ["Element"], "Element", {constructor := true}⟩,
     ⟨"compound.combine", "combine", ["Element", "Element"], "Element",
      {associative := true, commutative := true, identity := some compoundUnit}⟩]⟩}
def compoundPrepared : Prepared := (prepare compound).toOption.get (by decide_cbv)

#guard compound.check
#guard (compoundPrepared.language.equations[2]?).map (·.left) == some
  (.apply "compound.combine" [encode compoundUnit, .fvar "maude:axiom:X"])
#guard (compoundPrepared.language.equations[3]?).map (·.left) == some
  (.apply "compound.combine" [.fvar "maude:axiom:X", encode compoundUnit])

def variableUnit : Maude.Theory := {compound with signature :=
  {compound.signature with operators := compound.signature.operators.map fun declaration =>
    if declaration.id == "compound.combine" then
      {declaration with attributes := {declaration.attributes with identity := some (.var "X")}}
    else declaration}}

#guard !variableUnit.check
#guard (prepare variableUnit).toOption.isNone
#guard (decode? (.lambda none (.bvar 0))).isNone
#guard (decode? (.collection .hashBag [] none)).isNone

def extraConditionVariable : Maude.Row :=
  ⟨"extra-variable", [("N", "Nat"), ("M", "Nat")],
    [⟨Maude.Examples.binary "max.le" Maude.Examples.m Maude.Examples.n, .app "max.true" []⟩],
    Maude.Examples.n, Maude.Examples.n⟩

#guard extraConditionVariable.check Maude.Examples.conditional.signature
#guard !extraConditionVariable.inputsBound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.Controls
