import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeACUEquationCompilation
import Mettapedia.Languages.Maude.BagCardinality
import Mettapedia.Languages.Maude.BagIdempotence

/-! Equation-stage controls distinguish scalar equations, ground ACU
extension and the explicitly justified pointwise idempotence strategy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUEquationCompilation.Controls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def groundCarrierRow : Maude.Row := ⟨"replace-a", [], [],
  Maude.BagCardinality.token "a", Maude.BagCardinality.token "b"⟩
def variableCarrierRow : Maude.Row := ⟨"erase-bag", [("B", "Bag")], [],
  .var "B", Maude.BagCardinality.operation.unit⟩

#guard groundCarrierRow.check Maude.Examples.cardinality.signature
#guard variableCarrierRow.check Maude.Examples.cardinality.signature
#guard (equationRule? Maude.BagCardinality.operation groundCarrierRow 0).map (·.left) == some
  (ACUBagPresentation.pack (ACUBagCompilation.wrapperName Maude.BagCardinality.operation.declaration)
    [Maude.BagCardinality.token "a"] (some ACUBagCompilation.restName))
#guard (equationRule? Maude.BagCardinality.operation groundCarrierRow 0).map (·.right) == some
  (ACUBagPresentation.pack (ACUBagCompilation.wrapperName Maude.BagCardinality.operation.declaration)
    [Maude.BagCardinality.token "b"] (some ACUBagCompilation.restName))
#guard (equationRule? Maude.BagCardinality.operation variableCarrierRow 0).isNone
#guard !(prepare Maude.BagIdempotence.operation).isOk
#guard (prepareIdempotence Maude.BagIdempotence.operation).isOk
#guard !(prepareIdempotence Maude.BagCardinality.operation).isOk

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.ACUEquationCompilation.Controls
