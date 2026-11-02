import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderCall

/-! Constructor-order comparison continues into fields only when the
ordinals agree. The expression is the continuation in the loaded source.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlVariantOrder

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution

def code : Atom := apply "case" [apply "gslt:ml:order" [.var "leftOrdinal", .var "rightOrdinal"],
  .expression [.expression [.symbol "MlEqualOrder", apply "gslt:ml:compare-fields" [.var "left", .var "right"]],
    .expression [.var "order", .var "order"]]]

theorem returns (state : State) (caller : Subst) (first second : Nat) (result : OCaml.Compared)
    (firstRead : caller.lookup "leftOrdinal" = some (number first))
    (secondRead : caller.lookup "rightOrdinal" = some (number second))
    (orderFresh : caller.lookup "order" = none)
    (fieldsReturned : PureReturns runtime caller state (apply "gslt:ml:compare-fields" [.var "left", .var "right"])
      state (encoded (view result))) :
    PureReturns runtime caller state code state
      (encoded (view (match (if first < second then Ordering.lt else if first = second then .eq else .gt) with
        | .eq => result | order => .ok (.ok order)))) := by
  have runOrder := OCamlOrderCall.natural_returns state caller _ _ first second
    (bound_returns _ _ _ firstRead) (bound_returns _ _ _ secondRead)
  generalize ordered : (if first < second then Ordering.lt else if first = second then .eq else .gt) = order at runOrder ⊢
  cases order <;> unfold code
  all_goals
    apply pure_case_returns _ _ _ _ _ _ _ _ rfl
    · exact runOrder
    · simp only [ordering, CettaWireAtom.encode, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue.eq_def, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
        orderFresh]
      simp [show ("MlEqualOrder" == "MlLessOrder") = false by decide,
        show ("MlEqualOrder" == "MlGreaterOrder") = false by decide]
    · intro selected body selection
      simp only [ordering, CettaWireAtom.encode, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue.eq_def, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom,
        orderFresh] at selection
      simp [show ("MlEqualOrder" == "MlLessOrder") = false by decide,
        show ("MlEqualOrder" == "MlGreaterOrder") = false by decide] at selection
      obtain ⟨rfl, rfl⟩ := selection
      first
      | exact fieldsReturned
      | exact bound_returns _ _ _ (by rfl)

#print axioms returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlVariantOrder
