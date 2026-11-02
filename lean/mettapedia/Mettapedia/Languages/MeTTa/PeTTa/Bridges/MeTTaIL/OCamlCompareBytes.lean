import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlByteExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlOrderCall
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareWire
import Mettapedia.Languages.OCaml.ByteComparison

/-! Byte traversal reuses the existing byte codec and exact numeric order.
This closes the string case already present in the source value carrier.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareBytes

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution OCamlByteExecution

def bytesTerm (bytes : List UInt8) : Term := encodeList byteTerm bytes

def orderCode : Atom := apply "case" [apply "gslt:ml:order" [.var "first", .var "second"],
  .expression [.expression [.symbol "MlEqualOrder", apply "gslt:ml:compare-bytes" [.var "tail", .var "rest"]],
    .expression [.var "order", .var "order"]]]

private theorem order_returns (state : State) (caller : Subst) (first second : Nat) (result : OCaml.Compared)
    (firstRead : caller.lookup "first" = some (number first))
    (secondRead : caller.lookup "second" = some (number second))
    (orderFresh : caller.lookup "order" = none)
    (tailReturned : PureReturns runtime caller state (apply "gslt:ml:compare-bytes" [.var "tail", .var "rest"])
      state (encoded (view result))) :
    PureReturns runtime caller state orderCode state
      (encoded (view (match (if first < second then Ordering.lt else if first = second then .eq else .gt) with
        | .eq => result | order => .ok (.ok order)))) := by
  have runOrder := OCamlOrderCall.natural_returns state caller _ _ first second
    (bound_returns _ _ _ firstRead) (bound_returns _ _ _ secondRead)
  generalize ordered : (if first < second then Ordering.lt else if first = second then .eq else .gt) = order at runOrder ⊢
  cases order <;> unfold orderCode
  all_goals
    apply pure_case_returns _ _ _ _ _ _ _ _ rfl
    · exact runOrder
    · simp only [ordering, CettaWireAtom.encode, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue.eq_def, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, orderFresh]
      simp [show ("MlEqualOrder" == "MlLessOrder") = false by decide,
        show ("MlEqualOrder" == "MlGreaterOrder") = false by decide]
    · intro selected body selection
      simp only [ordering, CettaWireAtom.encode, SpaceSemantics.selectCase,
        SpaceSemantics.matchValue.eq_def, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, orderFresh] at selection
      simp [show ("MlEqualOrder" == "MlLessOrder") = false by decide,
        show ("MlEqualOrder" == "MlGreaterOrder") = false by decide] at selection
      obtain ⟨rfl, rfl⟩ := selection
      first | exact tailReturned | exact bound_returns _ _ _ (by rfl)

theorem bytes_returns (state : State) (left right : List UInt8) :
    PureReturns runtime [] state
      (apply "gslt:ml:compare-bytes" [encoded (bytesTerm left), encoded (bytesTerm right)]) state
      (encoded (view (OCaml.compareValue (.literal (.string left)) (.literal (.string right))))) := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil =>
      rw [OCaml.bytes_nil_nil]
      metta_call checked
      ml_compare_eval [] unfolding [bytesTerm, encodeList, view, ordering]
    | cons head tail =>
      rw [OCaml.bytes_nil_cons]
      metta_call checked
      ml_compare_eval [] unfolding [bytesTerm, encodeList, view, ordering]
  | cons head tail ih =>
    cases right with
    | nil =>
      rw [OCaml.bytes_cons_nil]
      metta_call checked
      ml_compare_eval [] unfolding [bytesTerm, encodeList, view, ordering]
    | cons other rest =>
      rw [OCaml.bytes_cons_cons]
      have first := byte_returns state head
      have second := byte_returns state other
      have later := ih rest
      metta_call checked
      ml_compare_eval [first, second] unfolding [bytesTerm, encodeList]
      apply order_returns state _ head.toNat other.toNat _ (by rfl) (by rfl) (by rfl)
      metta_capture checked using later unfolding [bytesTerm, encodeList]

#print axioms bytes_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareBytes
