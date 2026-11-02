import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlVariantOrder
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlTagExecution

/-! The variant helper checks source type identity, separates nullary and
block constructors, then compares constructor ordinals and their fields.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareVariants

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlControllerSource OCamlCompareWire OCamlOrderExecution OCamlTagExecution

private theorem ordinal_at (state : State) (caller : Subst) (first second : Nat)
    (left right : List OCaml.Value)
    (firstRead : caller.lookup "leftOrdinal" = some (number first))
    (secondRead : caller.lookup "rightOrdinal" = some (number second))
    (leftRead : caller.lookup "left" = some (encoded (fieldsTerm left)))
    (rightRead : caller.lookup "right" = some (encoded (fieldsTerm right)))
    (orderFresh : caller.lookup "order" = none)
    (fieldsReturned : PureReturns runtime [] state
      (apply "gslt:ml:compare-fields" [encoded (fieldsTerm left), encoded (fieldsTerm right)]) state
      (encoded (view (OCaml.compareFields left right)))) :
    PureReturns runtime caller state OCamlVariantOrder.code state
      (encoded (view (match (if first < second then Ordering.lt else if first = second then .eq else .gt) with
        | .eq => OCaml.compareFields left right | order => .ok (.ok order)))) := by
  apply OCamlVariantOrder.returns state caller first second _ firstRead secondRead orderFresh
  apply Library.capture checked (head := "gslt:ml:compare-fields") (by decide +kernel)
    _ _ _ _ _ _ (by metta_literal; rfl) rfl
  simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
    leftRead, rightRead, Option.getD_some]
  convert fieldsReturned using 1
  rfl

theorem helper_returns (state : State) (leftType leftTag rightType rightTag : Nat)
    (left right : List OCaml.Value)
    (fieldsReturned : PureReturns runtime [] state
      (apply "gslt:ml:compare-fields" [encoded (fieldsTerm left), encoded (fieldsTerm right)]) state
      (encoded (view (OCaml.compareFields left right)))) :
    PureReturns runtime [] state (apply "gslt:ml:compare-variants"
      [encoded (tagTerm leftType leftTag), encoded (fieldsTerm left),
       encoded (tagTerm rightType rightTag), encoded (fieldsTerm right)]) state
      (encoded (view (OCaml.compareValue (.variant leftType leftTag left) (.variant rightType rightTag right)))) := by
  have first := tag_returns state leftType leftTag
  have second := tag_returns state rightType rightTag
  rw [OCaml.compare_variant]
  by_cases same : leftType = rightType
  · subst rightType
    simp only [ne_eq, not_true_eq_false, if_false]
    cases left with
    | nil =>
      cases right with
      | nil =>
        metta_call checked
        ml_compare_eval [first, second] unfolding [fields_nil]
        exact ordinal_at state _ leftTag rightTag [] [] (by rfl) (by rfl) (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, fields_nil, CettaWireAtom.encode, CettaWireAtom.encodeMany]) (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, fields_nil, CettaWireAtom.encode, CettaWireAtom.encodeMany]) (by rfl) fieldsReturned
      | cons head tail =>
        metta_call checked
        ml_compare_eval [first, second] unfolding [fields_nil, fields_cons, encodeList, view, ordering]
    | cons head tail =>
      cases right with
      | nil =>
        metta_call checked
        ml_compare_eval [first, second] unfolding [fields_nil, fields_cons, encodeList, view, ordering]
      | cons other rest =>
        metta_call checked
        ml_compare_eval [first, second] unfolding [fields_cons, encodeList]
        exact ordinal_at state _ leftTag rightTag (head :: tail) (other :: rest)
          (by rfl) (by rfl) (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, fields_cons, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]) (by simp [Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, fields_cons, encodeList, CettaWireAtom.encode, CettaWireAtom.encodeMany]) (by rfl) fieldsReturned
  · simp only [ne_eq, same, not_false_eq_true, if_true, view]
    metta_call checked
    ml_compare_eval [first, second] unfolding [same]

#print axioms helper_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlCompareVariants
