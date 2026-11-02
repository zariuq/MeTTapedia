import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketEncoding
import Mettapedia.GSLT.Parsing.SourcePacketActions
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CettaWireAtom

/-! The exported constructor actions produce the same ordered packet data
used by source-certificate reconstruction. Slot selection is explicit. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketActionBridge

open Mettapedia.GSLT.Parsing
open Mettapedia.GSLT.LanguageDef.CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

theorem children_exact (values : List Term) :
    CettaWireAtom.encode (SourcePacketActions.children values) =
      SourcePacketEncoding.children (CettaWireAtom.encodeMany values) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [SourcePacketActions.children, CettaWireAtom.encode, CettaWireAtom.encodeMany,
      SourcePacketEncoding.children, ih]

theorem node_exact (label : String) (values : List Term) :
    CettaWireAtom.encode (SourcePacketActions.node label values) =
      SourcePacketEncoding.structural label (CettaWireAtom.encodeMany values) := by
  simp only [SourcePacketActions.node, CettaWireAtom.encode, CettaWireAtom.encodeMany,
    SourcePacketEncoding.structural, children_exact]

theorem structural_action (label : String) (slots : List Term) (positions : List Nat) :
    ((SourcePacketActions.structural label positions).execute slots).map CettaWireAtom.encode =
      (positions.mapM fun position => slots[position]?).map
        (fun values => SourcePacketEncoding.structural label (CettaWireAtom.encodeMany values)) := by
  rw [SourcePacketActions.structural_execute]
  cases positions.mapM (fun position => slots[position]?) with
  | none => rfl
  | some values => exact congrArg some (node_exact label values)

theorem lexical_action (label : String) (point : Nat) (rest : List Term) :
    ((SourcePacketActions.lexical label).execute (.application "cp" [.natural point] :: rest)).map
      CettaWireAtom.encode = some (SourcePacketEncoding.lexical label point) := rfl

#print axioms structural_action
#print axioms lexical_action

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketActionBridge
