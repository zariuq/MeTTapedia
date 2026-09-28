import Mettapedia.OSLF.Syntax.FiniteRuleProofData

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.DataControls
open Mettapedia.OSLF.Binding.WireCodec

/-- The one-sided generic label contract permits decoding aliases. -/
def aliasLabel : Codec Bool where
  put b := if b then .atom 1 else .atom 0
  get
    | .atom 0 => some false
    | .atom 1 | .atom 2 => some true
    | _ => none
  get_put b := by cases b <;> rfl

theorem arbitrary_label_need_not_be_canonical :
    getWire aliasLabel (.pair (.atom 2) (.atom 0)) = some (.node true []) ∧
    putWire aliasLabel (.node true []) ≠ .pair (.atom 2) (.atom 0) :=
  ⟨rfl, by intro equal; cases equal⟩

theorem concrete_label_preserves_the_input :
    dataWireCodec.get (.pair (.atom 2) (.atom 0)) = some (.node (.atom 2) []) ∧
    dataWireCodec.put (.node (.atom 2) []) = .pair (.atom 2) (.atom 0) := ⟨rfl, rfl⟩

theorem malformed_children_rejected :
    dataWireCodec.get (.pair (.atom 2) (.atom 1)) = none := rfl

end Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire.DataControls
