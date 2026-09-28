import Mettapedia.Languages.Agda.SourceEvidence.ProofControls

namespace Mettapedia.Languages.Agda.SourceEvidence.Codec.Execution
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.StaticSpecification.Examples

/-- info: true -/
#guard_msgs in
#eval (decode (encodeTermEq closedBeta)).isSome

/-- info: true -/
#guard_msgs in
#eval (decode (encodeTermEq closedEta)).isSome

/-- info: true -/
#guard_msgs in
#eval (decode (encodeTyping orderedSpineResult)).isSome

/-- info: false -/
#guard_msgs in
#eval (decode (.node 3 [.atom 0, encodeContext .nil, .atom 0] [])).isSome

/-- info: false -/
#guard_msgs in
#eval (decodeAt (.typing .nil (.sort 0) (Ty.universe 0))
  (encodeTyping directSortTyping)).isSome

/-- info: false -/
#guard_msgs in
#eval decide (encodeTermEq Controls.firstThenSecond = encodeTermEq Controls.secondThenFirst)

/-- A small execution of the terminating search, using only Prop inhabitation. -/
def recoveredEmpty : Recovered (.context .nil) := recover (.context .nil) ⟨.nil⟩

/-- info: true -/
#guard_msgs in
#eval (decodeNat (.context .nil) recoveredEmpty.code).isSome

end Mettapedia.Languages.Agda.SourceEvidence.Codec.Execution
