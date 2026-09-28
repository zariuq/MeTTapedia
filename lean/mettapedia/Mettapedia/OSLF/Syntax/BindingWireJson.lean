import Mettapedia.OSLF.Syntax.BindingWireData
import Lean.Data.Json

/-! JSON is an external transport adapter. The qualified native codec imports
`WireData` and the byte codec, without importing this module. Lean's current
JSON representation and UTF-8 library have a classical dependency. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.WireCodec

def Data.toJson : Data → Lean.Json
  | .atom n => Lean.toJson n
  | .pair first second => .arr #[first.toJson, second.toJson]

def Data.ofJson : Lean.Json → Option Data
  | .arr fields =>
      if h : fields.size = 2 then do
        return .pair (← ofJson (fields[0]'(by omega))) (← ofJson (fields[1]'(by omega)))
      else none
  | .num value => (Lean.Json.num value).getNat?.toOption.map .atom
  | _ => none
termination_by json => sizeOf json
decreasing_by
  all_goals
    apply Nat.lt_trans (Array.sizeOf_get _ _ _)
    simp only [Lean.Json.arr.sizeOf_spec]
    omega

theorem Data.ofJson_toJson : ∀ data : Data, ofJson data.toJson = some data
  | .atom n => by rw [toJson, ofJson.eq_def]; rfl
  | .pair first second => by
      rw [toJson, ofJson.eq_def]
      change (do return Data.pair (← ofJson first.toJson) (← ofJson second.toJson)) = _
      rw [ofJson_toJson first, ofJson_toJson second]
      rfl

def Codec.toJson {α : Type} (codec : Codec α) (value : α) : Lean.Json := (codec.put value).toJson

def Codec.ofJson {α : Type} (codec : Codec α) (json : Lean.Json) : Option α := do
  codec.get (← Data.ofJson json)

theorem Codec.ofJson_toJson {α : Type} (codec : Codec α) (value : α) :
    codec.ofJson (codec.toJson value) = some value := by
  simp only [Codec.ofJson, Codec.toJson, Data.ofJson_toJson]
  exact codec.get_put value

def sampleJson : Lean.Json := (Data.pair (.atom 17) (.pair (.atom 0) (.atom 9))).toJson

theorem sample_json_roundtrip :
    Data.ofJson sampleJson = some (.pair (.atom 17) (.pair (.atom 0) (.atom 9))) :=
  Data.ofJson_toJson _

theorem json_wrong_arity : Data.ofJson (.arr #[Lean.toJson (0 : Nat)]) = none := by
  rw [Data.ofJson.eq_def]
  rfl

theorem json_wrong_atom : Data.ofJson (.str "0") = none := by rw [Data.ofJson.eq_def]

#print axioms Data.toJson
#print axioms Data.ofJson
#print axioms Data.ofJson_toJson
#print axioms Codec.ofJson_toJson

end Mettapedia.OSLF.Binding.WireCodec
