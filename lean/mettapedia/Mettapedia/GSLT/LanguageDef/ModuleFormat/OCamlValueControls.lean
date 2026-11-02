import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading

/-! Closure identity includes its kind, code group/slot and captured
environment. Equal displayed arithmetic values still encode equally.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ValueControls

open Mettapedia.Languages

theorem same_closure : value (.closure (.recursive 7 0) [.literal (.integer 7)]) =
    value (.closure (.recursive 7 0) [.literal (.integer (3 + 4))]) := rfl

theorem different_slots : value (.closure (.recursive 7 0) []) ≠ value (.closure (.recursive 7 1) []) := by
  intro same
  have sourceSame := value_injective same
  cases sourceSame

theorem different_kinds : value (.closure (.lambda 7) []) ≠ value (.closure (.recursive 7 0) []) := by
  intro same
  have sourceSame := value_injective same
  cases sourceSame

theorem different_captures : value (.closure (.lambda 7) [.literal (.integer 7)]) ≠
    value (.closure (.lambda 7) [.literal (.integer 9)]) := by
  intro same
  have sourceSame := value_injective same
  cases sourceSame

#print axioms different_slots
#print axioms different_kinds
#print axioms different_captures

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ValueControls
