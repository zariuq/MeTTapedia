import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeSyntax
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Step

/-!
# Raw configuration decoding

The executable runtime presents configurations as occurrence-bearing lists.
Decoding forgets occurrence order while retaining multiplicity in the typed
cost configuration.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Decode a raw component list as an unordered typed configuration. -/
def decodeRawConfig (config : RawCostConfig) : CostConfig String :=
  (config.map decodeCostTerm : Multiset (CostTerm String))

@[simp]
theorem decodeRawConfig_append (left right : RawCostConfig) :
    decodeRawConfig (left ++ right) =
      decodeRawConfig left + decodeRawConfig right := by
  simp [decodeRawConfig]

@[simp]
theorem decodeRawConfig_components : ∀ term : RawCostTerm,
    decodeRawConfig term.components = (decodeCostTerm term).components
  | .nil => rfl
  | .signed process signature => rfl
  | .par left right => by
      simp [RawCostTerm.components, decodeCostTerm, CostTerm.components,
        decodeRawConfig_components left, decodeRawConfig_components right]
  | .drop name => rfl
  | .purse surface stack => rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
