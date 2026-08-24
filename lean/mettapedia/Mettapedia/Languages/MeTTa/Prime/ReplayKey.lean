import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.FibreReplayKey
import Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

/-!
# Replay-key consequences of Prime exact codecs

Prime's abstract exact codec supplies a recovering decoder and therefore an
exact replay key.  Every observation of the retained state is consequently
constant on the codec's key fibres.
-/

namespace Mettapedia.Languages.MeTTa.Prime

open Mettapedia.GSLT.LanguageDef.Cost.Elaboration
open PrimeAbstractImplementationModel

universe uState uValue

/-- The encoding of every Prime exact codec admits exact replay. -/
theorem exactCodec_replayKey_isExact {State : Type uState}
    (codec : ExactCodec State) : ReplayKey.IsExact codec.encode :=
  ⟨{ decode := codec.decode, recovers := codec.decode_encode }⟩

/-- Every observation is supported by the encoding of an exact codec. -/
theorem exactCodec_replayKey_supports
    {State : Type uState} {Value : Type uValue}
    (codec : ExactCodec State) (observation : State → Value) :
    ReplayKey.Supports codec.encode observation :=
  (exactCodec_replayKey_isExact codec).supports observation

#print axioms exactCodec_replayKey_isExact
#print axioms exactCodec_replayKey_supports

end Mettapedia.Languages.MeTTa.Prime
