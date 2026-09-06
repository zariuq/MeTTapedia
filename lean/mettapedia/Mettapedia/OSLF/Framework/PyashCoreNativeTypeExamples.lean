import Mettapedia.OSLF.Framework.PyashCoreModel

namespace Mettapedia.OSLF.Framework.PyashCoreInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Positive native-type witness: a canonical Pyash state shape is accepted by `pyashStateTop`. -/
def pyashStateTopPositiveExample : Pattern :=
  .apply "State"
    [ .apply "DeriveSignature" []
    , .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], .apply "RTNil" []]
    , .apply "Signature" [.apply "VRead" [], .apply "RTNil" []]
    , .apply "Ok" []
    ]

/-- Negative native-type witness: non-`State` constructor is rejected by `pyashStateTop`. -/
def pyashStateTopNegativeNonStateExample : Pattern :=
  .apply "DeriveSignature" []

/-- Negative native-type witness: malformed outcome constructor is rejected by `pyashStateTop`. -/
def pyashStateTopNegativeBadOutcomeExample : Pattern :=
  .apply "State"
    [ .apply "DeriveSignature" []
    , .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], .apply "RTNil" []]
    , .apply "Signature" [.apply "VRead" [], .apply "RTNil" []]
    , .apply "VRead" []
    ]

theorem pyashStateTop_accepts_positive_example :
    (langOSLF pyashCore "State").satisfies
      pyashStateTopPositiveExample pyashStateTop.pred := by
  rw [pyashStateTop_satisfies_iff]
  unfold pyashStateTopPositiveExample
  simp [isPyashState, isPyashInstr, isPyashSentence, isPyashMood, isPyashVerb,
    isPyashRoleTypes, isPyashSignature, isPyashOutcome]

theorem pyashStateTop_rejects_non_state_example :
    ¬ (langOSLF pyashCore "State").satisfies
      pyashStateTopNegativeNonStateExample pyashStateTop.pred := by
  rw [pyashStateTop_satisfies_iff]
  unfold pyashStateTopNegativeNonStateExample
  simp [isPyashState]

theorem pyashStateTop_rejects_bad_outcome_example :
    ¬ (langOSLF pyashCore "State").satisfies
      pyashStateTopNegativeBadOutcomeExample pyashStateTop.pred := by
  rw [pyashStateTop_satisfies_iff]
  unfold pyashStateTopNegativeBadOutcomeExample
  simp [isPyashState, isPyashInstr, isPyashSentence, isPyashMood, isPyashVerb,
    isPyashRoleTypes, isPyashSignature, isPyashOutcome]

end Mettapedia.OSLF.Framework.PyashCoreInstance
