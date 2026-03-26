import Mettapedia.Languages.Metamath.MMLean4Bridge
import Mettapedia.Languages.Metamath.GroundedSemantics
import Mettapedia.Languages.Metamath.LanguageDefDSL
import Mettapedia.Languages.Metamath.BridgeConformance
import Mettapedia.Languages.Metamath.Fixtures
import Mettapedia.Languages.Metamath.CommentConformance
import Mettapedia.Languages.Metamath.Simulation
import Mettapedia.Languages.Metamath.AcceptanceEquivalence

/-!
# Metamath Bridge Surface

Positive example:
- this umbrella exposes the verified `mm-lean4` bridge layer used for rebuilding
  Metamath semantics in `mettapedia`

Negative example:
- this umbrella does not reintroduce the deleted opaque-hook `LanguageDef` lane
-/
