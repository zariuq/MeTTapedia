import Mettapedia.GSLT.LanguageDef.NativeControlCollection
import Mettapedia.GSLT.LanguageDef.NativeControlCase
import Mettapedia.GSLT.LanguageDef.NativeControlLifting
import Mettapedia.GSLT.LanguageDef.NativeControlOnce
import Mettapedia.GSLT.LanguageDef.NativeControlScopedLifting
import Mettapedia.GSLT.LanguageDef.NativeControlCursor
import Mettapedia.GSLT.LanguageDef.NativeControlEffectCursor

/-!
# Native answer-control refinements

Collection, element enumeration, committed case selection, local-relation
outlining and delimited once have executable models with exact observation
comparisons. Transparent local entry preserves cut scopes. Cursor adapters
connect the host-answer protocol, including terminal world effects, to the
existing indexed provider/client machinery.

These modules prove algorithm and interface laws. They do not identify the
models with a C implementation, establish a full PeTTa front end, or prescribe
a new Prime syntax. Source constraint placement, pattern preparation, variable
ownership, exported-value lifetime and resource cleanup remain obligations
of each concrete realization.
-/
