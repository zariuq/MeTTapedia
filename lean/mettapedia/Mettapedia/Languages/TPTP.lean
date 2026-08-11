import Mettapedia.Languages.TPTP.StatusSemantics
import Mettapedia.Languages.TPTP.NIKAuthority
import Mettapedia.Languages.TPTP.ProblemAuthority
import Mettapedia.Languages.TPTP.NIKDefault
import Mettapedia.Languages.TPTP.GroundCNFAuthority

/-!
# TPTP and TSTP proof authority

This entry point exposes the fail-closed status vocabulary, the open family of
local rule authorities, chronological DAG replay, and whole-problem authority
composition.  Concrete TPTP dialects and rule registries remain responsible
for their own parsing, source authentication, semantic status meanings, and
global discharge theorems.
-/
