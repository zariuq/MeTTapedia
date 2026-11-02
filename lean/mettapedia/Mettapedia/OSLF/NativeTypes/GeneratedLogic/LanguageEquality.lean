import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Equality of languages, decided

Languages have decidable equality, so a driver or a set of canonical forms proved for one language serves exactly that
language wherever it is met, read from a file or declared.
-/

namespace Mettapedia.OSLF.MeTTaIL.Syntax

deriving instance DecidableEq for Equation
deriving instance DecidableEq for RewriteRule
deriving instance DecidableEq for LanguageDef

end Mettapedia.OSLF.MeTTaIL.Syntax
