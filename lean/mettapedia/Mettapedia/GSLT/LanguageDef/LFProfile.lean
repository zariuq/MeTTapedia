import Mettapedia.GSLT.LanguageDef.LF.Profiles
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchDemand
import Mettapedia.GSLT.LanguageDef.LF.Canonical
import Mettapedia.GSLT.LanguageDef.LF.ProfileChecker

/-!
# Profile-parametric LF theory

This umbrella exposes the source-extracted basic/indexed PTS lattice, the
frozen DTTBench statement-demand theorem, eta-long canonical forms with
hereditary substitution, and the profile-parametric reference checker.

The checker and canonical-action substrate are deliberately conversion-free.
Conversion-dependent source terms, including DTTBench witnesses, must enter
through a separately proved conversion-capable LF/MIK frontend.
-/
