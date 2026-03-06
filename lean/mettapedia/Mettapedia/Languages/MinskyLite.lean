import Mettapedia.Languages.MinskyLite.LanguageDef
import Mettapedia.Languages.MinskyLite.LookupPlan
import Mettapedia.Languages.MinskyLite.RewriteIR
import Mettapedia.Languages.MinskyLite.TransitionSpec
import Mettapedia.Languages.MinskyLite.SpecProfile

/-!
# MinskyLite

Minimal deterministic two-register machine:
- executable `LanguageDef`
- transition, rewrite, lookup, and syntax-profile artifacts
- Lean-side export surface for mettail-rust consumption
-/
