import Mettapedia.Languages.IMP.LanguageDef
import Mettapedia.Languages.IMP.LookupPlan
import Mettapedia.Languages.IMP.RewriteIR
import Mettapedia.Languages.IMP.TransitionSpec
import Mettapedia.Languages.IMP.SpecProfile

/-!
# IMP

Imperative core language package:
- Lean `LanguageDef` with explicit continuation/state semantics
- lookup, transition, rewrite, and syntax-profile artifacts
- Lean-side export surface for mettail-rust consumption
-/
