import Mettapedia.Languages.OpenTheory.Substitution
import Mettapedia.Languages.OpenTheory.CoreRules

/-!
# OpenTheory bridge interface

This module currently exposes provenance-sensitive typed syntax, the pinned
source-compatible substitution model, typed alpha-canonical sequents, and an
executable checker for the first six nonbinding primitive rules.  The checker
has Type-valued one-step certificates, an independent declarative semantics,
exact success and failure correspondence, and a verified Boolean-sequent
profile.  Substitution also
provides the stricter `TermSubst.TypeCorrect` admission profile and its
type-preservation theorem.

It does not yet expose binding rules, theorem substitution, definitions,
recursive article proof trails, article-machine state, reader execution, or an
adequacy theorem for OpenTheory, HOL Light, or HOL4 artifacts.
-/
