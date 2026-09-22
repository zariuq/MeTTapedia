import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Data.List.Nodup

/-!
# Gluing two extensions of one base presentation

Independent guest languages can retain disjoint symbol tags.  Extensions of
a common presentation instead need to identify their shared declarations.
The list-level operation here retains the left presentation and appends right
declarations whose keys do not already occur in the base.

The operation alone does not establish that its arguments extend the base,
that filtered declarations are retained in the left presentation, or that the
result validates.  Those are separate compatibility obligations; no universal
property is asserted here.

A general obstruction is independent of the chosen operation: distinct
constructors with the same label cannot both belong to a presentation with
duplicate-free constructor labels.
-/

namespace Mettapedia.GSLT.LanguageDef.DialectGluing

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Keep every left declaration and append right declarations whose label or
name is absent from the base.  Compatibility and validation are separate
conditions on this list-level combination. -/
def glue (name : String) (base left right : LanguageDef) : LanguageDef :=
  { name
    types := left.types ++
      right.types.filter (fun declaration =>
        !(base.typeNames.contains declaration.name))
    terms := left.terms ++
      right.terms.filter (fun rule => !(base.terms.any (·.label == rule.label)))
    equations := left.equations ++
      right.equations.filter (fun equation =>
        !(base.equations.any (·.name == equation.name)))
    rewrites := left.rewrites ++
      right.rewrites.filter (fun rewrite =>
        !(base.rewrites.any (·.name == rewrite.name))) }

/-- Distinct constructors sharing a label cannot coexist in any presentation
whose constructor labels are duplicate-free. -/
theorem not_nodup_labels_of_constructor_clash (presentation : LanguageDef)
    {left right : GrammarRule}
    (leftMember : left ∈ presentation.terms)
    (rightMember : right ∈ presentation.terms)
    (sameLabel : left.label = right.label)
    (distinct : left ≠ right) :
    ¬ (presentation.terms.map (·.label)).Nodup := by
  intro nodup
  have injective := List.inj_on_of_nodup_map nodup
  exact distinct (injective leftMember rightMember sameLabel)

#print axioms not_nodup_labels_of_constructor_clash

end Mettapedia.GSLT.LanguageDef.DialectGluing
