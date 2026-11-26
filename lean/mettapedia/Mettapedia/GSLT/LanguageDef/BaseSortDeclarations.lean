import Mettapedia.OSLF.MeTTaIL.Syntax

/-! Builders for declarations whose explicit type annotations are base sorts. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BaseSortDeclarations

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Preserve the order and names of the context entries. -/
abbrev context (entries : List (String × String)) : List (String × TypeExpr) :=
  entries.map fun entry => (entry.1, .base entry.2)

abbrev constructor (label category : String) (parameters : List (String × String))
    (policy : Option TermEvalPolicy := none) : GrammarRule where
  label
  category
  params := parameters.map fun parameter => .simple parameter.1 (.base parameter.2)
  syntaxPattern := [.terminal label]
  evalPolicy? := policy

abbrev rule (name : String) (annotations : List (String × TypeExpr))
    (premises : List Premise) (left right : Pattern) : RewriteRule where
  name
  typeContext := annotations
  premises
  left
  right

attribute [simp] context rule

end Mettapedia.GSLT.LanguageDef.BaseSortDeclarations
