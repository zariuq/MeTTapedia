import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! Propose a closed string-list view of computed module data. As with the
existing grammar/profile views, quotation supplies no equality proof or
admission authority; callers must certify the view against the authored data. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

open Lean Elab Term

scoped syntax (name := stringsView) "module_strings_view% " term:max : term

@[term_elab stringsView] unsafe def elabStringsView : TermElab := fun stx _expected => do
  let `(module_strings_view% $source:term) := stx | throwUnsupportedSyntax
  let type := mkApp (mkConst ``Option [Level.zero]) (mkApp (mkConst ``List [Level.zero]) (mkConst ``String))
  let expression ← elabTermEnsuringType source type
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let some values ← Meta.evalExpr (Option (List String)) type expression
    | throwError "the requested module string-list value did not decode"
  pure (toExpr values)

end Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews
