import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
import Mettapedia.Languages.ProcessCalculi.MORK.MatchLookupLocality

/-!
# Lookup-stable extension for PeTTa value matching

Successful matching can add bindings but cannot change an already captured
lookup. The law includes PeTTa's expression-list `cons` view and follows its
independent matching judgment. In particular, a captured space handle remains
the same while query patterns introduce additional variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

mutual
  theorem ValueMatch.lookupExtends {initial final : Subst} {pattern value : Atom}
      (matched : ValueMatch initial pattern value final) : final.lookupExtends initial := by
    cases matched with
    | cons first rest => exact Subst.lookupExtends_trans first.lookupExtends rest.lookupExtends
    | expression _ fields => exact fields.lookupExtends
    | atomic _ atom => exact matchAtom_lookupExtends (matchAtom_complete atom)
    termination_by sizeOf pattern

  theorem ValueMatches.lookupExtends {initial final : Subst} {patterns values : List Atom}
      (matched : ValueMatches initial patterns values final) : final.lookupExtends initial := by
    cases matched with
    | nil => exact Subst.lookupExtends_refl _
    | cons first rest => exact Subst.lookupExtends_trans first.lookupExtends rest.lookupExtends
    termination_by sizeOf patterns
end

theorem matchValue_lookup_extends {initial final : Subst} {pattern value : Atom}
    (matched : matchValue initial pattern value = some final) : final.lookupExtends initial :=
  (matchValue_sound matched).lookupExtends

mutual
  theorem ValueMatch.lookupOutside {initial final : Subst} {pattern value : Atom}
      (matched : ValueMatch initial pattern value final) (name : String)
      (outside : name ∉ atomFreeVars pattern) : Subst.lookup final name = Subst.lookup initial name := by
    cases matched with
    | cons first rest =>
        have parts := outside
        simp only [atomFreeVars, atomFreeVars.atomFreeVarsList, List.mem_append,
          List.not_mem_nil, false_or, or_false, not_or] at parts
        exact (rest.lookupOutside name parts.2).trans (first.lookupOutside name parts.1)
    | expression _ fields => exact fields.lookupOutside name outside
    | atomic _ atom => exact atom.lookupOutside name outside
    termination_by sizeOf pattern

  theorem ValueMatches.lookupOutside {initial final : Subst} {patterns values : List Atom}
      (matched : ValueMatches initial patterns values final) (name : String)
      (outside : name ∉ atomFreeVars.atomFreeVarsList patterns) :
      Subst.lookup final name = Subst.lookup initial name := by
    cases matched with
    | nil => rfl
    | cons first rest =>
        have parts := outside
        simp only [atomFreeVars.atomFreeVarsList, List.mem_append, not_or] at parts
        exact (rest.lookupOutside name parts.2).trans (first.lookupOutside name parts.1)
    termination_by sizeOf patterns
end

theorem matchValue_lookup_outside {initial final : Subst} {pattern value : Atom}
    (matched : matchValue initial pattern value = some final) (name : String)
    (outside : name ∉ atomFreeVars pattern) : Subst.lookup final name = Subst.lookup initial name :=
  (matchValue_sound matched).lookupOutside name outside

namespace MatchExtensionControls

theorem captured_handle_survives_cons_match :
    matchValue [("space", .symbol "&self")] (.expression [.symbol "cons", .var "x", .var "xs"])
      (.expression [.grounded (.int 7), .grounded (.int 8)]) =
      some [("xs", .expression [.grounded (.int 8)]), ("x", .grounded (.int 7)), ("space", .symbol "&self")] := by
  decide +kernel

theorem captured_handle_cannot_be_rebound :
    matchValue [("space", .symbol "&self")] (.var "space") (.symbol "&other") = none := by decide +kernel

end MatchExtensionControls

end Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics
