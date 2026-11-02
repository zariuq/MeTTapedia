import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec

/-!
# Lookup locality of structural matching

A successful match changes no lookup whose name is absent from the pattern.
This includes preservation of absence, not just preservation of already bound
values. It therefore licenses fresh local names in later source continuations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem MatchAtomRel.lookupOutside {initial final : Subst} {pattern value : Atom}
    (matched : MatchAtomRel initial pattern value final) (name : String)
    (outside : name ∉ atomFreeVars pattern) : Subst.lookup final name = Subst.lookup initial name := by
  induction matched with
  | @var_fresh initial slot payload _ =>
      have different : slot ≠ name := by simpa [atomFreeVars, ne_comm] using outside
      simp [Subst.lookup, different]
  | var_bound | symbol | grounded | expr_nil => rfl
  | expr_cons first rest firstIH restIH =>
      have parts := outside
      simp only [atomFreeVars, atomFreeVars.atomFreeVarsList, List.mem_append, not_or] at parts
      exact (restIH parts.2).trans (firstIH parts.1)

theorem matchAtom_lookup_outside {initial final : Subst} {pattern value : Atom}
    (matched : matchAtom initial pattern value = some final) (name : String)
    (outside : name ∉ atomFreeVars pattern) : Subst.lookup final name = Subst.lookup initial name :=
  (matchAtom_sound matched).lookupOutside name outside

end Mettapedia.Languages.ProcessCalculi.MORK
