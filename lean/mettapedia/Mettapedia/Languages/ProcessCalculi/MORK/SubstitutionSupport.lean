import Mettapedia.Languages.ProcessCalculi.MORK.AtomRenaming

/-! A first-lookup substitution leaves terms unchanged when none of their
variables is a key. This is a law of the actual substitution algorithm. -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem applySubst_fixed_of_no_keys (bindings : Subst) : ∀ term : Atom,
    (∀ name ∈ atomFreeVars term, bindings.lookup name = none) → applySubst bindings term = term
  | .var name => by
      intro absent
      simp only [applySubst,absent name (by simp [atomFreeVars]),Option.getD_none]
  | .symbol _ | .grounded _ => by intro _; rfl
  | .expression terms => by
      intro absent
      apply congrArg Atom.expression
      exact list terms absent
where
  list : ∀ terms : List Atom,
      (∀ name ∈ atomFreeVars.atomFreeVarsList terms, bindings.lookup name = none) →
      applySubst.applySubstList bindings terms = terms
    | [] => by intro _; rfl
    | first :: rest => by
        intro absent
        exact congrArg₂ List.cons
          (applySubst_fixed_of_no_keys bindings first
            (fun name present => absent name (List.mem_append_left _ present)))
          (list rest (fun name present => absent name (List.mem_append_right _ present)))

end Mettapedia.Languages.ProcessCalculi.MORK
