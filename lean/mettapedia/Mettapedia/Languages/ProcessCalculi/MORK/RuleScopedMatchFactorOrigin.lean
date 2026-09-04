import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.RuleScopedMatchSafety

/-!
# Factor origin for rule-scoped MORK matching

Successful compatible matches replay each selected pattern factor from a
concrete carrier in the input space.  The lemmas here are kept separate from
the core rule-scoped safety module so consumers that need only capability
safety do not inherit the stronger exactness dependency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK

/-- A successful compatible MORK match replays each selected pattern factor
from a concrete workspace carrier.  The input equality keeps this lemma usable
at an authored rule boundary without expanding the full pattern in callers. -/
theorem cMatchInputSpecMork_compat_factor_replay_origin
    (space : List Atom) (input : InputSpec) (pattern : Pattern) (factor : Atom)
    (inputExact : input = .compat pattern)
    (factorMember : factor ∈ pattern.atoms)
    {substitution : Subst} {witnesses : List Atom}
    (member : (substitution, witnesses) ∈
      cMatchInputSpecMork [] space input) :
    ∃ carrier ∈ space, applySubst substitution factor = carrier := by
  subst input
  exact cmatchInputSpec_compat_factor_replay_origin space pattern factor
    factorMember (List.mem_map_of_mem member)

/-- Filtering successful compatible MORK matches cannot hide the carrier from
which a selected factor was replayed. -/
theorem cMatchInputSpecMork_filtered_compat_factor_replay_origin
    (space : List Atom) (input : InputSpec) (pattern : Pattern)
    (keep : Subst × List Atom → Bool) (factor : Atom)
    (inputExact : input = .compat pattern)
    (factorMember : factor ∈ pattern.atoms)
    {substitution : Subst}
    (member : substitution ∈
      ((cMatchInputSpecMork [] space input).filter keep).map Prod.fst) :
    ∃ carrier ∈ space, applySubst substitution factor = carrier := by
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, witnesses⟩, filtered, equal⟩ := member
  subst substitution
  exact cMatchInputSpecMork_compat_factor_replay_origin space input pattern
    factor inputExact factorMember (List.mem_filter.mp filtered).1

#print axioms cMatchInputSpecMork_compat_factor_replay_origin
#print axioms cMatchInputSpecMork_filtered_compat_factor_replay_origin

end Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
