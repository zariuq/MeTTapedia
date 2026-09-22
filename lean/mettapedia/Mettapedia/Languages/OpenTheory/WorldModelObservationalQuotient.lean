import Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
import Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient

/-!
# Theorem-list worlds distinguish state equality from observation

The generic observational quotient is inhabited by an existing OpenTheory
world-model reading. For two distinct theorem atoms, commuted revisions
produce different raw lists but the same membership answers. The quotient
map is therefore genuinely noninjective, while the quotient reading still
satisfies the world-model laws. This is a concrete limit on interpreting WM
agreement as literal state equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.WorldModelObservationalQuotient

open Mettapedia.Languages.OpenTheory.WorldModelQueryGSLT
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.OSLF.Framework.WMCalculusObservationalQuotient

/-- On a scope containing two distinct theorems, the observational quotient
forgets list order: its quotient map is not injective. -/
theorem theoremList_classOf_not_injective (atoms : TheoremAtoms)
    (readsBack : atoms.ReadsBack [axiomP, axiomQ]) :
    ¬ Function.Injective (classOf (theoremListReading atoms)) := by
  obtain ⟨_, distinct, agree⟩ :=
    revisionComm_changes_list_keeps_membership atoms readsBack
  exact classOf_not_injective_of_distinct_agree
    (theoremListReading atoms) distinct agree

/-- The quotient reading still interprets the WM calculus soundly, despite
its state carrier identifying distinct raw theorem lists. -/
theorem theoremList_quotient_coreLaws (atoms : TheoremAtoms) :
    (quotientReading (theoremListReading atoms)
      (theoremListReading_coreLaws atoms)).CoreLaws :=
  quotientReading_coreLaws (theoremListReading atoms)
    (theoremListReading_coreLaws atoms)

end Mettapedia.Languages.OpenTheory.WorldModelObservationalQuotient
