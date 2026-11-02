import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationSection
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationFormComputable
import Mettapedia.GSLT.LanguageDef.EffectiveSection

/-!
# The canonical section of a calculus with replication is effective

The canonical form with replication is computable on codes (`ReplicationCodes.canonR_codeComputable`): a computable
function on numbers takes the code of every pattern to the code of its canonical form, absorbing copies of replicated
components round by round. So the canonical section of every calculus with restriction and replication is effective
(`replicationCanonicalSection_effective`), and its static equivalence, the laws of replication among them, is
decidable along every computable family of closed processes (`replicationStaticEquivalence_computablePred`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open RestrictionBlocks

/-- **The canonical section of a calculus with replication is effective.** -/
theorem replicationCanonicalSection_effective (theory : IGSLT) (block : ReplicationBlock)
    [laws : ReplicationLanguage theory.presentation.presentation.language block] :
    (replicationCanonicalSection theory block).Effective := by
  obtain ⟨track, computable, tracks⟩ := ReplicationCodes.canonR_codeComputable block
  exact ⟨track, computable, fun term => (tracks term.1).symm⟩

/-- **The static equivalence of a calculus with replication is decidable** along every family of closed processes
whose codes are computable. -/
theorem replicationStaticEquivalence_computablePred (theory : IGSLT) (block : ReplicationBlock)
    [laws : ReplicationLanguage theory.presentation.presentation.language block]
    {left right : ℕ → theory.toGSLT.Term}
    (leftComputable : Computable fun index => theory.termCode (left index))
    (rightComputable : Computable fun index => theory.termCode (right index)) :
    ComputablePred fun index => theory.toGSLT.equations.r (left index) (right index) :=
  (replicationCanonicalSection_effective theory block).computablePred leftComputable rightComputable

end Mettapedia.GSLT.LanguageDef
