import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Section
import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.FormComputable
import Mettapedia.GSLT.LanguageDef.EffectiveSection

/-!
# The canonical section of a calculus with restriction is effective

The canonical form of restriction blocks is computable on codes (`FormCodes.canon_codeComputable`): a computable
function on numbers takes the code of every pattern to the code of its canonical form. So the canonical section of
every calculus with restriction is effective (`blockCanonicalSection_effective`), and its static equivalence is
decidable along every computable family of closed processes (`blockStaticEquivalence_computablePred`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open RestrictionBlocks

/-- **The canonical section of a calculus with restriction is effective.** -/
theorem blockCanonicalSection_effective (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block] :
    (blockCanonicalSection theory block).Effective := by
  obtain ⟨track, computable, tracks⟩ := FormCodes.canon_codeComputable block
  exact ⟨track, computable, fun term => (tracks term.1).symm⟩

/-- **The static equivalence of a calculus with restriction is decidable** along every family of closed processes
whose codes are computable. -/
theorem blockStaticEquivalence_computablePred (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block] {left right : ℕ → theory.toGSLT.Term}
    (leftComputable : Computable fun index => theory.termCode (left index))
    (rightComputable : Computable fun index => theory.termCode (right index)) :
    ComputablePred fun index => theory.toGSLT.equations.r (left index) (right index) :=
  (blockCanonicalSection_effective theory block).computablePred leftComputable rightComputable

end Mettapedia.GSLT.LanguageDef
