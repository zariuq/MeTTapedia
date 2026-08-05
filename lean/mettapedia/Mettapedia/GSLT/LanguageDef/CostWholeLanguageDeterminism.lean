import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion
import Mettapedia.GSLT.LanguageDef.CostInteractionClosure

/-!
# Label determinism of the generated Cost language

The generated Cost core language validates with collision-free constructor
labels, so distinct generated rules never share a wire label.  This
discharges the label-determinism hypothesis of the typed fill descent for
every continued interactive GSLT at once.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Two generated Cost rules with one wire label are one rule. -/
theorem CIGSLT.costWholeLanguage_labelDeterministic (source : CIGSLT) :
    WellSorted.LabelDeterministic source.costWholeLanguage := by
  intro left right leftMembership rightMembership labelEq
  have labelsNodup :
      (source.costWholeLanguage.terms.map (·.label)).Nodup := by
    rw [CIGSLT.costWholeLanguage_terms]
    exact LanguageDef.constructorLabels_nodup_of_validate_eq_nil
      source.costCoreLanguage source.costCoreLanguage_validate
  exact List.inj_on_of_nodup_map labelsNodup leftMembership rightMembership
    labelEq

end Mettapedia.GSLT.LanguageDef
