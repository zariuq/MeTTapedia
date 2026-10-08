import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualSums
import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Full-motive sum elimination in the typed contextual quotient

The source's actual pair rules satisfy the shared stable-sum capability.
Its context comparison and motive elimination therefore apply to arbitrary
typed quotient families, including families over the complete pair context.
The context-substitution square compares the independently selected sum and
tuple lifts, and elimination recovers the complete supplied body class.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.SumElimination

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization
open Mettapedia.TypeTheory.ContextualSumComprehension

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

noncomputable def stable : StableSums (QuotientCwf.cwf levels) where
  operations := Sums.operations levels
  beta := Sums.beta levels
  eta := Sums.eta levels
  substitution := Sums.substitution levels

theorem context_comparison_preserves_base {context : QuotientCwf.QContext rules}
    (domain : QuotientCwf.Ty levels context)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)) :
    pack (stable levels) domain codomain ≫ QuotientCwf.wk (Sums.sigma levels domain codomain) =
      QuotientCwf.wk codomain ≫ QuotientCwf.wk domain := pack_over (stable levels) domain codomain

theorem context_comparison_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty levels target)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain)) :
    pack (stable levels) (QuotientCwf.tySub domain morphism)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism domain)) ≫
      sumReindex (stable levels) morphism domain codomain =
      tupleReindex (C := QuotientCwf.cwf levels) morphism domain codomain ≫
        pack (stable levels) domain codomain := pack_reindex (stable levels) morphism domain codomain

theorem full_motive_beta {context : QuotientCwf.QContext rules}
    (domain : QuotientCwf.Ty levels context)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain))
    (motive : QuotientCwf.Ty levels (QuotientCwf.ext context (Sums.sigma levels domain codomain)))
    (body : QuotientCwf.Tm levels (QuotientCwf.ext (QuotientCwf.ext context domain) codomain)
      (QuotientCwf.tySub motive (pack (stable levels) domain codomain))) :
    QuotientCwf.tmSub (eliminate (stable levels) domain codomain motive body)
      (pack (stable levels) domain codomain) = body := eliminate_beta (stable levels) domain codomain motive body

theorem full_motive_eta {context : QuotientCwf.QContext rules}
    (domain : QuotientCwf.Ty levels context)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain))
    (motive : QuotientCwf.Ty levels (QuotientCwf.ext context (Sums.sigma levels domain codomain)))
    (term : QuotientCwf.Tm levels (QuotientCwf.ext context (Sums.sigma levels domain codomain)) motive) :
    eliminate (stable levels) domain codomain motive
      (QuotientCwf.tmSub term (pack (stable levels) domain codomain)) = term :=
  eliminate_eta (stable levels) domain codomain motive term

theorem full_motive_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty levels target)
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext target domain))
    (motive : QuotientCwf.Ty levels (QuotientCwf.ext target (Sums.sigma levels domain codomain)))
    (body : QuotientCwf.Tm levels (QuotientCwf.ext (QuotientCwf.ext target domain) codomain)
      (QuotientCwf.tySub motive (pack (stable levels) domain codomain))) :
    QuotientCwf.tmSub (eliminate (stable levels) domain codomain motive body)
      (sumReindex (stable levels) morphism domain codomain) =
      eliminate (stable levels) (QuotientCwf.tySub domain morphism)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf levels) morphism domain))
        (QuotientCwf.tySub motive (sumReindex (stable levels) morphism domain codomain))
        (reindexBody (stable levels) morphism domain codomain motive body) :=
  eliminate_substitution (stable levels) morphism domain codomain motive body

end TypedContextual.SumElimination
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
