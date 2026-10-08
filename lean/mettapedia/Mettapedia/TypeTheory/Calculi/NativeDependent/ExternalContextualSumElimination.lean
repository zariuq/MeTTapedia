import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualSums
import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Full-motive elimination in the generated external contextual quotient

The source's actual pair rules satisfy the shared stable-sum capability.
Its context comparison and motive elimination therefore apply to arbitrary
typed quotient families, including families over the complete pair context.
The context-substitution square compares the independently selected sum and
tuple lifts, and elimination recovers the complete supplied body class.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SumElimination

open _root_.CategoryTheory

universe u
open Mettapedia.TypeTheory.ContextualSumComprehension

variable {S : Symbols.{u}} {D : Signature S}

noncomputable def stable (D : Signature S) : StableSums (QuotientCwf.cwf D) where
  operations := Sums.operations D
  beta := Sums.beta
  eta := Sums.eta
  substitution := Sums.substitution

theorem context_comparison_preserves_base {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)) :
    pack (stable D) domain codomain ≫ QuotientCwf.wk (Sums.sigma domain codomain) =
      QuotientCwf.wk codomain ≫ QuotientCwf.wk domain := pack_over (stable D) domain codomain

theorem context_comparison_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain)) :
    pack (stable D) (QuotientCwf.tySub domain morphism)
      (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism domain)) ≫
      sumReindex (stable D) morphism domain codomain =
      tupleReindex (C := QuotientCwf.cwf D) morphism domain codomain ≫
        pack (stable D) domain codomain := pack_reindex (stable D) morphism domain codomain

theorem full_motive_beta {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : QuotientCwf.Ty (QuotientCwf.ext context (Sums.sigma domain codomain)))
    (body : QuotientCwf.Tm (QuotientCwf.ext (QuotientCwf.ext context domain) codomain)
      (QuotientCwf.tySub motive (pack (stable D) domain codomain))) :
    QuotientCwf.tmSub (eliminate (stable D) domain codomain motive body)
      (pack (stable D) domain codomain) = body := eliminate_beta (stable D) domain codomain motive body

theorem full_motive_eta {context : QuotientCwf.QContext D}
    (domain : QuotientCwf.Ty context)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (motive : QuotientCwf.Ty (QuotientCwf.ext context (Sums.sigma domain codomain)))
    (term : QuotientCwf.Tm (QuotientCwf.ext context (Sums.sigma domain codomain)) motive) :
    eliminate (stable D) domain codomain motive
      (QuotientCwf.tmSub term (pack (stable D) domain codomain)) = term :=
  eliminate_eta (stable D) domain codomain motive term

theorem full_motive_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (domain : QuotientCwf.Ty target)
    (codomain : QuotientCwf.Ty (QuotientCwf.ext target domain))
    (motive : QuotientCwf.Ty (QuotientCwf.ext target (Sums.sigma domain codomain)))
    (body : QuotientCwf.Tm (QuotientCwf.ext (QuotientCwf.ext target domain) codomain)
      (QuotientCwf.tySub motive (pack (stable D) domain codomain))) :
    QuotientCwf.tmSub (eliminate (stable D) domain codomain motive body)
      (sumReindex (stable D) morphism domain codomain) =
      eliminate (stable D) (QuotientCwf.tySub domain morphism)
        (QuotientCwf.tySub codomain (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
          (C := QuotientCwf.cwf D) morphism domain))
        (QuotientCwf.tySub motive (sumReindex (stable D) morphism domain codomain))
        (reindexBody (stable D) morphism domain codomain motive body) :=
  eliminate_substitution (stable D) morphism domain codomain motive body

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SumElimination
