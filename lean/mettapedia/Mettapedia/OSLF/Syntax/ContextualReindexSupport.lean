import Mettapedia.OSLF.Syntax.ContextualFamilyReindex
import Mettapedia.OSLF.Syntax.ContextualFamilySupport

/-!
# Support and image sizes under declaration-interface transport

Transporting the parameter context and result sort changes neither the
mentioned holes nor the number of nodes. A reindexing image mentions exactly
its destination identity. These laws require no finite declaration carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {V W X : Type}
  {source : V → MetaArity S} {target : W → MetaArity S} {next : X → MetaArity S}

theorem support_castMetaBody {first second : MetaArity S} (same : first = second)
    (body : Term (signature S source) first.1 first.2) :
    support (castMetaBody (V := signature S source) same body) = support body := by
  cases same
  rfl

theorem termSize_castMetaBody {T : Signature} {first second : MetaArity T} (same : first = second)
    (body : Term T first.1 first.2) : termSize (castMetaBody same body) = termSize body := by
  cases same
  rfl

theorem support_reindex (identities : V → W)
    (preserves : ∀ identity, target (identities identity) = source identity) (identity : V) :
    support (reindex identities preserves identity) = [identities identity] := by
  rw [reindex, support_castMetaBody, support_generator]

theorem termSize_instantiate_reindex (identities : V → W)
    (preserves : ∀ identity, target (identities identity) = source identity)
    (candidate : Assignment target next) (identity : V) :
    termSize (instantiate candidate (reindex identities preserves identity)) =
      termSize (candidate (identities identity)) := by
  rw [instantiate_reindex, termSize_castMetaBody]

end Mettapedia.OSLF.Binding.ContextualFamily
