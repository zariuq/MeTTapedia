import Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation.Fundamental

/-! Pi injectivity for the independent finite-Set/Pi source calculus, derived
from its proved fundamental lemma. Both components are actual source
derivations; the codomains are compared under the original left domain. -/

namespace Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
open Mettapedia.Languages.Agda.StaticSpecification
open Mettapedia.Languages.Agda.SourceMetatheory.WeakHead
open Mettapedia.Languages.Agda.SourceMetatheory.Kripke

def sourcePiInjectivity {Γ : RawContext n} {A A' : Ty n} {B B' : TyAbs n}
    (equal : TypeEq Γ (Ty.pi A B) (Ty.pi A' B')) :
    TypeEq Γ A A' × TypeEq (Γ.snoc A) B.open B'.open := by
  have semantic := equalTypesRelated equal
  have components := semantic.1.piComponentEvidenceAt semantic.2 (World.identity equal.context)
  simpa only [Ty.rename_id, TyAbs.rename_id] using components

end Mettapedia.Languages.Agda.SourceMetatheory.LogicalRelation
