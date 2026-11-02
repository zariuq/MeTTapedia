import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionReading
import Mettapedia.Logic.HOL.FiniteConstructorPayloadBoundary

/-!
# Full-model constructor boundary for the original mixed-vector reading

The current reading uses `E` for both payload elements and recursive values.
Its raw payload type has fields `[N, E, N]`. Consequently the unrestricted
constructor-injectivity statement has no full-function-space interpretation
at that same result carrier. The conditional child-array theorems do not
assume this statement and are unaffected.

Separate data/result carriers and guarded no-confusion over represented
payloads require their own interpretations. Neither is selected here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorBoundary
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading FiniteConstructorEncoding
universe w

theorem original_reading_refuses_full_injectivity {Γ : Ctx Base}
    (model : HenkinModel.{0,0,w} Base Const) (full : model.FullDomains)
    (payload : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType (constructors payload).fields ⇒ (N ⇒ E) ⇒ E))
    (bottom : Term Const Γ E) (values : model.Valuation Γ) :
    ¬ (model.denote (ConstructorInjectivity.statement construct) values).down :=
  FiniteConstructorPayloadBoundary.full_injectivity_statement_refused N E model full
    (model.denote (weakenCtx Γ original.zero) values) (model.denote bottom values) construct values

#print axioms original_reading_refuses_full_injectivity
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorBoundary
