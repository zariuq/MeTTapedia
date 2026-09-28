import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedYoneda
import Mettapedia.OSLF.Syntax.FiniteLimitGeneratedContextEmbedding
import Mettapedia.OSLF.Syntax.RhoEquationContextRepresentability

/-!
# Raw and authored-equation contexts in the same finite-limit construction

The generic Yoneda closure applies to the actual equation-quotient context
category of the reflective presentation. The previously proved representation
of equation-class name states then lands in a represented object of this
finitely complete category, without identifying that object with a raw-context
representable.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoEquationContextRepresentability

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.FiniteLimitYoneda

private noncomputable abbrev sourceClone :=
  (BindingEquationQuotientModel.algebra rhoSourceE).substitution.toClone

private noncomputable abbrev sourceContexts := ContextObject sourceClone

private noncomputable def nameContext : sourceContexts :=
  ContextObject.ofList sourceClone [Srt.nm]

/-- The name-state object of the complete authored rho equation quotient is
one of the representables generating its finite-limit category. -/
theorem sourceName_in_generated :
    Generated sourceContexts (yoneda.obj nameContext) :=
  represented sourceContexts nameContext

/-- The already-proved equation-class state presheaf is the pullback of that
specific generated representable, along the actual raw-to-quotient context
functor. Its substitution action is the one established previously. -/
noncomputable def sourceNameState_as_generated :
    (cloneContextToSyntactic sig).op ⋙ termQPresheaf rhoSourceE Srt.nm ≅
      (termCloneToSemanticContextFunctor sig ⋙ quotientContextFunctor rhoSourceE).op ⋙
        (Generated sourceContexts).ι.obj
          ((intoGenerated sourceContexts).obj nameContext) := by
  exact sourceNameYonedaIso

end Mettapedia.OSLF.Binding.RhoEquationContextRepresentability
