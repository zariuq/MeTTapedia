import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementInterpretationControls

/-!
# Generated refinement elimination through a varying mixed tail

The supplied source derivation transports an actual finite fibre, a native
predicate-function variable and a truth assumption. Its interpreted arrow
lands in the guarded original context. The protected tail components are
retained exactly, while the older scalar is obtained by forgetting the
refined generic value. No whole-tail semantic action is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.MixedTailControls

open _root_.CategoryTheory
open InterpretationControls
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

noncomputable section

theorem stable : StrictPiSubstitution model.products :=
  NativeLocalTypeOperations.products_substitution World

theorem beta : PiBeta model.products := NativeLocalTypeOperations.products_beta World

theorem eta : PiEta model.products stable.1 := NativeLocalPiEta.products_eta World

def baseProjection : ComprehensionProjectionData Controls.signature .nil
    (Controls.scalar 0) (Controls.positive 0) :=
  comprehensionProjectionData Controls.emptyContext (Controls.scalarFormed Controls.emptyContext)
    Controls.positiveVariable

def transportedTail : SuffixTransport Controls.signature
    (.snoc .nil (.comprehension (Controls.scalar 0) (Controls.positive 0)))
    (.snoc .nil (Controls.scalar 0))
    (comprehensionProjection (Controls.scalar 0) (Controls.positive 0)) Controls.mixedSuffix :=
  Controls.mixedSuffixFormed.transport baseProjection.formed baseProjection.arrow

def fullContext : ContextExpr Controls.symbols 3 :=
  (Controls.mixedSuffix.substitute (comprehensionProjection (Controls.scalar 0) (Controls.positive 0))).plug
    (.snoc .nil (.comprehension (Controls.scalar 0) (Controls.positive 0)))

def fullContextTree : Derivation Controls.signature (.context fullContext) :=
  transportedTail.formed.context

def assumedOriginalContext : ContextExpr Controls.symbols 3 :=
  .assume (Controls.mixedSuffix.plug (.snoc .nil (Controls.scalar 0))) Controls.finalGuard

def targetContextTree : Derivation Controls.signature (.context assumedOriginalContext) :=
  deriveList (.contextAssume _ Controls.finalGuard)
    (.cons Controls.mixedSuffixFormed.context (.cons Controls.finalGuardFormed .nil))

def fullSubstitution : Substitution Controls.symbols 3 3 :=
  liftSubstitutionN (comprehensionProjection (Controls.scalar 0) (Controls.positive 0)) 2

def fullArrowTree : Derivation Controls.signature
    (.substitution fullContext assumedOriginalContext fullSubstitution) :=
  comprehensionAssumptionSubstitution Controls.emptyContext (Controls.scalarFormed Controls.emptyContext)
    Controls.positiveVariable Controls.mixedSuffixFormed

def sourceScope : Scope World 3 := fullContextTree.contextValue model realization stable beta eta
def targetScope : Scope World 3 := targetContextTree.contextValue model realization stable beta eta

theorem source_read : model.evaluateContext fullContext = some sourceScope :=
  fullContextTree.contextValue_readout model realization stable beta eta

theorem target_read : model.evaluateContext assumedOriginalContext = some targetScope :=
  targetContextTree.contextValue_readout model realization stable beta eta

def fullArrow : sourceScope.1 ⟶ targetScope.1 :=
  fullArrowTree.substitutionArrow model realization stable beta eta sourceScope targetScope source_read target_read

theorem full_arrow_read : model.evaluateSubstitution sourceScope targetScope fullSubstitution = some fullArrow :=
  fullArrowTree.substitutionArrow_readout model realization stable beta eta
    sourceScope targetScope source_read target_read

theorem protected_function_retained : targetScope.2.components fullArrow 0 = sourceScope.2.lookup 0 := by
  have component := (model.evaluateSubstitution_eq_some_iff sourceScope targetScope fullSubstitution fullArrow).mp
    full_arrow_read 0
  change some (sourceScope.2.lookup 0) = some (targetScope.2.components fullArrow 0) at component
  exact (Option.some.inj component).symm

theorem protected_finite_witness_retained : targetScope.2.components fullArrow 1 = sourceScope.2.lookup 1 := by
  have component := (model.evaluateSubstitution_eq_some_iff sourceScope targetScope fullSubstitution fullArrow).mp
    full_arrow_read 1
  change some (sourceScope.2.lookup 1) = some (targetScope.2.components fullArrow 1) at component
  exact (Option.some.inj component).symm

theorem forgotten_scalar_read : model.evaluateTerm sourceScope (fullSubstitution 2) =
    some (targetScope.2.components fullArrow 2) :=
  (model.evaluateSubstitution_eq_some_iff sourceScope targetScope fullSubstitution fullArrow).mp
    full_arrow_read 2

theorem complete_tail_guard : model.evaluatePredicate sourceScope
    (Controls.finalGuard.substitute fullSubstitution) = some ⊤ :=
  (Controls.fullSuffixGuard.native_sound model realization).entailsAt sourceScope source_read

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.MixedTailControls
