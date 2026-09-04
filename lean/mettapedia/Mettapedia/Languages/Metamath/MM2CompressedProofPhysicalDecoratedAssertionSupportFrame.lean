import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch

/-!
# Physical decorated-assertion support frame

This module transports atom-local workspace invariants across the actual
decorated-assertion transaction.  It is kept separate from the larger launch
development so downstream invariant instances elaborate against a compact
interface.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionSupportFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
open Mettapedia.Languages.ProcessCalculi.MORK

/-- An atom-local invariant of the live workspace survives the complete
physical assertion launch whenever it contains both compiler-captured
continuation classes. -/
theorem physical_decorated_assertion_fire_atomsWithin_of_generated
    {space : List Atom} {property : Atom → Prop}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (liveWithin : AtomsWithin property
      (morkEraseSupport space decoratedDirectAssertionDirective.atom))
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    (generatedWithin : ∀ atom,
      DecoratedAssertionGeneratedSupportedAtom atom → property atom) :
    AtomsWithin property
      (cFireRuleScopedSourceExecFact space
        decoratedDirectAssertionDirective) := by
  apply cFireRuleScopedSourceExecFact_atomsWithin_of_live_additions
    property space decoratedDirectAssertionDirective liveWithin
  exact @RuleScopedTemplateAdditionsWithin.mono
    DecoratedAssertionGeneratedSupportedAtom property
    decoratedDirectAssertionDirective.rule.input
    (physicalDecoratedAssertionMatcherRows space)
    decoratedDirectAssertionDirective.rule.tmpl generatedWithin
    (physical_decorated_assertion_additions_supported_origin listNodup
      morkNodup directivePresent rejoinCapabilities bridgeCapabilities)

#print axioms physical_decorated_assertion_fire_atomsWithin_of_generated

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionSupportFrame
