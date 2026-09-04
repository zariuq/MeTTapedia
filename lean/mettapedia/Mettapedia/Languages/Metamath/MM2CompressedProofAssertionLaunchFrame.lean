import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous

/-!
# Canonical generated frame for a compressed assertion launch

The local matcher is lifted monotonically into the complete source-derived
launch space.  The construction retains the real cursor handlers and the
already exhausted speculative proof probe, so scheduling is proved against
the assembled target inventory rather than a singleton phase.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

/-- Exact source-independent data flow of the canonical generated assertion
launcher.  Source authorization is added by the continuous boundary theorem;
this proposition concerns the MM2 surface alone. -/
def ExactDirectAssertionLaunch (context : DirectAssertionContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst,
    instantiateTemplateAtom? substitution directAssertionPendingTemplate =
        some context.pendingRow ∧
      instantiateTemplateAtom? substitution directAssertionLookupTemplate =
        some context.lookupRow ∧
      instantiateTemplateAtom? substitution directAssertionMachineTemplate =
        some context.machineRow ∧
      instantiateTemplateAtom? substitution directAssertionContextTemplate =
        some context.assertionContextRow ∧
      instantiateTemplateAtom? substitution directAssertionNormalControlTemplate =
        some context.normalControlRow ∧
      instantiateTemplateAtom? substitution directAssertionNormalLabelTemplate =
        some context.normalLabelRow ∧
      instantiateTemplateAtom? substitution directAssertionReloadTemplate =
        some context.reloadRow ∧
      instantiateTemplateAtom? substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule

def directAssertionSchedulerFrame : List Atom :=
  [compressedProofStepDirective.atom,
   compressedAssertionLaunchDirective.atom,
   compressedHeapLookupFaultDirective.atom,
   compressedHeapLookupAdvanceDirective.atom]

def canonicalDirectAssertionSpace
    (context : DirectAssertionContext) : List Atom :=
  directAssertionMatchSlice context ++ directAssertionSchedulerFrame

def directAssertionLive (space : List Atom) : List Atom :=
  space.erase speculativeDirectAssertionDirective.atom

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
