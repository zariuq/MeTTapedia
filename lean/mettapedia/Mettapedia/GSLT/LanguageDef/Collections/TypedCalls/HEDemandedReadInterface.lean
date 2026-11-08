import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorEdge
import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission

/-!
# Reached typing reads of the demanded constructor program

The source derivation uses five families of typing observations. Each
constructor-arrow read earns a fresh private name at its actual occurrence.
This interface contains no source-evaluation or whole-call-success premise.
Its instances must obtain these replies from the chosen typing service.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedReadInterface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed
open HEDemandedConstructorEdge (space producer consumerSignature)
open HERepeatedFormalSource (signature)

structure Reads where
  lookup : CastLookup
  pair : ∀ scope (before : Frame) expected, ∃ name,
    lookup scope space before.bindings (.symbol "OtherDemandPair") expected [(signature name).functionType] ∧
    name ∉ invocationTypeScope scope [] (.symbol "OtherDemandPair") expected before.bindings
  number : ∀ scope (before : Frame) (value : Int) expected,
    lookup scope space before.bindings (.grounded (.int value)) expected [.symbol "Number"]
  producer : ∀ scope (before : Frame) expected,
    lookup scope space before.bindings HEDemandedConstructorEdge.producer expected [HEDemandedConstructorEdge.demand]
  consumerHead : ∀ scope (before : Frame) expected,
    lookup scope space before.bindings (.symbol "use-demand") expected [consumerSignature.functionType]
  producerHead : ∀ scope (before : Frame) expected,
    lookup scope space before.bindings (.symbol "other-demand-result") expected
      [CompletedDelivery.arrowType [] HEDemandedConstructorEdge.demand]

def environment (reads : Reads) (minimal : Minimal.Services) : WorldEnvironment Space Unit :=
  { WorldEnvironment.readOnly minimal Completed.Controls.typedDispatch reads.lookup with
    arguments := kindArgumentService }

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedReadInterface
