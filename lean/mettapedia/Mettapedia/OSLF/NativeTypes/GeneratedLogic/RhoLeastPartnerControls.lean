import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoLeastPartners
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls

/-!
# Controls: ρ's least partners and their schemas

On the forwarder `for(y<-@0){*y}` and the outputs `@0!(@0!(0))` and `@0!(0)`:

- the forwarder's payload schema has both outputs as instances, two distinct least partners of one schema
  (`forwarder_payload_instances`);
- the output `@0!(@0!(0))` has the forwarder as an instance of its body schema (`sender_body_instance`);
- a bag holding a whole redex steps under the empty label (`redex_plain_step`);
- the inert process has no least label of one prime: only whole redexes enable it (`inert_no_single_partner`);
- the waiting receiver and the inert process are not semi-saturated bisimilar on least labels, the least-label form of
  the canary that separates them under partners (`waiting_not_semiSaturated_inert`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.LeastPartners.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalBag (IsPrime fromProcess)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical (IsCanonical IsCanonicalList)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReaction (GroundComm input output)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalReactionControls (zero channel body payload input_prime
  output_prime)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem (closedNil)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy (waitingInput
  waitingInput_not_partner_bisimilar_nil)
open Mettapedia.GSLT.RedexRelativeCongruence (ActIPO)
open Mettapedia.GSLT.BagRelativePushout (bag)
open Mettapedia.GSLT.SemiSaturated (SemiSaturatedBisimilar)

theorem plain_output_prime : IsPrime (output channel zero) := by
  refine ⟨(Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefRewriteSystem.rhoClosedTermWellSorted_process_iff _).mpr
    ⟨.output (.quote .unit) .unit, rfl⟩, ?_, ?_, ?_⟩
  · simp [output, channel, zero, IsCanonical, IsCanonicalList]
  · simp [output]
  · intro elements
    simp [output]

/-- The forwarder `for(y<-@0){*y}`. -/
def forwarder : Prime := ⟨input channel body, input_prime⟩

/-- The output `@0!(@0!(0))`. -/
def sender : Prime := ⟨output channel payload, output_prime⟩

/-- The output `@0!(0)`. -/
def plainSender : Prime := ⟨output channel zero, plain_output_prime⟩

theorem forwarder_ne_sender : forwarder ≠ sender := fun same => by
  have := congrArg Subtype.val same
  simp [forwarder, sender, input, output] at this

theorem forwarder_ne_plainSender : forwarder ≠ plainSender := fun same => by
  have := congrArg Subtype.val same
  simp [forwarder, plainSender, input, output] at this

theorem sender_ne_plainSender : sender ≠ plainSender := fun same => by
  have := congrArg Subtype.val same
  simp [sender, plainSender, output, payload, zero, channel] at this

/-- **One schema, two least partners**: both outputs on `@0` are least partners of the forwarder, instances of the
payload schema of its input. -/
theorem forwarder_payload_instances :
    (∃ target, ActIPO rules (bag {sender}) (bag {forwarder}) (bag target)) ∧
      (∃ target, ActIPO rules (bag {plainSender}) (bag {forwarder}) (bag target)) ∧ sender ≠ plainSender :=
  ⟨⟨_, payloadSchema input_prime output_prime (Multiset.mem_singleton_self _)
      (fun member => forwarder_ne_sender (Multiset.mem_singleton.mp member).symm)⟩,
    ⟨_, payloadSchema input_prime plain_output_prime (Multiset.mem_singleton_self _)
      (fun member => forwarder_ne_plainSender (Multiset.mem_singleton.mp member).symm)⟩,
    sender_ne_plainSender⟩

/-- **The body schema**: the forwarder is a least partner of the output `@0!(@0!(0))`. -/
theorem sender_body_instance : ∃ target, ActIPO rules (bag {forwarder}) (bag {sender}) (bag target) :=
  ⟨_, bodySchema input_prime output_prime (Multiset.mem_singleton_self _)
    (fun member => forwarder_ne_sender (Multiset.mem_singleton.mp member))⟩

/-- **A whole redex steps under the empty label.** -/
theorem redex_plain_step : ∃ target, ActIPO rules (bag 0) (bag {forwarder, sender}) (bag target) :=
  ⟨_, actIPO_iff_cases.mpr ⟨⟨channel, channel, body, payload, input_prime, output_prime, rfl⟩, rfl,
    Or.inl ⟨Multiset.mem_cons_self _ _, Multiset.mem_cons_of_mem (Multiset.mem_singleton_self _), rfl⟩⟩⟩

/-- **The inert process has no least partner of one prime**: only a whole redex enables it. -/
theorem inert_no_single_partner (token : Prime) (target : Multiset Prime) :
    ¬ ActIPO rules (bag {token}) (bag 0) (bag target) := fun step => by
  obtain ⟨comm, -, cases⟩ := actIPO_iff_cases.mp step
  simp only [Multiset.notMem_zero, false_and, and_false, false_or] at cases
  have sizes := congrArg Multiset.card cases.2.2
  simp at sizes

/-- **The waiting receiver and the inert process are not semi-saturated bisimilar on least labels.** -/
theorem waiting_not_semiSaturated_inert :
    ¬ SemiSaturatedBisimilar rules (bag (primes (fromProcess waitingInput))) (bag (primes (fromProcess closedNil))) :=
  fun bisimilar => waitingInput_not_partner_bisimilar_nil ((semiSaturated_iff_partnerBisimilar _ _).mp bisimilar)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.LeastPartners.Controls
