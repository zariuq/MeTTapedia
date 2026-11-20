import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FrontierNative
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchOutcome

/-!
# Building native expansions from finite proof-producing probes

A probe returns an actual admitted invocation, a refutation of that name's
eligibility, or a retained pending reason. The pending payload may carry a
residual problem, a budget checkpoint or another caller-defined continuation.
Only a settled probe at every supported name licenses a completed expansion.

The builder is a finite computation over the immutable name set. It invokes
no source semantics and does not turn incomplete probing into an empty result.
The probe provider must establish its actual admission/refutation evidence;
this module does not assume a general decision procedure for symbolic guards.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open SourceLanguage Hosting Hosting.Alternatives

universe uPending

variable {S : Signature} {Γ : Ctx S} {star : S.Srt}
  {κ : Keys S} {D : Discipline S Γ star}
  {N : Nodes S Γ star} {P : SourceLanguage.Program κ Γ star D.Ty}
  {Pending : Type uPending} {before : Leaf S} {name : RuleName}

abbrev ProbeResult (Pending : Type uPending) (N : Nodes S Γ star)
    (P : SourceLanguage.Program κ Γ star D.Ty) (before : Leaf S) (name : RuleName) :=
  Except Pending (Sum (Invocation N P before name) (PLift (¬ Enabled N P before name)))

abbrev ProbeResult.accepted (reply : ProbeResult Pending N P before name) : Bool :=
  FrontierNativeCore.ProbeResult.accepted reply

abbrev ProbeResult.settled (reply : ProbeResult Pending N P before name) : Bool :=
  FrontierNativeCore.ProbeResult.settled reply

abbrev ProbeResult.verdict (reply : ProbeResult Pending N P before name) : Search.Outcome.Verdict :=
  FrontierNativeCore.ProbeResult.verdict reply

abbrev ProbeResult.invocation (reply : ProbeResult Pending N P before name)
    (accepted : reply.accepted = true) : Invocation N P before name :=
  FrontierNativeCore.ProbeResult.invocation reply accepted

theorem ProbeResult.accepted_sound (reply : ProbeResult Pending N P before name)
    (accepted : reply.accepted = true) : Enabled N P before name :=
  ⟨reply.invocation accepted⟩

theorem ProbeResult.enabled_accepted (reply : ProbeResult Pending N P before name)
    (ready : reply.settled = true) (enabled : Enabled N P before name) : reply.accepted = true := by
  cases reply with
  | error reason => cases ready
  | ok result =>
      cases result with
      | inl invocation => rfl
      | inr refuted => exact False.elim (refuted.down enabled)

theorem ProbeResult.refuted_sound (reply : ProbeResult Pending N P before name)
    (refused : reply.verdict = .refuted) : ¬ Enabled N P before name := by
  cases reply with
  | error reason => cases refused
  | ok result =>
      cases result with
      | inl invocation => cases refused
      | inr refuted => exact refuted.down

variable (N P)

def Ready (probe : (name : RuleName) → ProbeResult Pending N P before name) : Prop :=
  ∀ name ∈ FrontierNames.names P, (probe name).settled = true

def acceptedNames (probe : (name : RuleName) → ProbeResult Pending N P before name) : Finset RuleName :=
  (FrontierNames.names P).filter fun name => (probe name).accepted = true

/-- A finite builder from actual supplied decisions. Positive entries carry their native data;
negative entries carry refutations. The ready condition rejects every pending entry. -/
def fromProbes (probe : (name : RuleName) → ProbeResult Pending N P before name)
    (ready : Ready N P probe) : Expansion N P before :=
  FrontierNativeCore.fromProbes (catalogue N P) probe ready

theorem fromProbes_names (probe : (name : RuleName) → ProbeResult Pending N P before name)
    (ready : Ready N P probe) : (fromProbes N P probe ready).names = acceptedNames N P probe := rfl

/-- A pending supported query prevents this probe family from certifying coverage.
It says nothing about whether another procedure could complete the expansion. -/
theorem pending_not_ready (probe : (name : RuleName) → ProbeResult Pending N P before name)
    {name : RuleName} {reason : Pending} (supported : name ∈ FrontierNames.names P)
    (pending : probe name = .error reason) : ¬ Ready N P probe := by
  intro ready
  have settled := ready name supported
  rw [pending] at settled
  cases settled

theorem pending_status (reason : Pending) :
    (ProbeResult.verdict (.error reason : ProbeResult Pending N P before name)) = .suspended := rfl

theorem pending_is_not_refuted (reason : Pending) :
    (ProbeResult.verdict (.error reason : ProbeResult Pending N P before name)) ≠ .refuted := by
  intro impossible
  cases impossible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.fromProbes
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.ProbeResult.refuted_sound
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.FrontierNative.pending_not_ready
