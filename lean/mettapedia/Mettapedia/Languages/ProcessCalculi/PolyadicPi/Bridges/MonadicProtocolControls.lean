import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolSimulation

/-!
# Controls for the private-session tuple protocol

The controls distinguish field order, private subject names, duplicated calls,
retained receivers, and cross-arity interference. A direct pair of unordered
outputs on one channel is included as an unsafe comparison. The cross-arity
control refutes primitive-step reflection for arbitrary untyped names, rather
than assuming a source/target channel discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol

def orderedBody {Γ : Ctx sig} : Proc (.nm :: .nm :: Γ) :=
  out1 (.var .zero) (.var (.succ .zero))

theorem ordered_openPair {Γ : Ctx sig} (first second : Name Γ) :
    openPair orderedBody first second = out1 first second := rfl

/-- A tuple consumer really receives its first and second fields in order. -/
theorem ordered_return {Γ : Ctx sig} (channel first second : Name Γ) :
    Nonempty ((operationalTheory Γ).RewritePath
      (invocation channel first second orderedBody) (out1 first second)) :=
  ⟨invocationPath channel first second orderedBody⟩

abbrev threeNames : Ctx sig := [.nm, .nm, .nm]

def channel : Name threeNames := .var .zero
def first : Name threeNames := .var (.succ .zero)
def second : Name threeNames := .var (.succ (.succ .zero))

theorem unequal_fields : first ≠ second := by intro equal; cases equal

/-- Exchanging the fields produces a different actual returned term. -/
theorem field_order_observed :
    out1 first second ≠ out1 second first := by
  intro equal
  cases equal

/-- The selected final private firing cannot return the reversed tuple. -/
theorem final_firing_cannot_reverse :
    ¬ Step (secondState first second orderedBody)
      (nu (nu (weaken (weaken (out1 second first))))) := by
  intro firing
  have exactEndpoint := (secondState_endpoint_iff first second orderedBody _).1 firing
  cases exactEndpoint

/-- The two transport names remain distinct from one another in the actual
intrinsic scope; a second-field output cannot satisfy the callback input. -/
theorem second_field_not_callback {Γ : Ctx sig} (value : Name (.nm :: .nm :: Γ))
    (body : Proc (.nm :: .nm :: .nm :: Γ)) {endpoint : Proc (.nm :: .nm :: Γ)} :
    ¬ Step (par (out1 (.var (.succ .zero)) value) (inp1 (.var .zero) body)) endpoint :=
  mismatched_unary_channel_no_step _ _ _ (by intro equal; cases equal) _

/-- In a common scope the two sessions occupy disjoint private positions.
Neither field subject belonging to the second session matches either private
receiver subject of the first session, regardless of their payload aliases. -/
theorem separated_sessions_do_not_cross {Γ : Ctx sig}
    (sender receiver datum : Name (.nm :: .nm :: .nm :: .nm :: Γ))
    (senderPosition : sender = .var .zero ∨ sender = .var (.succ .zero))
    (receiverPosition : receiver = .var (.succ (.succ .zero)) ∨
      receiver = .var (.succ (.succ (.succ .zero))))
    (body : Proc (.nm :: .nm :: .nm :: .nm :: .nm :: Γ))
    {endpoint : Proc (.nm :: .nm :: .nm :: .nm :: Γ)} :
    ¬ Step (par (out1 sender datum) (inp1 receiver body)) endpoint := by
  rcases senderPosition with rfl | rfl <;>
    rcases receiverPosition with rfl | rfl <;>
    exact mismatched_unary_channel_no_step _ _ _ (by intro equal; cases equal) _

/-- Private session and callback variables are absent from the supplied
ambient returned continuation, even if ambient payloads alias each other. -/
theorem returned_continuation_does_not_capture {Γ : Ctx sig}
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    countVar (Var.zero : Var (.nm :: .nm :: Γ) .nm)
      (weaken (weaken (openPair body first second))) = 0 :=
  countVar_zero_of_weaken _

theorem returned_continuation_does_not_capture_session {Γ : Ctx sig}
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    countVar (Var.succ Var.zero : Var (.nm :: .nm :: Γ) .nm)
      (weaken (weaken (openPair body first second))) = 0 := by
  unfold weaken
  rw [rename_comp]
  apply countVar_rename_of_miss
  intro sort name
  rfl

/-- The selected common receiver receives two separately ordered tuples. -/
theorem two_requests_same_channel :
    Nonempty ((operationalTheory threeNames).RewritePath
      (par (par (sendPair channel first second) (rep (receivePair channel orderedBody)))
        (sendPair channel second first))
      (par (out1 first second) (par (out1 second first) (rep (receivePair channel orderedBody))))) :=
  ⟨twoSendersPath channel first second second first orderedBody⟩

theorem two_requests_count :
    (twoSendersPath channel first second second first orderedBody).length = 8 := rfl

/-- Reversing which sender is chosen first still returns both actual tuples. -/
theorem reversed_requests_same_channel :
    Nonempty ((operationalTheory threeNames).RewritePath
      (par (par (sendPair channel second first) (rep (receivePair channel orderedBody)))
        (sendPair channel first second))
      (par (out1 second first) (par (out1 first second) (rep (receivePair channel orderedBody))))) :=
  ⟨twoSendersPath channel second first first second orderedBody⟩

/-- Equal sender terms are two occurrences, and produce two return occurrences. -/
theorem duplicated_requests_retained :
    Nonempty ((operationalTheory threeNames).RewritePath
      (par (par (sendPair channel first second) (rep (receivePair channel orderedBody)))
        (sendPair channel first second))
      (par (out1 first second) (par (out1 first second) (rep (receivePair channel orderedBody))))) :=
  ⟨duplicateSendersPath channel first second orderedBody⟩

theorem duplicated_requests_count :
    (duplicateSendersPath channel first second orderedBody).length = 8 := rfl

/-- Both requests enter before either is completed; actual private callback
and payload firings interleave without combining different sender tuples. -/
theorem interleaved_requests_same_channel :
    Nonempty ((operationalTheory threeNames).RewritePath
      (par (par (sendPair channel first second) (rep (receivePair channel orderedBody)))
        (sendPair channel second first))
      (par (out1 first second) (par (out1 second first) (rep (receivePair channel orderedBody))))) :=
  ⟨interleavedSendersPath channel first second second first orderedBody⟩

theorem interleaved_requests_count :
    (interleavedSendersPath channel first second second first orderedBody).length = 8 := rfl

def unsafeTwoFields {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  par (par (out1 channel first) (out1 channel second))
    (inp1 channel (inp1 (weaken channel) (rename swapRen body)))

/-- Publishing both fields on one private channel without an ordering
handshake permits the second field to be selected first. -/
theorem unsafe_second_can_arrive_first {Γ : Ctx sig} (channel first second : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    StepModulo (unsafeTwoFields channel first second body)
      (par (out1 channel first)
        (inst (inp1 (weaken channel) (rename swapRen body)) second)) := by
  refine ⟨_, _, ?_, .parR _ (.comm1 channel second _), .refl _⟩
  exact .parAssoc _ _ _

/-- The unordered implementation really can return the reversed pair. -/
def unsafeReversedPath :
    (operationalTheory threeNames).RewritePath
      (unsafeTwoFields channel first second orderedBody) (out1 second first) :=
  .cons (unsafe_second_can_arrive_first channel first second orderedBody)
    (.cons ⟨_, _, .refl _, .comm1 channel first _, .refl _⟩ (.nil _))

theorem unsafeReversedPath_length : unsafeReversedPath.length = 2 := rfl

/-- The source distinguishes unary from binary receivers. -/
theorem source_cross_arity_inert {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) {endpoint : Proc Γ} :
    ¬ Step (par (out1 channel datum) (inp2 channel body)) endpoint :=
  mismatched_arity_no_step _ _ _

/-- The unconstrained lowered binary receiver initially has a unary public
input, so it can accept an unrelated source unary output. -/
theorem lowered_cross_arity_fires {Γ : Ctx sig} (channel datum : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    Step (lower (par (out1 channel datum) (inp2 channel body)))
      (inst (nu (par (out1 (.var (.succ .zero)) (.var .zero))
        (receiveFields (lower body)))) datum) := by
  rw [lower_par, lower_out1, lower_inp2]
  exact .comm1 _ _ _

/-- Primitive-step reflection fails for this candidate on the entire untyped
source; a useful backward theorem must exclude cross-arity interference. -/
theorem no_untyped_primitive_reflection :
    ¬ (∀ (source endpoint : Proc threeNames), Step (lower source) endpoint →
      ∃ sourceEndpoint, Step source sourceEndpoint) := by
  intro reflection
  obtain ⟨endpoint, firing⟩ := reflection
    (par (out1 channel first) (inp2 channel orderedBody)) _
    (lowered_cross_arity_fires channel first orderedBody)
  exact source_cross_arity_inert channel first orderedBody firing

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Controls
