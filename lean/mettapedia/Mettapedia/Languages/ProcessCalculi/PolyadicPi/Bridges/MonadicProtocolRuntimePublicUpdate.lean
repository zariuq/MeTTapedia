import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicationArrangement
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimePublicReceipt

/-!
# A supplied public firing commits its original occurrence

The actual selected idle decoder determines the original source continuation.
Its frame and the sender's own waiter are retained. Callback allocation remains
the receiver's real restriction; the old unused callback position is reused
only after closing the original private telescope. The resulting endpoint is
the actual pending registry with its exact remaining occurrence list.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicUpdate

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open Capabilities Ownership RuntimeState RuntimeActors ScopedActiveFrontier
open ActiveMarking ActiveOriginErasure ActiveGuardedBodies ActiveHeaderInvariant
open ActiveUnarySelectedBoundary RuntimePublicationArrangement RuntimePublicReceipt

def binaryReceiver {Γ : Ctx sig} (persistent : Bool) (channel : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) : Proc Γ :=
  if persistent then rep (inp2 channel body) else inp2 channel body

def updatedFrame {Γ : Ctx sig} (persistent : Bool) (frame : List (Proc Γ))
    (input : Fin frame.length) : List (Proc Γ) :=
  if persistent then frame[input.val] :: otherFrame frame input else otherFrame frame input

def commit {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n) (call : Call Γ) :
    Fin n → Slot Γ := Function.update registry owner (.pending .callback call)

theorem lower_binary_receiver {Γ : Ctx sig} (persistent : Bool) (channel : Name Γ)
    (body : Proc (.nm :: .nm :: Γ)) :
    lower (binaryReceiver persistent channel body) = receiver persistent channel (PublicRoles.decoderBody body) := by
  cases persistent <;> simp only [binaryReceiver, receiver, Bool.false_eq_true, if_false, if_true,
    lower_rep, lower_inp2, receivePair, PublicRoles.decoderBody]

theorem updated_heads {Γ : Ctx sig} (persistent : Bool) (frame : List (Proc Γ))
    (input : Fin frame.length) (heads : ∀ atom ∈ frame, IdleFrame.Head atom) :
    ∀ atom ∈ updatedFrame persistent frame input, IdleFrame.Head atom := by
  cases persistent with
  | false => exact other_heads frame input heads
  | true =>
      intro atom member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ heads _ (List.getElem_mem input.isLt)
      · exact other_heads frame input heads atom member

theorem selected_reordering {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second)
    (frame : List (Proc Γ)) (input : Fin frame.length) (persistent : Bool)
    (body : Proc (.nm :: .nm :: Γ))
    (original : frame[input.val] = binaryReceiver persistent channel body) :
    Transport
      (.par (.out1 (.publication owner))
        (.par (receiverMarks persistent (.idle input.val)
          (ActiveSyntaxMarking.mark (.idle input.val) (PublicRoles.decoderBody body)))
          (restMarks registry owner first second frame input)))
      (par (out1 (rename (ambient n) channel) (keyName n owner .session))
        (par (receiver persistent (rename (ambient n) channel)
          (rename (liftRen (ambient n) [.nm]) (PublicRoles.decoderBody body)))
          (rest registry owner first second frame input)))
      (assemblyMarks registry frame) (assembly registry (parallel frame)) := by
  have reordering := unarrange registry owner channel first second offered frame input
  simp only [exposed, exposedMarks, Actor.marks, Actor.render, Actor.origin,
    ActiveSyntaxMarking.mark, out1] at reordering
  rw [idleMark, idleRender, original, lower_binary_receiver,
    RuntimeIdleUpdate.mark_receiver, RuntimeIdleUpdate.rename_receiver] at reordering
  exact reordering

/-- The original selected publication and selected decoder determine the
whole supplied endpoint, although other public pairs may also be enabled. -/
theorem supplied_public_receipt {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Var Γ .nm)
    (offered : registry owner = .offered (.var channel) (.var first) (.var second))
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (input : Fin frame.length) (persistent : Bool) (body : Proc (.nm :: .nm :: Γ))
    (original : frame[input.val] = binaryReceiver persistent (.var channel) body)
    {target : Proc (World n Γ)}
    (actual : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target)
    (traced : TracedExposure (assemblyMarks registry frame) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = .idle input.val)
    (chosenOutput : traced.continuation.outputOrigin = .publication owner) :
    StructuralEq target
      (par (nu (freshBody n owner ⟨.var first, .var second, body⟩))
        (if persistent then
          par (rep (receivePair (.var (ambient n .nm channel))
            (rename (liftRen (ambient n) [.nm, .nm]) (lower body))))
            (rest registry owner (.var first) (.var second) frame input)
         else rest registry owner (.var first) (.var second) frame input)) := by
  classical
  let guard := rename (liftRen (ambient n) [.nm]) (PublicRoles.decoderBody body)
  let guardMarks := ActiveSyntaxMarking.mark (.idle input.val : Origin n) (PublicRoles.decoderBody body)
  have reorder := selected_reordering registry owner (.var channel) (.var first) (.var second)
    offered frame input persistent body original
  obtain ⟨traced', inputEq, outputEq⟩ := RuntimeIdleUpdate.rebase_trace traced reorder
  have endpoint := ActiveUnaryPersistentBoundary.receiver_endpoint persistent (ambient n .nm channel)
    (key n owner .session) guard (rest registry owner (.var first) (.var second) frame input)
    (.idle input.val) (.publication owner) (by intro same; cases same) guardMarks
    (restMarks registry owner (.var first) (.var second) frame input)
    ((ActiveSyntaxMarking.mark_fits _ _).rename (liftRen (ambient n) [.nm]))
    (rest_fits registry owner (.var first) (.var second) frame input)
    (rest_unused registry owner (.var first) (.var second) frame input heads)
    (rest_single registry owner (.var first) (.var second) frame input heads)
    (rest_count_zero registry owner (.var first) (.var second) frame input heads)
    (actual.changeSource reorder.erase) traced' unary
    (inputEq.trans chosenInput) (outputEq.trans chosenOutput)
  dsimp only [guard] at endpoint
  have decoded := decoder_receipt n owner ⟨.var first, .var second, body⟩
  change inst (rename (liftRen (ambient n) [.nm]) (PublicRoles.decoderBody body))
    (.var (key n owner .session)) = nu (freshBody n owner ⟨.var first, .var second, body⟩) at decoded
  rw [decoded] at endpoint
  cases persistent with
  | false => exact endpoint
  | true =>
      have receiverEquality := receivePair_rename (ambient n) (.var channel) (lower body)
      change inp1 (.var (ambient n .nm channel))
          (rename (liftRen (ambient n) [.nm]) (PublicRoles.decoderBody body)) = _ at receiverEquality
      rw [receiverEquality] at endpoint
      exact endpoint

private theorem slot_support {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner other : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second) :
    countVar (key n owner .callback) ((registry other).placed n other) = 0 := by
  by_cases same : other = owner
  · subst other; rw [offered]; exact CallbackSupport.offered_callback_full_count_zero _ _ _ _ _
  · exact CallbackSupport.other_slot_full_count_zero n owner other (Ne.symm same) .callback (registry other)

theorem registry_support {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ) (frame : Proc Γ)
    (offered : registry owner = .offered channel first second) :
    countVar (key n owner .callback) (registryTarget registry frame) = 0 := by
  have slots : ∀ owners : List (Fin n),
      countVar (key n owner .callback)
        (parallel (owners.map (fun other => (registry other).placed n other))) = 0 := by
    intro owners
    induction owners with
    | nil => rfl
    | cons other rest ih =>
        simp only [List.map_cons, parallel, par, countVar, countVarArgs, weakenVar, Nat.add_zero]
        rw [slot_support registry owner other channel first second offered, ih]
  simp only [registryTarget, par, countVar, countVarArgs, weakenVar, Nat.add_zero]
  rw [slots, CallbackSupport.frame_full_count_zero, Nat.zero_add]

theorem rest_support {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Name Γ)
    (offered : registry owner = .offered channel first second)
    (live : ∀ other, Live (registry other))
    (frame : List (Proc Γ)) (input : Fin frame.length) :
    countVar (key n owner .callback) (rest registry owner first second frame input) = 0 := by
  have original := (ScopedOpening.support_zero_structural
    (registry_equation registry (parallel frame) live) (key n owner .callback)).mp
      (registry_support registry owner channel first second (parallel frame) offered)
  have arranged := (ScopedOpening.support_zero_structural
    (arrange registry owner channel first second offered frame input).erase (key n owner .callback)).mp original
  simp only [exposed, par, countVar, countVarArgs, weakenVar, Nat.add_zero] at arranged
  omega

def committedTail {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (persistent : Bool) (frame : List (Proc Γ)) (input : Fin frame.length) : Proc (World n Γ) :=
  par (parallel ((otherEntries registry owner).map Actor.render))
    (rename (ambient n) (lower (parallel (updatedFrame persistent frame input))))

private theorem exchange {Γ : Ctx sig} (a b c : Proc Γ) :
    StructuralEq (par a (par b c)) (par b (par a c)) :=
  (StructuralEq.parAssoc _ _ _).symm.trans
    ((StructuralEq.par (.parComm _ _) (.refl _)).trans (.parAssoc _ _ _))

theorem retained_receiver {Γ : Ctx sig} {n : Nat} (frame : List (Proc Γ))
    (input : Fin frame.length) (channel : Var Γ .nm) (body : Proc (.nm :: .nm :: Γ))
    (original : frame[input.val] = binaryReceiver true (.var channel) body) :
    rep (receivePair (.var (ambient n .nm channel))
      (rename (liftRen (ambient n) [.nm, .nm]) (lower body))) =
      rename (ambient n) (lower frame[input.val]) := by
  rw [original]
  change rep _ = rename (ambient n) (lower (rep (inp2 (.var channel) body)))
  rw [lower_rep, lower_inp2, rename_rep, receivePair_rename]
  rfl

theorem residual_arrangement {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Var Γ .nm) (frame : List (Proc Γ))
    (input : Fin frame.length) (persistent : Bool) (body : Proc (.nm :: .nm :: Γ))
    (original : frame[input.val] = binaryReceiver persistent (.var channel) body) :
    StructuralEq
      (if persistent then
        par (rep (receivePair (.var (ambient n .nm channel))
          (rename (liftRen (ambient n) [.nm, .nm]) (lower body))))
          (rest registry owner (.var first) (.var second) frame input)
       else rest registry owner (.var first) (.var second) frame input)
      (par (Actor.render (.waiter owner (.var first) (.var second)))
        (committedTail registry owner persistent frame input)) := by
  cases persistent with
  | false =>
      simp only [Bool.false_eq_true, if_false, rest, committedTail, updatedFrame]
      rw [remaining_idle]
      exact .refl _
  | true =>
      simp only [if_true]
      rw [retained_receiver frame input channel body original]
      simp only [rest, committedTail, updatedFrame, if_true, parallel, lower_par, rename_par]
      rw [remaining_idle]
      exact (exchange _ _ _).trans (.par (.refl _) (exchange _ _ _))

private theorem owners_equation {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (live : ∀ owner, Live (registry owner)) (owners : List (Fin n)) :
    StructuralEq (parallel (owners.map (fun owner => (registry owner).placed n owner)))
      (parallel ((owners.flatMap (fun owner => slotActors owner (registry owner))).map Actor.render)) := by
  induction owners with
  | nil => exact .refl _
  | cons owner rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, parallel]
      exact (StructuralEq.par (slot_equation owner (registry owner) (live owner)) ih).trans
        (parallel_append _ _)

theorem committed_shape {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ) (owner : Fin n)
    (live : ∀ owner, Live (registry owner)) (call : Call Γ) (frame : Proc Γ) :
    StructuralEq (registryTarget (commit registry owner call) frame)
      (par ((Slot.pending .callback call).placed n owner)
        (par (parallel ((otherEntries registry owner).map Actor.render))
          (rename (ambient n) (lower frame)))) := by
  have reordered := parallel_perm ((List.perm_cons_erase (List.mem_finRange owner)).map
    (fun other => (commit registry owner call other).placed n other))
  simp only [List.map_cons, parallel] at reordered
  have selected : commit registry owner call owner = .pending .callback call := Function.update_self _ _ _
  rw [selected] at reordered
  have unchanged :
      ((List.finRange n).erase owner).map (fun other => (commit registry owner call other).placed n other) =
      ((List.finRange n).erase owner).map (fun other => (registry other).placed n other) := by
    apply List.map_congr_left
    intro other member
    have different := ((List.nodup_finRange n).mem_erase_iff.mp member).1
    rw [commit, Function.update_of_ne different]
  rw [unchanged] at reordered
  have shaped := owners_equation registry live ((List.finRange n).erase owner)
  exact (StructuralEq.par (reordered.trans (.par (.refl _) shaped)) (.refl _)).trans
    (.parAssoc _ _ _)

/-- Every actual selected publication and receiver yields the supplied
closed endpoint of their updated occurrence registry, including the original
persistent listener and every other offered or pending occurrence. -/
theorem supplied_public_update {Γ : Ctx sig} {n : Nat} (registry : Fin n → Slot Γ)
    (owner : Fin n) (channel first second : Var Γ .nm)
    (offered : registry owner = .offered (.var channel) (.var first) (.var second))
    (live : ∀ owner, Live (registry owner))
    (frame : List (Proc Γ)) (heads : ∀ atom ∈ frame, IdleFrame.Head atom)
    (input : Fin frame.length) (persistent : Bool) (body : Proc (.nm :: .nm :: Γ))
    (original : frame[input.val] = binaryReceiver persistent (.var channel) body)
    {target : Proc (World n Γ)}
    (actual : ScopedCommunicationInversion.Exposure (assembly registry (parallel frame)) target)
    (traced : TracedExposure (assemblyMarks registry frame) actual)
    (unary : inputHeader actual.selected = .input1)
    (chosenInput : traced.continuation.inputOrigin = .idle input.val)
    (chosenOutput : traced.continuation.outputOrigin = .publication owner) :
    StructuralEq ((privateScope n).close target)
      ((privateScope n).close (registryTarget
        (commit registry owner ⟨.var first, .var second, body⟩)
        (parallel (updatedFrame persistent frame input)))) := by
  let call : Call Γ := ⟨.var first, .var second, body⟩
  let tail := committedTail registry owner persistent frame input
  have receipt := supplied_public_receipt registry owner channel first second offered frame heads
    input persistent body original actual traced unary chosenInput chosenOutput
  have arranged := residual_arrangement registry owner channel first second frame input persistent body original
  have restSupport := rest_support registry owner (.var channel) (.var first) (.var second) offered live frame input
  have retainedSupport : countVar (key n owner .callback)
      (if persistent then
        par (rep (receivePair (.var (ambient n .nm channel))
          (rename (liftRen (ambient n) [.nm, .nm]) (lower body))))
          (rest registry owner (.var first) (.var second) frame input)
       else rest registry owner (.var first) (.var second) frame input) = 0 := by
    cases persistent with
    | false => exact restSupport
    | true =>
        simp only [if_true]
        rw [retained_receiver frame input channel body original]
        simp only [par, countVar, countVarArgs, weakenVar, Nat.add_zero]
        rw [ambient_has_no_private, restSupport]
  have remainderSupport := (ScopedOpening.support_zero_structural arranged (key n owner .callback)).mp retainedSupport
  have unused : countVar (Var.succ (key n owner .callback))
      (par (freshBody n owner call)
        (weaken (par (Actor.render (.waiter owner (.var first) (.var second))) tail))) = 0 := by
    simp only [par, countVar, countVarArgs, weakenVar, Nat.add_zero]
    rw [fresh_body_support, ScopedOpening.count_weaken, Nat.zero_add]
    exact remainderSupport
  have actualClosed := (privateScope n).congr (receipt.trans (.par (.refl _) arranged))
  exact actualClosed.trans ((closed_receipt n owner call tail unused).trans
    ((privateScope n).congr (committed_shape registry owner live call
      (parallel (updatedFrame persistent frame input))).symm))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimePublicUpdate
