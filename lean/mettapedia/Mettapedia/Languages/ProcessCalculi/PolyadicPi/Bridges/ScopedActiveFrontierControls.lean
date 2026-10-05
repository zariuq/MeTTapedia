import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

/-!
# Private-scope, occurrence, and guard controls for active frontiers

The first control communicates across two separately written restrictions.
Its payload is the sender's private name, not the receiver's private name.
The persistent-listener example keeps an equal duplicate output occurrence.
The guard control rejects flattening an enabled process out of an input body.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi

abbrev publicWorld : Ctx sig := [.nm]
abbrev commonWorld : Ctx sig := [.nm, .nm, .nm]

def publicChannel : Name publicWorld := .var .zero

def privateSender : Proc publicWorld :=
  nu (out1 (.var (.succ .zero)) (.var .zero))

def privateReceiver : Proc publicWorld :=
  nu (inp1 (.var (.succ .zero))
    (out1 (.var .zero) (.var (.succ .zero))))

def independentScopes : Proc publicWorld := par privateSender privateReceiver

def senderFrontier : Frontier publicWorld :=
  restrict (singleton (out1 (.var (.succ .zero)) (.var .zero)))

def receiverFrontier : Frontier publicWorld :=
  restrict (singleton (inp1 (.var (.succ .zero))
    (out1 (.var .zero) (.var (.succ .zero)))))

def independentFrontier : Frontier publicWorld := merge senderFrontier receiverFrontier

theorem sender_normalization : normalize privateSender = senderFrontier := by
  rw [privateSender, normalize_nu, normalize_out1]
  rfl

theorem receiver_normalization : normalize privateReceiver = receiverFrontier := by
  rw [privateReceiver, normalize_nu, normalize_inp1]
  rfl

theorem independent_normalization : normalize independentScopes = independentFrontier := by
  rw [independentScopes, normalize_par, sender_normalization, receiver_normalization]
  rfl

def responseBody : Proc (.nm :: commonWorld) :=
  out1 (.var .zero) (.var (.succ .zero))

/-- Actual source communication across separate restrictions keeps both
private names, with the received sender name in the subject position. -/
theorem independently_scoped_communication :
    StepModulo independentScopes
      (nu (nu (par (out1 (.var (.succ .zero)) (.var .zero)) nil))) := by
  have selected : independentFrontier.atoms.Perm
      [out1 (.var (.succ (.succ .zero))) (.var (.succ .zero)),
        inp1 (.var (.succ (.succ .zero))) responseBody] := .refl _
  obtain ⟨redex, endpoint, before, firing, after⟩ :=
    independentFrontier.unary_pair (.var (.succ (.succ .zero)))
      (.var (.succ .zero)) responseBody [] selected
  have initial : StructuralEq independentScopes independentFrontier.term := by
    rw [← independent_normalization]
    exact normalization _
  exact ⟨redex, endpoint, .trans initial before, firing, after⟩

/-- The common world has both private binders and the old public name. -/
theorem independent_scope_world : (normalize independentScopes).world = commonWorld := by
  rw [independent_normalization]
  rfl

theorem public_channel_stays_shared :
    rename (mergeLeft senderFrontier receiverFrontier)
        (Term.var (.succ .zero) : Name (.nm :: publicWorld)) =
      rename (mergeRight senderFrontier receiverFrontier)
        (Term.var (.succ .zero) : Name (.nm :: publicWorld)) := rfl

/-- Identically positioned local variables in two operands do not become
one private channel when their scopes are merged. -/
theorem private_channels_stay_distinct :
    rename (mergeLeft senderFrontier receiverFrontier)
        (Term.var .zero : Name (.nm :: publicWorld)) ≠
      rename (mergeRight senderFrontier receiverFrontier)
        (Term.var .zero : Name (.nm :: publicWorld)) := by
  intro collision
  cases collision

def duplicatedRequests : Proc publicWorld :=
  par (out1 publicChannel publicChannel)
    (par (out1 publicChannel publicChannel) (rep (inp1 publicChannel nil)))

def duplicateFrontier : Frontier publicWorld :=
  merge (singleton (out1 publicChannel publicChannel))
    (merge (singleton (out1 publicChannel publicChannel))
      (singleton (rep (inp1 publicChannel nil))))

theorem duplicate_normalization : normalize duplicatedRequests = duplicateFrontier := by
  rw [duplicatedRequests, normalize_par, normalize_par, normalize_out1, normalize_rep]
  rfl

theorem duplicate_occurrences_count : (normalize duplicatedRequests).atoms.length = 3 := by
  rw [duplicate_normalization]
  rfl

/-- A selected firing consumes one occurrence and keeps the identical
other request, as well as the original persistent receiver. -/
theorem duplicate_request_server_firing :
    StepModulo duplicatedRequests
      (par nil (par (rep (inp1 publicChannel nil))
        (par (out1 publicChannel publicChannel) nil))) := by
  have selected : duplicateFrontier.atoms.Perm
      [out1 publicChannel publicChannel, rep (inp1 publicChannel nil),
        out1 publicChannel publicChannel] := by
    exact .cons _ (.swap _ _ [])
  obtain ⟨redex, endpoint, before, firing, after⟩ :=
    duplicateFrontier.unary_server publicChannel publicChannel nil
      [out1 publicChannel publicChannel] selected
  have initial : StructuralEq duplicatedRequests duplicateFrontier.term := by
    rw [← duplicate_normalization]
    exact normalization _
  exact ⟨redex, endpoint, .trans initial before, firing, after⟩

def enabledBody : Proc publicWorld :=
  par (out1 publicChannel publicChannel) (inp1 publicChannel nil)

def guardedBody : Proc publicWorld := inp1 publicChannel (weaken enabledBody)

theorem inner_body_enabled : Step enabledBody nil := .comm1 _ _ _

theorem input_guard_keeps_whole_body : normalize guardedBody = singleton guardedBody := by
  rw [guardedBody, normalize_inp1]

/-- An enabled redex underneath an input remains blocked until that input
is consumed; the frontier never silently exposes it. -/
theorem input_guard_blocks_inner_firing {endpoint : Proc publicWorld} :
    ¬ Step guardedBody endpoint := by
  intro firing
  cases firing

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier.Controls
