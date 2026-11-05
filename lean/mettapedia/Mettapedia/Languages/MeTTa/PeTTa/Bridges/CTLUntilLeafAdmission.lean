import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilAdmissionFrame

/-!
# Uniform admission of the reached EU publication leaf

One actual canonical guard declaration serves every captured predecessor.
The request is constructed from the reached principal reading, and both
admission checkers return their actual certificates. Complete decoded rows
exclude reference handoff; allocation suspension remains a source outcome.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open FlatQueryRowCodec (Codec)
open CTLUntilScopedRound (Query Decoded)
open CTLUntilAdmissionFrame (AdmissionFrame)
open CTLUntilMixedStore (render Row)
open CTLUntilSourceRows (number)
open NamedGuardedCandidateBatch (State)

theorem declaration_same_fields (first second : LiteralQuerySource.Request)
    (handle : first.handle = second.handle) (payload : first.payload = second.payload) :
    NamedPresenceSource.declaration first = NamedPresenceSource.declaration second := by
  simp only [NamedPresenceSource.declaration, CapturedPresenceSource.source,
    CapturedPresenceSource.equality, CapturedCollectedOnceSource.source,
    CapturedOnceSource.source, CapturedOnceSource.query, handle, payload]

structure GuardProfile {Label : Type} (codec : Codec Label) (label : Label) (query : Query)
    (program : SpaceSemantics.Program) where
  occurrence : Nat
  row : program.equations[occurrence]? = some (NamedPresenceSource.declaration
    (CTLUntilPublicationSource.request codec query.satisfactionHandle label 0))
  otherHeads : ∀ index equation, program.equations[index]? = some equation →
    index ≠ occurrence → equation.head ≠ "in"
  leftEvaluated : Eval.argumentIsRaw program "in" 0 = false
  rightEvaluated : Eval.argumentIsRaw program "in" 1 = false

variable {Context Label : Type}

theorem GuardProfile.row_for {codec : Codec Label} {label : Label} {query : Query}
    {program : SpaceSemantics.Program} (profile : GuardProfile codec label query program) (node : Nat) :
    program.equations[profile.occurrence]? = some (NamedPresenceSource.declaration
      (CTLUntilPublicationSource.request codec query.satisfactionHandle label node)) :=
  profile.row.trans (congrArg some (declaration_same_fields _ _ rfl rfl))

theorem request_from_reading (codec : Codec Label) (label : Label) (node : Nat) (query : Query)
    (principal : Environment)
    (reading : read principal query.template.body.firstCode = render codec (.satisfaction label node)) :
    LiteralQuerySource.ofPattern query.satisfactionHandle
      (read principal query.template.body.firstCode) (.symbol "t") =
      some (CTLUntilPublicationSource.request codec query.satisfactionHandle label node) := by
  rw [reading]
  exact LiteralQuerySource.ofPattern_complete _ _
    (CTLUntilPublicationSource.satisfaction_literal codec label node)
    (by simp [LiteralQuerySource.ordinaryQuery, render]) (.symbol "t") (.symbol "t")

/-- Admission comes from the actual source declaration and reached frame.
Neither an available copy identity nor a successful future run is assumed. -/
theorem invoke_not_reference (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (profile : GuardProfile codec label query program)
    (distinct : query.names.temporary ≠ query.names.result)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (admitted : AdmissionFrame codec label operand round query [] caller)
    (valid : Decoded codec query.handles state) (saved : ScopedCursor Context) :
    (GuardedNestedQuerySource.invoke program query.template caller state context origins pending).execution.stop ≠
      .reference saved := by
  obtain ⟨frame, resultFresh, temporaryFresh, finished, output⟩ := admitted
  cases frame with
  | publish _ resolved fixed node bound =>
    obtain ⟨principal, resolved⟩ := resolved
    have readings := fixed principal (resolve_sound resolved)
    have nodeRead := bound principal (resolve_sound resolved)
    obtain ⟨firstRead, secondRead⟩ := CTLUntilCandidateAdmission.payload_readings codec label round node query.names principal
      readings.1 readings.2.2.2 nodeRead
    let request := CTLUntilPublicationSource.request codec query.satisfactionHandle label node
    let input := (query.template.candidate caller context origins request).input program state pending
    have requested := request_from_reading codec label node query principal firstRead
    obtain ⟨guard, receipt, guardPrepared, bodyPrepared, _secondValue⟩ :=
      NamedGuardedInsertionAdmission.canonical_admission input query.template.body principal (codec.encode label) (number node)
        (render codec (.frontier label (round + 1) node)) profile.occurrence
        resolved readings.1 nodeRead (codec.literal label) (.grounded _) rfl
        (profile.row_for node) profile.otherHeads profile.leftEvaluated profile.rightEvaluated rfl rfl rfl
        temporaryFresh resultFresh distinct firstRead secondRead
        (CTLUntilPublicationSource.frontier_literal codec label (round + 1) node)
        (CTLUntilPublicationSource.satisfaction_ordinary codec label node)
        (CTLUntilPublicationSource.frontier_ordinary codec label (round + 1) node)
    obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.satisfactionHandle (by simp [Query.handles])
    have noReference := CTLUntilCandidateAdmission.decoded_not_reference codec label node input query.template.body
      guard receipt guardPrepared bodyPrepared finished output rfl atoms rows snapshot decoded
    intro stopped
    unfold GuardedNestedQuerySource.invoke at stopped
    dsimp only at stopped
    split at stopped
    next inconsistent => simp [resolved] at inconsistent
    next actualPrincipal actualResolved =>
      have same := Option.some.inj (actualResolved.symm.trans resolved)
      subst actualPrincipal
      split at stopped
      next unavailable =>
        have impossible : (none : Option LiteralQuerySource.Request) = some request :=
          unavailable.symm.trans requested
        cases impossible
      next actualRequest actualRequested =>
        have same := Option.some.inj (actualRequested.symm.trans requested)
        subst actualRequest
        dsimp only at stopped
        split at stopped
        next refused => exact noReference refused
        · cases stopped
        · cases stopped

theorem leaf_not_reference (codec : Codec Label) (label operand : Label) (round : Nat) (query : Query)
    (program : SpaceSemantics.Program) (profile : GuardProfile codec label query program)
    (distinct : query.names.temporary ≠ query.names.result)
    (caller : Control) (state : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (admitted : AdmissionFrame codec label operand round query [] caller)
    (valid : Decoded codec query.handles state) (saved : ScopedCursor Context) :
    ((GuardedNestedQuerySource.leaf program query.template Context).execute caller state context origins pending).stop ≠
      .reference saved :=
  invoke_not_reference codec label operand round query program profile distinct caller state context origins pending admitted valid saved

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafAdmission
