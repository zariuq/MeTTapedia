import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceReadout

/-!
# Exact split surfaces in the admitted parser domain

The two actual indexed participants retain independently accepted entire
signature Patterns. Their exact cover spends two physical cells even when
the signing atoms agree. This reads the concrete split rho interface; it
does not add an authored split rewrite to the generated whole-rule language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

theorem ConfigAdmitted.recv_signature {location : RawCostName} {source : RawCostTerm}
    {index : Nat} {endpoint : RawRecvEndpoint} (image : ConfigAdmitted location source)
    (found : recvAt? index source = some endpoint) : SignatureAdmitted endpoint.sig := by
  cases image with
  | purse stack => simp [recvAt?] at found
  | par first second => simp [recvAt?] at found
  | code code =>
      cases code with
      | zero => simp [recvAt?] at found
      | drop name => simp [recvAt?] at found
      | par first second => simp [recvAt?] at found
      | signed process signature =>
          cases process <;> simp [recvAt?] at found
          subst endpoint
          rw [signature.normalize_identity]
          exact signature

theorem ConfigAdmitted.send_signature {location : RawCostName} {source : RawCostTerm}
    {index : Nat} {endpoint : RawSendEndpoint} (image : ConfigAdmitted location source)
    (found : sendAt? index source = some endpoint) : SignatureAdmitted endpoint.sig := by
  cases image with
  | purse stack => simp [sendAt?] at found
  | par first second => simp [sendAt?] at found
  | code code =>
      cases code with
      | zero => simp [sendAt?] at found
      | drop name => simp [sendAt?] at found
      | par first second => simp [sendAt?] at found
      | signed process signature =>
          cases process <;> simp [sendAt?] at found
          subst endpoint
          rw [signature.normalize_identity]
          exact signature

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated ActivationGenerated.SerializationAdmission Mettapedia.OSLF.MeTTaIL.Syntax

theorem RawSplitOccurrenceCover.admitted_signatures {location : RawCostName} {config : RawCostConfig}
    (cover : RawSplitOccurrenceCover config) (images : config.Forall (ConfigAdmitted location)) :
    SignatureAdmitted cover.receiver.sig ∧ SignatureAdmitted cover.sender.sig := by
  exact ⟨(List.forall_iff_forall_mem.mp images cover.recvSource
    (List.fst_mem_of_mem_zipIdx cover.recvOccurrence)).recv_signature cover.recvFound,
    (List.forall_iff_forall_mem.mp images cover.sendSource
      (List.fst_mem_of_mem_zipIdx cover.sendOccurrence)).send_signature cover.sendFound⟩

theorem RawSplitOccurrenceCover.admitted_selected_length_two {location : RawCostName} {config : RawCostConfig}
    (cover : RawSplitOccurrenceCover config) (images : config.Forall (ConfigAdmitted location)) :
    cover.selected.length = 2 := by
  obtain ⟨receiver, sender⟩ := cover.admitted_signatures images
  have atomic : cover.selected.Forall (fun purse => purse.head.length = 1) := by
    rw [List.forall_iff_forall_mem]
    intro purse member
    exact (selected_purse_parts images cover.sourceOrdered member).2.1.length_eq_one
  have count := congrArg Multiset.card cover.exactSpend
  change (rawSelectedSpend cover.selected).card =
    (RawCostSig.normalize (cover.receiver.sig ++ cover.sender.sig) : Multiset String).card at count
  rw [rawSelectedSpend_card_eq_length atomic, RawCostSig.normalize_toMultiset] at count
  change cover.selected.length = (cover.receiver.sig ++ cover.sender.sig).length at count
  simpa only [List.length_append, receiver.length_eq_one, sender.length_eq_one] using count

/-- Both indexed surfaces are read back by the actual existing code and
signature parsers, independently of which located purse occurrence pays. -/
theorem RawSplitOccurrenceCover.admitted_fields {location : RawCostName} {config : RawCostConfig}
    (cover : RawSplitOccurrenceCover config) (images : config.Forall (ConfigAdmitted location)) :
    ∃ bodySource payloadSource recvSignatureSource sendSignatureSource,
      ∃ (recvSignature : TypedSignature recvSignatureSource) (sendSignature : TypedSignature sendSignatureSource),
        ∃ body payload,
          CodeImage 1 bodySource body ∧ CodeImage 0 payloadSource payload ∧
          signature? recvSignatureSource = some recvSignature ∧ signature? sendSignatureSource = some sendSignature ∧
          cover.receiver.sig = [literalAuthorityKey recvSignatureSource] ∧
          cover.sender.sig = [literalAuthorityKey sendSignatureSource] ∧
          cover.receiver.body.normalize = (literalEncodeTerm body).normalize ∧
          cover.sender.payload.normalize = (literalEncodeTerm payload).normalize := by
  have receiver := List.forall_iff_forall_mem.mp images cover.recvSource
    (List.fst_mem_of_mem_zipIdx cover.recvOccurrence)
  have sender := List.forall_iff_forall_mem.mp images cover.sendSource
    (List.fst_mem_of_mem_zipIdx cover.sendOccurrence)
  obtain ⟨bodySource, body, bodyImage, bodySame⟩ := (receiver.recv_code cover.recvFound).readback
  obtain ⟨payloadSource, payload, payloadImage, payloadSame⟩ := (sender.send_code cover.sendFound).readback
  obtain ⟨recvSignatureSource, recvSignature, recvChecked, recvAuthority⟩ :=
    (receiver.recv_signature cover.recvFound).accepted_pattern
  obtain ⟨sendSignatureSource, sendSignature, sendChecked, sendAuthority⟩ :=
    (sender.send_signature cover.sendFound).accepted_pattern
  exact ⟨bodySource, payloadSource, recvSignatureSource, sendSignatureSource, recvSignature, sendSignature,
    body, payload, bodyImage, payloadImage, recvChecked, sendChecked, recvAuthority, sendAuthority, bodySame, payloadSame⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
