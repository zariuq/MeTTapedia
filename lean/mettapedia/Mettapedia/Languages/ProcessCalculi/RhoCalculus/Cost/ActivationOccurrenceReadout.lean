import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceCover
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSerializationRuntime

/-!
# Admitted fields of exact funded occurrences

Actual selected surfaces retain checked entire-signature patterns and the
existing parser's closed code witnesses. The physical cover is not replaced:
a whole occurrence in this image selects one singleton-headed purse, whose
ordered tail remains admitted at the configuration's fixed funding location.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem SignatureAdmitted.accepted_pattern {raw : RawCostSig} (image : SignatureAdmitted raw) :
    ∃ source, ∃ signature : TypedSignature source,
      signature? source = some signature ∧ raw = [literalAuthorityKey source] := by
  cases image with
  | accepted signature checked => exact ⟨_, signature, checked, rfl⟩

mutual
  theorem NameAdmitted.runtimeBinderSafeAt :
      ∀ {depth : Nat} {name : RawCostName}, NameAdmitted depth name →
        name.runtimeBinderSafeAt depth = true := by
    intro depth name image
    cases image with
    | bvar bound => simpa [RawCostName.runtimeBinderSafeAt] using bound
    | quote code => exact code.runtimeBinderSafeAt

  theorem CodeAdmitted.runtimeBinderSafeAt :
      ∀ {depth : Nat} {term : RawCostTerm}, CodeAdmitted depth term →
        term.runtimeBinderSafeAt depth = true := by
    intro depth term image
    cases image with
    | zero => rfl
    | drop name => exact name.runtimeBinderSafeAt
    | signed process signature => exact process.runtimeBinderSafeAt
    | par first second =>
        change (_ && _) = true
        rw [first.runtimeBinderSafeAt, second.runtimeBinderSafeAt]
        rfl

  theorem ProcAdmitted.runtimeBinderSafeAt :
      ∀ {depth : Nat} {process : RawCostProc}, ProcAdmitted depth process →
        process.runtimeBinderSafeAt depth = true := by
    intro depth process image
    cases image with
    | zero => rfl
    | send name code =>
        change (_ && _) = true
        rw [name.runtimeBinderSafeAt, code.runtimeBinderSafeAt]
        rfl
    | recv name code =>
        change (_ && _) = true
        rw [name.runtimeBinderSafeAt, code.runtimeBinderSafeAt]
        rfl
    | par first second =>
        change (_ && _) = true
        rw [first.runtimeBinderSafeAt, second.runtimeBinderSafeAt]
        rfl
end

theorem ConfigAdmitted.whole_signature {location : RawCostName} {source : RawCostTerm}
    {index : Nat} {redex : RawWholeRedex} (image : ConfigAdmitted location source)
    (found : wholeAt? index source = some redex) : SignatureAdmitted redex.sig := by
  cases image with
  | purse stack => simp [wholeAt?] at found
  | par first second => simp [wholeAt?] at found
  | code image =>
      cases image with
      | zero => simp [wholeAt?] at found
      | drop name => simp [wholeAt?] at found
      | par first second => simp [wholeAt?] at found
      | signed process signature =>
          cases process with
          | zero => simp [wholeAt?] at found
          | send name code => simp [wholeAt?] at found
          | recv name code => simp [wholeAt?] at found
          | par first second =>
              cases first <;> cases second <;> simp [wholeAt?] at found
              all_goals
                obtain ⟨_same, rfl⟩ := found
                rw [signature.normalize_identity]
                exact signature

theorem ConfigAdmitted.purse_parts {location purseLocation : RawCostName}
    {head : RawCostSig} {tail : RawCostStack}
    (image : ConfigAdmitted location (.purse purseLocation (head :: tail))) :
    purseLocation = location ∧ SignatureAdmitted head ∧ StackAdmitted tail := by
  cases image with
  | code image => cases image
  | purse stack =>
      cases stack with
      | cons signature rest => exact ⟨rfl, signature, rest⟩

theorem selected_purse_parts {location : RawCostName} {config : RawCostConfig}
    {selected : List RawSelectedPurse} (images : config.Forall (ConfigAdmitted location))
    (ordered : selected.Sublist config.purses) {purse : RawSelectedPurse}
    (member : purse ∈ selected) :
    purse.location = location ∧ SignatureAdmitted purse.head ∧ StackAdmitted purse.tail := by
  have mapped : purse.toTerm ∈ config.filter RawCostTerm.isActivePurse := by
    rw [← RawCostConfig.purses_map_toTerm config]
    exact List.mem_map.mpr ⟨purse, ordered.subset member, rfl⟩
  exact ConfigAdmitted.purse_parts (List.forall_iff_forall_mem.mp images purse.toTerm
    (List.mem_filter.mp mapped).1)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated.SerializationAdmission

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated ActivationGenerated.SerializationAdmission Mettapedia.OSLF.MeTTaIL.Syntax

theorem RawWholeOccurrenceCover.admitted_fields {location : RawCostName} {config : RawCostConfig}
    (cover : RawWholeOccurrenceCover config) (images : config.Forall (ConfigAdmitted location)) :
    ∃ bodySource payloadSource signatureSource,
      ∃ (signature : TypedSignature signatureSource), ∃ body payload,
      CodeImage 1 bodySource body ∧ CodeImage 0 payloadSource payload ∧
        signature? signatureSource = some signature ∧
        cover.redex.sig = [literalAuthorityKey signatureSource] ∧
        cover.redex.body.normalize = (literalEncodeTerm body).normalize ∧
        cover.redex.payload.normalize = (literalEncodeTerm payload).normalize := by
  have sourceImage := List.forall_iff_forall_mem.mp images cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  obtain ⟨receiver, message⟩ := sourceImage.whole_code cover.found
  obtain ⟨bodySource, body, bodyImage, bodySame⟩ := receiver.readback
  obtain ⟨payloadSource, payload, payloadImage, payloadSame⟩ := message.readback
  obtain ⟨signatureSource, signature, checked, authority⟩ :=
    (sourceImage.whole_signature cover.found).accepted_pattern
  exact ⟨bodySource, payloadSource, signatureSource, signature, body, payload,
    bodyImage, payloadImage, checked, authority, bodySame, payloadSame⟩

theorem RawWholeOccurrenceCover.admitted_selected_singleton {location : RawCostName}
    {config : RawCostConfig} (cover : RawWholeOccurrenceCover config)
    (images : config.Forall (ConfigAdmitted location)) :
    ∃ purse, cover.selected = [purse] ∧ purse.location = location ∧
      purse.head = cover.redex.sig ∧ StackAdmitted purse.tail := by
  have sourceImage := List.forall_iff_forall_mem.mp images cover.source
    (List.fst_mem_of_mem_zipIdx cover.occurrence)
  have signature := sourceImage.whole_signature cover.found
  have atomic : cover.selected.Forall (fun purse => purse.head.length = 1) := by
    rw [List.forall_iff_forall_mem]
    intro purse member
    exact (selected_purse_parts images cover.sourceOrdered member).2.1.length_eq_one
  have count := congrArg Multiset.card cover.exactSpend
  rw [rawSelectedSpend_card_eq_length atomic] at count
  change cover.selected.length = cover.redex.sig.length at count
  rw [signature.length_eq_one] at count
  obtain ⟨purse, same⟩ := List.length_eq_one_iff.mp count
  have parts := selected_purse_parts images cover.sourceOrdered (purse := purse) (by rw [same]; simp)
  refine ⟨purse, same, parts.1, ?_, parts.2.2⟩
  obtain ⟨atom, head⟩ := List.length_eq_one_iff.mp parts.2.1.length_eq_one
  obtain ⟨required, demand⟩ := List.length_eq_one_iff.mp signature.length_eq_one
  have sameAtom : atom = required := by
    simpa [same, rawSelectedSpend, RawCostSig.toMultiset, head, demand] using cover.exactSpend
  rw [head, demand, sameAtom]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
