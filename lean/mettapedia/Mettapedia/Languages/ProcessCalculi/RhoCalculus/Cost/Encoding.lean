import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Runtime

/-!
# Cost-rho executable encoding boundary

This module proves that the typed-to-raw encoding loses no declarative syntax
and that every raw wire encoder has a matching decoder.  The reverse
typed/raw direction is intentionally not stated as literal equality: raw
signatures may be presented in noncanonical list order, while typed
signatures are multisets.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-! ## Typed syntax to raw syntax -/

mutual
  @[simp]
  theorem decodeCostName_encodeCostName (name : CostName String) :
      decodeCostName (encodeCostName name) = name := by
    cases name <;>
      simp [encodeCostName, decodeCostName, decodeCostTerm_encodeCostTerm]

  @[simp]
  theorem decodeCostProc_encodeCostProc (proc : CostProc String) :
      decodeCostProc (encodeCostProc proc) = proc := by
    cases proc <;>
      simp [encodeCostProc, decodeCostProc, decodeCostName_encodeCostName,
        decodeCostTerm_encodeCostTerm, decodeCostProc_encodeCostProc]

  @[simp]
  theorem decodeCostTerm_encodeCostTerm (term : CostTerm String) :
      decodeCostTerm (encodeCostTerm term) = term := by
    cases term <;>
      simp [encodeCostTerm, decodeCostTerm, decodeCostName_encodeCostName,
        decodeCostProc_encodeCostProc, decodeCostTerm_encodeCostTerm,
        decodeCostStack_encodeCostStack]

  @[simp]
  theorem decodeCostStack_encodeCostStack (stack : CostStack String) :
      decodeCostStack (encodeCostStack stack) = stack := by
    cases stack <;>
      simp [encodeCostStack, decodeCostStack, decodeCostStack_encodeCostStack]
end

/-! ## Raw syntax wire round trips -/

namespace CostWire

/-- `Option` traversal preserves a list when its element function returns every
input unchanged. -/
theorem mapM_eq_some_self {Alpha : Type} (f : Alpha → Option Alpha)
    (hf : ∀ item, f item = some item) :
    ∀ items : List Alpha, List.mapM f items = some items
  | [] => rfl
  | item :: rest => by
      simp [hf item, mapM_eq_some_self f hf rest]

/-- Decoding an elementwise encoding under `List.mapM` recovers the source
list. -/
theorem mapM_map_eq_some {Alpha Beta : Type} (encode : Alpha → Beta)
    (decode : Beta → Option Alpha) (h : ∀ item, decode (encode item) = some item) :
    ∀ items : List Alpha, List.mapM decode (items.map encode) = some items
  | [] => rfl
  | item :: rest => by
      simp [h item, mapM_map_eq_some encode decode h rest]

@[simp]
theorem decodeSig_encodeSig (sig : RawCostSig) :
    decodeSig (encodeSig sig) = some sig := by
  simp only [encodeSig, decodeSig]
  exact mapM_map_eq_some CostWire.symbol
    (fun wire => match wire with | .symbol atom => some atom | _ => none)
    (fun atom => rfl) sig

@[simp]
theorem mapM_decodeSig_encodeSig (stack : RawCostStack) :
    stack.mapM (decodeSig ∘ encodeSig) = some stack :=
  mapM_eq_some_self (decodeSig ∘ encodeSig) decodeSig_encodeSig stack

mutual
  @[simp]
  theorem decodeName_encodeName (name : RawCostName) :
      decodeName (encodeName name) = some name := by
    cases name with
    | bvar index => rfl
    | quote term => simp [encodeName, decodeName, decodeTerm_encodeTerm]
    | signature sig =>
        simp [encodeName, decodeName, encodeSig, decodeSig,
          mapM_eq_some_self]

  @[simp]
  theorem decodeProc_encodeProc (proc : RawCostProc) :
      decodeProc (encodeProc proc) = some proc := by
    cases proc <;>
      simp [encodeProc, decodeProc, decodeName_encodeName,
        decodeTerm_encodeTerm, decodeProc_encodeProc]

  @[simp]
  theorem decodeTerm_encodeTerm (term : RawCostTerm) :
      decodeTerm (encodeTerm term) = some term := by
    cases term <;>
      simp [encodeTerm, decodeTerm, decodeName_encodeName,
        decodeProc_encodeProc, decodeTerm_encodeTerm, decodeSig_encodeSig,
        mapM_decodeSig_encodeSig]
end

@[simp]
theorem decodeFunding_encodeFunding (funding : RawFundingContribution) :
    decodeFunding (encodeFunding funding) = some funding := by
  cases funding
  simp [encodeFunding, decodeFunding]

@[simp]
theorem decodeEvent_encodeEvent (event : RawEmittedEvent) :
    decodeEvent (encodeEvent event) = some event := by
  cases event with
  | mk id causes funding rawSpend =>
      have causes_ok :
          List.mapM decodeNatural (causes.map CostWire.natural) = some causes :=
        mapM_map_eq_some CostWire.natural decodeNatural (fun cause => rfl) causes
      have funding_ok :
          List.mapM decodeFunding (funding.map encodeFunding) = some funding :=
        mapM_map_eq_some encodeFunding decodeFunding
          decodeFunding_encodeFunding funding
      simp only [encodeEvent, decodeEvent, decodeSig_encodeSig]
      rw [causes_ok, funding_ok]
      rfl

@[simp]
theorem decodeReceipt_encodeReceipt (receipt : RawReceipt) :
    decodeReceipt (encodeReceipt receipt) = some receipt := by
  simp only [encodeReceipt, decodeReceipt]
  exact mapM_map_eq_some encodeEvent decodeEvent
    decodeEvent_encodeEvent receipt

@[simp]
theorem decodePrefixStatus_encodePrefixStatus (status : RawPrefixStatus) :
    decodePrefixStatus (encodePrefixStatus status) = some status := by
  cases status <;> rfl

@[simp]
theorem decodePrefix_encodePrefix (result : RawCausalPrefix) :
    decodePrefix (encodePrefix result) = some result := by
  cases result
  simp [encodePrefix, decodePrefix]

/-! ## Rejection examples at the wire boundary -/

theorem malformed_purse_wire_rejected :
    decodeTerm (.node "purse" [.symbol "pay", .symbol "not-a-stack"]) = none := by
  rfl

theorem location_signature_confusion_rejected :
    decodeFunding (.node "funding"
      [.node "term-nil" [], .node "signature" [.symbol "alice"]]) = none := by
  rfl

end CostWire

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
