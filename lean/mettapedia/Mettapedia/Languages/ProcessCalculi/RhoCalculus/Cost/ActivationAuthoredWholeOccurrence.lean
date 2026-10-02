import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAuthoredWholeInversion

/-!
# Same-occurrence realization of admitted authored whole firings

The source parser supplies the signed code. Literal normalized communication
locations and the selected physical purse are checked independently. The
existing collector and exact-cover catalogue are then derived, retaining the
same code index, purse occurrence and complete ordered tail.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match

theorem AuthoredWholeParserFields.normalized_code_shape
    {location : CostName LiteralAuthority} {source : Pattern}
    {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (fields : AuthoredWholeParserFields location source decoded bindings)
    (inputLocated : (literalEncodeName fields.inputChannel).normalize = (literalEncodeName location).normalize)
    (outputLocated : (literalEncodeName fields.outputChannel).normalize = (literalEncodeName location).normalize) :
    (literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel fields.outputChannel
      fields.body fields.payload fields.signature.val)).normalize =
      .signed (.par (.recv (literalEncodeName location).normalize (literalEncodeTerm fields.body).normalize)
        (.send (literalEncodeName location).normalize (literalEncodeTerm fields.payload).normalize))
        [literalAuthorityKey fields.signatureSource] ∨
    (literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel fields.outputChannel
      fields.body fields.payload fields.signature.val)).normalize =
      .signed (.par (.send (literalEncodeName location).normalize (literalEncodeTerm fields.payload).normalize)
        (.recv (literalEncodeName location).normalize (literalEncodeTerm fields.body).normalize))
        [literalAuthorityKey fields.signatureSource] := by
  have signature : encodeCostSig (fields.signature.val.map literalAuthorityKey) =
      [literalAuthorityKey fields.signatureSource] := by
    rw [fields.signature.property.1, literalEncodeSig_singleton]
  have rawReadout : literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
      fields.outputChannel fields.body fields.payload fields.signature.val) =
      .signed (if fields.reversed then
        .par (.send (literalEncodeName fields.outputChannel) (literalEncodeTerm fields.payload))
          (.recv (literalEncodeName fields.inputChannel) (literalEncodeTerm fields.body))
      else
        .par (.recv (literalEncodeName fields.inputChannel) (literalEncodeTerm fields.body))
          (.send (literalEncodeName fields.outputChannel) (literalEncodeTerm fields.payload)))
        [literalAuthorityKey fields.signatureSource] := by
    cases fields.reversed <;>
      change RawCostTerm.signed _ (encodeCostSig (fields.signature.val.map literalAuthorityKey)) = _ <;>
      rw [signature] <;> rfl
  rw [rawReadout]
  cases fields.reversed
  · simp only [Bool.false_eq_true, ite_false, RawCostTerm.normalize, RawCostProc.normalize,
      inputLocated, outputLocated, RawCostProc.components, List.singleton_append]
    rcases stableKeySort_pair_orders RawCostProc.key
      (.recv (literalEncodeName location).normalize (literalEncodeTerm fields.body).normalize)
      (.send (literalEncodeName location).normalize (literalEncodeTerm fields.payload).normalize) with ordered | swapped
    · exact Or.inl (by rw [ordered]; rfl)
    · exact Or.inr (by rw [swapped]; rfl)
  · simp only [ite_true, RawCostTerm.normalize, RawCostProc.normalize,
      inputLocated, outputLocated, RawCostProc.components, List.singleton_append]
    rcases stableKeySort_pair_orders RawCostProc.key
      (.send (literalEncodeName location).normalize (literalEncodeTerm fields.payload).normalize)
      (.recv (literalEncodeName location).normalize (literalEncodeTerm fields.body).normalize) with ordered | swapped
    · exact Or.inr (by rw [ordered]; rfl)
    · exact Or.inl (by rw [swapped]; rfl)

/-- A selected parsed code occurrence and the same selected physical purse
produce a real existing catalogue candidate. No collector-success premise
or redex-translation callback is assumed. -/
theorem AuthoredWholeParserFields.exact_occurrence_cover
    {location : CostName LiteralAuthority} {source : Pattern}
    {decoded : CostTerm LiteralAuthority} {bindings : Bindings}
    (fields : AuthoredWholeParserFields location source decoded bindings)
    {config : RawCostConfig} (wellFormed : config.Forall (fun term => term.wellFormed = true))
    (inputLocated : (literalEncodeName fields.inputChannel).normalize = (literalEncodeName location).normalize)
    (outputLocated : (literalEncodeName fields.outputChannel).normalize = (literalEncodeName location).normalize)
    (index : Nat)
    (occurrence : ((literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
      fields.outputChannel fields.body fields.payload fields.signature.val)).normalize, index) ∈ config.zipIdx)
    (purse : RawSelectedPurse) (purseMember : purse ∈ config.purses)
    (purseLocated : purse.location = (literalEncodeName location).normalize)
    (purseHead : purse.head = [literalAuthorityKey fields.signatureSource]) :
    ∃ cover : RawWholeOccurrenceCover config,
      cover.redex.index = index ∧
      cover.redex.location = (literalEncodeName location).normalize ∧
      cover.redex.body = (literalEncodeTerm fields.body).normalize ∧
      cover.redex.payload = (literalEncodeTerm fields.payload).normalize ∧
      cover.redex.sig = [literalAuthorityKey fields.signatureSource] ∧
      cover.source = (literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
        fields.outputChannel fields.body fields.payload fields.signature.val)).normalize ∧
      cover.selected = [purse] ∧ cover.runtimeStep ∈ runtimeCostCandidatesFromConfig config := by
  let redex : RawWholeRedex := {
    index := index
    location := (literalEncodeName location).normalize
    body := (literalEncodeTerm fields.body).normalize
    payload := (literalEncodeTerm fields.payload).normalize
    sig := [literalAuthorityKey fields.signatureSource] }
  have found : wholeAt? index
      (literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
        fields.outputChannel fields.body fields.payload fields.signature.val)).normalize = some redex := by
    rcases fields.normalized_code_shape inputLocated outputLocated with first | second
    · rw [first]
      simp [wholeAt?, redex, RawCostName.normalize_idempotent, RawCostSig.normalize,
        stableSortBy, stableInsertBy]
    · rw [second]
      simp [wholeAt?, redex, RawCostName.normalize_idempotent, RawCostSig.normalize,
        stableSortBy, stableInsertBy]
  let cover : RawWholeOccurrenceCover config := {
    redex := redex
    source := (literalEncodeTerm (twoChannelReceiverCode fields.reversed fields.inputChannel
      fields.outputChannel fields.body fields.payload fields.signature.val)).normalize
    occurrence := occurrence
    found := found
    selected := [purse]
    sourceOrdered := List.singleton_sublist.mpr purseMember
    located := by
      intro chosen member
      have same : chosen = purse := List.mem_singleton.mp member
      subst chosen
      simp only [purseLocated, redex, RawCostName.normalize_idempotent]
    exactSpend := by simp [rawSelectedSpend, purseHead, redex] }
  exact ⟨cover, rfl, rfl, rfl, rfl, rfl, rfl, rfl, cover.enabled wellFormed⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
