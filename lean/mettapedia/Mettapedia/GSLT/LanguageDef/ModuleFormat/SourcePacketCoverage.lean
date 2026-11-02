import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketEncoding

/-! Every compiled source derivation has a packet accepted by the existing
certificate proposer. The statement preserves the physical production and
all ordered child certificates. It does not assume native enumeration. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage

open Mettapedia.GSLT.Parsing
open ParserProfileSemantics PresentationExprSemantics ClassAwareParserPackCorrespondence
open ClassAwareParserPackCertificate SourcePacket SourcePacketCertificate SourcePacketEncoding

private theorem children_nodes (values : List Packet) :
    packetNodes.listNodes values < packetNodes (children values) := by
  induction values with
  | nil => decide
  | cons first rest ih =>
    simp only [children, packetNodes, packetNodes.listNodes] at *
    omega

private theorem structural_nodes (label : String) (values : List Packet) :
    packetNodes.listNodes values < packetNodes (structural label values) := by
  have bound := children_nodes values
  simp only [structural, packetNodes, packetNodes.listNodes]
  omega

mutual
  theorem propose_derivation {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      (formed : Profile plan) {input : List Nat} {sort : String} {start stop : Nat} {tree : CST}
      (derivation : ParserPackDerivesAt profile plan input sort start stop tree)
      (fuel : Nat) (enough : packetNodes (encode tree) < fuel) :
      proposeFuel plan input fuel sort start (encode tree) =
        some (stop, Certificate.ofDerivation derivation) :=
    match derivation with
    | .lexical position valid matcherExact sortExact labelExact matched => by
      cases fuel with
      | zero => omega
      | succ fuel =>
        obtain ⟨matched, output⟩ := matched
        subst sortExact
        subst labelExact
        subst output
        have consumes := formed.lexicalConsumes ⟨position, valid⟩
        rw [matcherExact] at consumes
        cases matched with
        | eof => exact False.elim (consumes rfl)
        | any lookup =>
          simpa only [encode, TerminalMatchesAt.cst, Certificate.ofDerivation, matcherExact] using
            propose_lexical plan input formed ⟨position, valid⟩ _ _ fuel lookup
        | char lookup =>
          simpa only [encode, TerminalMatchesAt.cst, Certificate.ofDerivation, matcherExact] using
            propose_lexical plan input formed ⟨position, valid⟩ _ _ fuel lookup
        | classMember lookup _ =>
          simpa only [encode, TerminalMatchesAt.cst, Certificate.ofDerivation, matcherExact] using
            propose_lexical plan input formed ⟨position, valid⟩ _ _ fuel lookup
    | .structural position valid sortExact labelExact body => by
      cases fuel with
      | zero => omega
      | succ fuel =>
        simp only [Certificate.ofDerivation]
        rw [encode_structural _ _ _ _ (items_are_nodes body)] at enough ⊢
        rw [← sortExact, ← labelExact, propose_structural plan input formed ⟨position, valid⟩]
        have completed := propose_items formed body fuel (by
          exact Nat.lt_of_lt_of_le (structural_nodes _ _) (Nat.le_of_lt_succ enough)) []
        simp only [List.append_nil] at completed
        rw [completed]
        rfl
    termination_by structural derivation

  theorem propose_items {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
      (formed : Profile plan) {input : List Nat} {items : List PackItem} {start stop : Nat} {values : List CST}
      (derivation : ParserPackItemsDeriveAt profile plan input items start stop values)
      (fuel : Nat) (enough : packetNodes.listNodes (encodeList values) < fuel) (tail : List Packet) :
      proposeItemsFuel plan input fuel items start (encodeList values ++ tail) =
        some (stop, ItemsCertificate.ofDerivation derivation, tail) :=
    match derivation with
    | .nil => by simp only [encodeList, List.nil_append, propose_items_nil, ItemsCertificate.ofDerivation]
    | .terminal matched rest => by
      rw [propose_items_terminal plan input fuel _ matched]
      rw [propose_items formed rest fuel enough tail]
      rfl
    | .nonterminal head rest => by
      simp only [encodeList, packetNodes.listNodes] at enough
      simp only [encodeList, List.cons_append, propose_items_nonterminal]
      rw [propose_derivation formed head fuel (by omega)]
      dsimp only [Bind.bind, Option.bind]
      rw [propose_items formed rest fuel (by omega) tail]
      rfl
    termination_by structural derivation
end

theorem propose_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    (formed : Profile plan) {input : List Nat} {sort : String} {tree : CST}
    (derivation : ParserPackDerivesAt profile plan input sort 0 input.length tree) :
    propose? plan input sort (encode tree) = some (Certificate.ofDerivation derivation) := by
  unfold propose?
  rw [propose_derivation formed derivation _ (Nat.lt_succ_self _)]
  simp

open ScalarSyntaxCore

/-- Replaying the encoded source tree reconstructs its independently
defined retained syntax core. No successful read is assumed. -/
theorem core_complete {description : Description} (parser : Parser description) (shape : Shape description)
    (formed : Profile parser.plan) {input : List Nat} {sort : String} {tree : CST}
    (source : LanguageDefScalarSyntax.DerivesAt SourceSyntaxExport.literalScalars?
      description.profile description.grammar input sort 0 input.length tree) :
    core? description parser shape input sort (encode tree) = some (reify description source) := by
  obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve parser.rulesCompiled source
  let target := preserveSourcePlanDerivation parser.agreement sourcePlan
  unfold core? readPacket?
  rw [propose_complete formed target]
  simp [readCertificate?, ClassAwareParserPackOutput.replay_exact (Replays.ofDerivation target),
    checkedTerm, lowerCST_source description shape source]

#print axioms propose_derivation
#print axioms propose_items
#print axioms propose_complete
#print axioms core_complete

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketCoverage
