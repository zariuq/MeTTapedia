import Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.ComputablePatternFactorOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.RuleScopedInertScheduling

/-!
# Draining obsolete compressed-lookup probes after assertion launch

The physical assertion launcher consumes the compact pending row and the heap
lookup row.  The older proof, assertion, fault, and cursor-advance probes remain
as executable shells, but each requires one of those two predecessor families.
This module derives their matcher emptiness from the row-family invariant rather
than evaluating a closed workspace.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalAssertionBridgeSchedule
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- The compatible-pattern projection used only after proving that a concrete
directive really has compatible input. -/
private def compatibleInputPattern (directive : SourceExecFact) : Pattern :=
  match directive.rule.input with
  | .compat pattern => pattern
  | .explicit _ => mkPattern []

private theorem compressedProofStepDirective_input_compat :
    compressedProofStepDirective.rule.input =
      .compat (compatibleInputPattern compressedProofStepDirective) := by
  rfl

private theorem compressedProofStepDirective_pending_mem :
    directAssertionPendingTemplate ∈
      (compatibleInputPattern compressedProofStepDirective).atoms := by
  decide +kernel

private theorem decoratedCursorAssertionDirective_input_compat :
    decoratedCursorAssertionDirective.rule.input =
      .compat (compatibleInputPattern decoratedCursorAssertionDirective) := by
  decide +kernel

private theorem decoratedCursorAssertionDirective_pending_mem :
    directAssertionPendingTemplate ∈
      (compatibleInputPattern decoratedCursorAssertionDirective).atoms := by
  decide +kernel

private theorem compressedHeapLookupFaultDirective_input_compat :
    compressedHeapLookupFaultDirective.rule.input =
      .compat (compatibleInputPattern compressedHeapLookupFaultDirective) := by
  rfl

private theorem compressedHeapLookupFaultDirective_pending_mem :
    directAssertionPendingTemplate ∈
      (compatibleInputPattern compressedHeapLookupFaultDirective).atoms := by
  decide +kernel

private theorem compressedHeapLookupAdvanceDirective_input_compat :
    compressedHeapLookupAdvanceDirective.rule.input =
      .compat (compatibleInputPattern compressedHeapLookupAdvanceDirective) := by
  rfl

/-- The retained cursor machine uses its own variable spelling, while sharing
the same fixed lookup-row head as the direct assertion probe. -/
private def cursorHeapLookupTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "heap-lookup-cursor"]

private theorem compressedHeapLookupAdvanceDirective_lookup_mem :
    cursorHeapLookupTemplate ∈
      (compatibleInputPattern compressedHeapLookupAdvanceDirective).atoms := by
  decide +kernel

/-- Absence of a fixed expression head makes that pattern factor impossible
under every incoming substitution. -/
private theorem cmatchAtom_fixed_head_eq_none_of_absent
    (space : List Atom) (patternHead : String) (patternTail : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠ some patternHead)
    (substitution : Subst) (carrier : Atom) (member : carrier ∈ space) :
    cmatchAtom substitution
        (.expression (.symbol patternHead :: patternTail)) carrier = none := by
  cases carrier with
  | grounded value => rfl
  | symbol value => rfl
  | «var» value => rfl
  | expression atoms =>
      cases atoms with
      | nil => rfl
      | cons head tail =>
          cases head with
          | grounded value => rfl
          | «var» value => rfl
          | expression value => rfl
          | symbol concreteHead =>
              by_cases equal : patternHead = concreteHead
              · subst concreteHead
                exact (absent
                  (.expression (.symbol patternHead :: tail)) member rfl).elim
              · exact cmatchAtom_expression_symbol_head_ne substitution
                  patternHead concreteHead patternTail tail equal

/-- Inserting the selected executable shell for matching preserves absence of
both predecessor data heads. -/
private theorem predecessor_heads_absent_in_read
    (space : List Atom) (directive : SourceExecFact)
    (decoded : extractSupportedSourceExecFact directive.atom = some directive)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    ∀ atom ∈ morkInsertSupport
        (morkEraseSupport space directive.atom) directive.atom,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup" := by
  intro atom member
  rcases mem_morkInsertSupport_cases member with live | rfl
  · exact absent atom (List.mem_of_mem_filter live)
  · constructor
    · intro pending
      obtain ⟨tail, shape⟩ :=
        (compressedDynamicRowHead?_eq_some_iff directive.atom
          "mm-compressed-step-pending").mp pending
      exact (supportedExecAtom_ne_expression_head decoded
        "mm-compressed-step-pending" tail (by decide) shape).elim
    · intro lookup
      obtain ⟨tail, shape⟩ :=
        (compressedDynamicRowHead?_eq_some_iff directive.atom
          "mm-compressed-heap-lookup").mp lookup
      exact (supportedExecAtom_ne_expression_head decoded
        "mm-compressed-heap-lookup" tail (by decide) shape).elim

/-- A compatible input containing one impossible factor has no complete
matcher row. -/
private theorem cmatchInputSpec_eq_nil_of_factor_absent
    (space : List Atom) (pattern : Pattern) (factor : Atom)
    (factorMember : factor ∈ pattern.atoms)
    (neverMatches : ∀ substitution carrier, carrier ∈ space →
      cmatchAtom substitution factor carrier = none) :
    cmatchInputSpec [] space (.compat pattern) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro result resultMember
  have projected : result.1 ∈
      (cmatchInputSpec [] space (.compat pattern)).map Prod.fst :=
    List.mem_map_of_mem resultMember
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, matched,
      _extension, _replay⟩ :=
    cmatchInputSpec_compat_factor_match_origin space pattern factor
      factorMember projected
  rw [neverMatches beforeFactor carrier carrierMember] at matched
  contradiction

/-- The retained proof-cell probe cannot match after assertion launch because
its pending-row premise has no carrier. -/
theorem compressedProofStep_no_matches_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cMatchInputSpecMork []
        (morkInsertSupport
          (morkEraseSupport space compressedProofStepDirective.atom)
          compressedProofStepDirective.atom)
        compressedProofStepDirective.rule.input = [] := by
  rw [compressedProofStepDirective_input_compat]
  apply cmatchInputSpec_eq_nil_of_factor_absent _ _
    directAssertionPendingTemplate
    compressedProofStepDirective_pending_mem
  intro substitution carrier member
  apply cmatchAtom_fixed_head_eq_none_of_absent _
    "mm-compressed-step-pending" _ _ substitution carrier member
  exact fun atom atomMember =>
    (predecessor_heads_absent_in_read space compressedProofStepDirective
      extract_compressedProofStepRule_exact absent atom atomMember).1

/-- The retained cursor assertion probe has the same pending-row prerequisite,
even though its lookup cursor is more specific than the direct probe. -/
theorem decoratedCursorAssertion_no_matches_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cMatchInputSpecMork []
        (morkInsertSupport
          (morkEraseSupport space decoratedCursorAssertionDirective.atom)
          decoratedCursorAssertionDirective.atom)
        decoratedCursorAssertionDirective.rule.input = [] := by
  rw [decoratedCursorAssertionDirective_input_compat]
  apply cmatchInputSpec_eq_nil_of_factor_absent _ _
    directAssertionPendingTemplate
    decoratedCursorAssertionDirective_pending_mem
  intro substitution carrier member
  apply cmatchAtom_fixed_head_eq_none_of_absent _
    "mm-compressed-step-pending" _ _ substitution carrier member
  have decoded :
      extractSupportedSourceExecFact decoratedCursorAssertionDirective.atom =
        some decoratedCursorAssertionDirective := by
    rw [decoratedCursorAssertionDirective_atom_exact]
    exact extract_decoratedCursorAssertionRule_exact
  exact fun atom atomMember =>
    (predecessor_heads_absent_in_read space decoratedCursorAssertionDirective
      decoded absent atom atomMember).1

/-- The retained missing-reference probe cannot match after assertion launch
because it also requires a pending compact step. -/
theorem compressedHeapLookupFault_no_matches_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cMatchInputSpecMork []
        (morkInsertSupport
          (morkEraseSupport space compressedHeapLookupFaultDirective.atom)
          compressedHeapLookupFaultDirective.atom)
        compressedHeapLookupFaultDirective.rule.input = [] := by
  rw [compressedHeapLookupFaultDirective_input_compat]
  apply cmatchInputSpec_eq_nil_of_factor_absent _ _
    directAssertionPendingTemplate
    compressedHeapLookupFaultDirective_pending_mem
  intro substitution carrier member
  apply cmatchAtom_fixed_head_eq_none_of_absent _
    "mm-compressed-step-pending" _ _ substitution carrier member
  exact fun atom atomMember =>
    (predecessor_heads_absent_in_read space compressedHeapLookupFaultDirective
      extract_compressedHeapLookupFaultRule_exact absent atom atomMember).1

/-- The retained cursor-advance probe cannot match after assertion launch
because every heap-lookup row has been consumed. -/
theorem compressedHeapLookupAdvance_no_matches_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cMatchInputSpecMork []
        (morkInsertSupport
          (morkEraseSupport space compressedHeapLookupAdvanceDirective.atom)
          compressedHeapLookupAdvanceDirective.atom)
        compressedHeapLookupAdvanceDirective.rule.input = [] := by
  rw [compressedHeapLookupAdvanceDirective_input_compat]
  apply cmatchInputSpec_eq_nil_of_factor_absent _ _
    cursorHeapLookupTemplate
    compressedHeapLookupAdvanceDirective_lookup_mem
  intro substitution carrier member
  apply cmatchAtom_fixed_head_eq_none_of_absent _
    "mm-compressed-heap-lookup" _ _ substitution carrier member
  exact fun atom atomMember =>
    (predecessor_heads_absent_in_read space compressedHeapLookupAdvanceDirective
      extract_compressedHeapLookupAdvanceRule_exact absent atom atomMember).2

/-- Any inert rule-scoped firing preserves predecessor-head absence because
its result is a physical sub-support of the input. -/
theorem predecessor_heads_absent_after_ruleScoped_no_match
    (space : List Atom) (directive : SourceExecFact)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup")
    (noMatches :
      (cMatchInputSpecMork []
        (morkInsertSupport (morkEraseSupport space directive.atom)
          directive.atom) directive.rule.input).filter
          (fun (substitution, _) =>
            matchSourceGuards substitution directive.rule.guards) = []) :
    ∀ atom ∈ cFireRuleScopedSourceExecFact space directive,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup" := by
  rw [cFireRuleScopedSourceExecFact_eq_erase_of_no_matches space directive
    noMatches]
  intro atom member
  exact absent atom (List.mem_of_mem_filter member)

theorem compressedProofStep_drains_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cFireRuleScopedSourceExecFact space compressedProofStepDirective =
      morkEraseSupport space compressedProofStepDirective.atom := by
  apply cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
  exact ruleScoped_guarded_no_matches_of_matcher_nil space
    compressedProofStepDirective
    (compressedProofStep_no_matches_of_no_predecessor_heads space absent)

theorem decoratedCursorAssertion_drains_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cFireRuleScopedSourceExecFact space decoratedCursorAssertionDirective =
      morkEraseSupport space decoratedCursorAssertionDirective.atom := by
  apply cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
  exact ruleScoped_guarded_no_matches_of_matcher_nil space
    decoratedCursorAssertionDirective
    (decoratedCursorAssertion_no_matches_of_no_predecessor_heads space absent)

theorem compressedHeapLookupFault_drains_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cFireRuleScopedSourceExecFact space compressedHeapLookupFaultDirective =
      morkEraseSupport space compressedHeapLookupFaultDirective.atom := by
  apply cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
  exact ruleScoped_guarded_no_matches_of_matcher_nil space
    compressedHeapLookupFaultDirective
    (compressedHeapLookupFault_no_matches_of_no_predecessor_heads space absent)

theorem compressedHeapLookupAdvance_drains_of_no_predecessor_heads
    (space : List Atom)
    (absent : ∀ atom ∈ space,
      compressedDynamicRowHead? atom ≠
          some "mm-compressed-step-pending" ∧
        compressedDynamicRowHead? atom ≠
          some "mm-compressed-heap-lookup") :
    cFireRuleScopedSourceExecFact space compressedHeapLookupAdvanceDirective =
      morkEraseSupport space compressedHeapLookupAdvanceDirective.atom := by
  apply cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
  exact ruleScoped_guarded_no_matches_of_matcher_nil space
    compressedHeapLookupAdvanceDirective
    (compressedHeapLookupAdvance_no_matches_of_no_predecessor_heads space absent)

#print axioms cmatchAtom_fixed_head_eq_none_of_absent
#print axioms predecessor_heads_absent_in_read
#print axioms cmatchInputSpec_eq_nil_of_factor_absent
#print axioms compressedProofStep_no_matches_of_no_predecessor_heads
#print axioms decoratedCursorAssertion_no_matches_of_no_predecessor_heads
#print axioms compressedHeapLookupFault_no_matches_of_no_predecessor_heads
#print axioms compressedHeapLookupAdvance_no_matches_of_no_predecessor_heads
#print axioms predecessor_heads_absent_after_ruleScoped_no_match
#print axioms compressedProofStep_drains_of_no_predecessor_heads
#print axioms decoratedCursorAssertion_drains_of_no_predecessor_heads
#print axioms compressedHeapLookupFault_drains_of_no_predecessor_heads
#print axioms compressedHeapLookupAdvance_drains_of_no_predecessor_heads

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionBridgeDrain
