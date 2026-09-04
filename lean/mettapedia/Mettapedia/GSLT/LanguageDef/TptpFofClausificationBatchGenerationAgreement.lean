import Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationLanguageDef

/-!
# Exact execution of source-indexed clausification-batch generation

This module connects the three authored batch-generation rules to an
independent inductive derivation.  The exact execution theorem proves that
the rules traverse the complete CNF clause list, preserve order and
multiplicity, and assign each clause its source occurrence plus local index.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationLanguageDef

namespace Batch

abbrev SourceOccurrence :=
  Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef.SourceOccurrence

abbrev encodeOccurrence :=
  Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef.encodeOccurrence

abbrev encodePolarity :=
  Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef.encodePolarity

noncomputable abbrev encodeClauseEntriesFrom {depth : Nat}
    (occurrence : SourceOccurrence) (localIndex : Nat)
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) : Pattern :=
  Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef.encodeClauseEntriesFrom
    occurrence localIndex clauses

noncomputable abbrev encodeClauseEntries {depth : Nat}
    (occurrence : SourceOccurrence)
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) : Pattern :=
  Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef.encodeClauseEntries
    occurrence clauses

noncomputable abbrev encodeOutput {depth : Nat}
    (occurrence : SourceOccurrence) (polarity : Bool)
    (skolem : TptpFofSkolemizationSemantics.Output 0)
    (skolemFree :
      TptpFofSkolemizationSemantics.ExistentialFree skolem.formula)
    (named : TptpFofDefinitionalNamingSemantics.Output depth)
    (quantifierFree : ∀ definition ∈ named.definitions,
      TptpFofDefinitionalNamingSemantics.QuantifierFree definition.source) :
    Pattern :=
  Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchLanguageDef.encodeOutput
    occurrence polarity skolem skolemFree named quantifierFree

end Batch

local macro "batch_generation_root" : tactic =>
  `(tactic|
    simp [rewriteAt,
      TptpFofClausificationBatchGenerationLanguageDef.language_rewrites,
      TptpFofClausificationBatchGenerationLanguageDef.rewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofClausificationBatchGenerationLanguageDef.startRule,
      TptpFofClausificationBatchGenerationLanguageDef.nilRule,
      TptpFofClausificationBatchGenerationLanguageDef.consRule,
      TptpFofClausificationBatchGenerationLanguageDef.mkRule,
      TptpFofClausificationBatchGenerationLanguageDef.congruence,
      request, indexEntries,
      TptpFofClausificationBatchGenerationLanguageDef.a,
      TptpFofClausificationBatchGenerationLanguageDef.v,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local macro "batch_generation_root_using_all" : tactic =>
  `(tactic|
    simp only [request, indexEntries,
      TptpFofClausificationBatchGenerationLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.a] at * <;>
    simp [*, rewriteAt,
      TptpFofClausificationBatchGenerationLanguageDef.language_rewrites,
      TptpFofClausificationBatchGenerationLanguageDef.rewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofClausificationBatchGenerationLanguageDef.startRule,
      TptpFofClausificationBatchGenerationLanguageDef.nilRule,
      TptpFofClausificationBatchGenerationLanguageDef.consRule,
      TptpFofClausificationBatchGenerationLanguageDef.mkRule,
      TptpFofClausificationBatchGenerationLanguageDef.congruence,
      request, indexEntries,
      TptpFofClausificationBatchGenerationLanguageDef.a,
      TptpFofClausificationBatchGenerationLanguageDef.v,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

inductive Derivation : Pattern → Pattern → Type
  | entriesNil (occurrence localIndex : Pattern) :
      Derivation
        (indexEntries occurrence localIndex
          TptpFofDefinitionalCnfLanguageDef.clausesNil)
        (a "tptp-fof-batch:entries-nil")
  | entriesCons {occurrence localIndex clause clauses entries : Pattern}
      (tail : Derivation
        (indexEntries occurrence
          (a "tptp-fof-resolved:index-succ" [localIndex]) clauses)
        entries) :
      Derivation
        (indexEntries occurrence localIndex
          (TptpFofDefinitionalCnfLanguageDef.clausesCons clause clauses))
        (a "tptp-fof-batch:entries-cons" [
          a "tptp-fof-batch:clause-entry" [
            a "tptp-fof-batch:clause-id" [occurrence, localIndex], clause],
          entries])
  | generate {occurrence polarity skolem named clauses entries : Pattern}
      (entriesDerivation : Derivation
        (indexEntries occurrence (a "tptp-fof-resolved:index-zero") clauses)
        entries) :
      Derivation
        (request occurrence polarity skolem
          (TptpFofDefinitionalCnfLanguageDef.cnfOutput named clauses))
        (a "tptp-fof-batch:output" [occurrence, polarity, skolem,
          TptpFofDefinitionalCnfLanguageDef.cnfOutput named clauses,
          entries])

def Derivation.height : {source target : Pattern} →
    Derivation source target → Nat
  | _, _, .entriesNil _ _ => 1
  | _, _, .entriesCons tail
  | _, _, .generate tail => tail.height + 1

theorem entriesNil_rewriteAt_exact (occurrence localIndex : Pattern)
    (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language (fuel + 1)
      (indexEntries occurrence localIndex
        TptpFofDefinitionalCnfLanguageDef.clausesNil) =
      [a "tptp-fof-batch:entries-nil"] := by
  batch_generation_root

theorem entriesCons_rewriteAt_exact
    (occurrence localIndex clause clauses entries : Pattern) (fuel : Nat)
    (tailExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofClausificationBatchGenerationLanguageDef.language fuel
        (indexEntries occurrence
          (a "tptp-fof-resolved:index-succ" [localIndex]) clauses) =
        [entries]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language (fuel + 1)
      (indexEntries occurrence localIndex
        (TptpFofDefinitionalCnfLanguageDef.clausesCons clause clauses)) =
      [a "tptp-fof-batch:entries-cons" [
        a "tptp-fof-batch:clause-entry" [
          a "tptp-fof-batch:clause-id" [occurrence, localIndex], clause],
        entries]] := by
  batch_generation_root_using_all

theorem generate_rewriteAt_exact
    (occurrence polarity skolem named clauses entries : Pattern) (fuel : Nat)
    (entriesExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofClausificationBatchGenerationLanguageDef.language fuel
        (indexEntries occurrence (a "tptp-fof-resolved:index-zero") clauses) =
        [entries]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language (fuel + 1)
      (request occurrence polarity skolem
        (TptpFofDefinitionalCnfLanguageDef.cnfOutput named clauses)) =
      [a "tptp-fof-batch:output" [occurrence, polarity, skolem,
        TptpFofDefinitionalCnfLanguageDef.cnfOutput named clauses,
        entries]] := by
  batch_generation_root_using_all

theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language fuel source =
        [target] := by
  induction derivation generalizing fuel with
  | entriesNil occurrence localIndex =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            entriesNil_rewriteAt_exact occurrence localIndex fuel
  | entriesCons tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          simpa [Nat.succ_eq_add_one] using
            entriesCons_rewriteAt_exact _ _ _ _ _ fuel childExact
  | generate entriesDerivation entriesHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : entriesDerivation.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := entriesHypothesis fuel childEnough
          simpa [Nat.succ_eq_add_one] using
            generate_rewriteAt_exact _ _ _ _ _ _ fuel childExact

theorem Derivation.no_invention {source expected target : Pattern}
    (derivation : Derivation source expected) (fuel : Nat)
    (enough : derivation.height ≤ fuel)
    (membership : target ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language fuel source) :
    target = expected := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

noncomputable def clauseEntriesDerivation
    {depth : Nat} (occurrence : Batch.SourceOccurrence) :
    (localIndex : Nat) →
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) →
    Derivation
      (indexEntries (Batch.encodeOccurrence occurrence)
        (TptpResolvedFofLanguageDef.encodeNatIndex localIndex)
        (TptpFofDefinitionalCnfLanguageDef.encodeClauses clauses))
      (Batch.encodeClauseEntriesFrom occurrence localIndex clauses)
  | _, [] => .entriesNil _ _
  | localIndex, _ :: clauses =>
      .entriesCons (clauseEntriesDerivation occurrence (localIndex + 1) clauses)

theorem clauseEntries_rewriteAt_exact
    {depth : Nat} (occurrence : Batch.SourceOccurrence)
    (clauses : List (TptpFofDefinitionalCnfSemantics.Clause depth)) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language
      (clauseEntriesDerivation occurrence 0 clauses).height
      (indexEntries (Batch.encodeOccurrence occurrence)
        (TptpResolvedFofLanguageDef.encodeNatIndex 0)
        (TptpFofDefinitionalCnfLanguageDef.encodeClauses clauses)) =
      [Batch.encodeClauseEntries occurrence clauses] := by
  exact (clauseEntriesDerivation occurrence 0 clauses).rewriteAt_exact _
    (by rfl)

noncomputable def outputDerivation
    {depth : Nat} (occurrence : Batch.SourceOccurrence) (polarity : Bool)
    (skolem : TptpFofSkolemizationSemantics.Output 0)
    (skolemFree :
      TptpFofSkolemizationSemantics.ExistentialFree skolem.formula)
    (named : TptpFofDefinitionalNamingSemantics.Output depth)
    (quantifierFree : ∀ definition ∈ named.definitions,
      TptpFofDefinitionalNamingSemantics.QuantifierFree definition.source) :
    Derivation
      (request (Batch.encodeOccurrence occurrence)
        (Batch.encodePolarity polarity)
        (TptpFofSkolemLanguageDef.encodeOutput skolem skolemFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput named
          quantifierFree))
      (Batch.encodeOutput occurrence polarity skolem skolemFree named
        quantifierFree) := by
  unfold Batch.encodeOutput
  exact .generate
    (clauseEntriesDerivation occurrence 0
      (TptpFofDefinitionalCnfSemantics.clausesForOutput named))

theorem output_rewriteAt_exact
    {depth : Nat} (occurrence : Batch.SourceOccurrence) (polarity : Bool)
    (skolem : TptpFofSkolemizationSemantics.Output 0)
    (skolemFree :
      TptpFofSkolemizationSemantics.ExistentialFree skolem.formula)
    (named : TptpFofDefinitionalNamingSemantics.Output depth)
    (quantifierFree : ∀ definition ∈ named.definitions,
      TptpFofDefinitionalNamingSemantics.QuantifierFree definition.source) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofClausificationBatchGenerationLanguageDef.language
      (outputDerivation occurrence polarity skolem skolemFree named
        quantifierFree).height
      (request (Batch.encodeOccurrence occurrence)
        (Batch.encodePolarity polarity)
        (TptpFofSkolemLanguageDef.encodeOutput skolem skolemFree)
        (TptpFofDefinitionalCnfLanguageDef.encodeCnfOutput named
          quantifierFree)) =
      [Batch.encodeOutput occurrence polarity skolem skolemFree named
        quantifierFree] := by
  exact (outputDerivation occurrence polarity skolem skolemFree named
    quantifierFree).rewriteAt_exact _ (by rfl)

#print axioms entriesNil_rewriteAt_exact
#print axioms entriesCons_rewriteAt_exact
#print axioms generate_rewriteAt_exact
#print axioms Derivation.rewriteAt_exact
#print axioms Derivation.no_invention
#print axioms clauseEntries_rewriteAt_exact
#print axioms output_rewriteAt_exact

end Mettapedia.GSLT.LanguageDef.TptpFofClausificationBatchGenerationAgreement
