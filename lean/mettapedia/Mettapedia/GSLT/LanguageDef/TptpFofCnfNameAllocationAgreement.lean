import Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationLanguageDef

/-!
# Exact execution of source-indexed CNF name allocation

This module connects the three authored allocation rewrites to an independent
list function.  Execution preserves the complete source batch as an exact
subterm, preserves clause identity, order, and multiplicity, assigns a
consecutive collision-free name interval, and returns the first unused name.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationLanguageDef

namespace Allocated

abbrev EncodedClauseEntry :=
  TptpFofClausificationBatchLanguageDef.EncodedClauseEntry

abbrev AllocatedClauseEntry :=
  TptpFofCnfAllocatedBatchLanguageDef.AllocatedClauseEntry

def encodeSourceEntries : List EncodedClauseEntry → Pattern
  | [] => batchEntriesNil
  | entry :: rest =>
      batchEntriesCons (batchClauseEntry entry.identity entry.clause)
        (encodeSourceEntries rest)

def encodeAllocatedEntries :=
  TptpFofCnfAllocatedBatchLanguageDef.encodeAllocatedEntries

def allocateFrom :=
  TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom

end Allocated

local macro "name_allocation_root" : tactic =>
  `(tactic|
    simp [rewriteAt,
      TptpFofCnfNameAllocationLanguageDef.language_rewrites,
      TptpFofCnfNameAllocationLanguageDef.rewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofCnfNameAllocationLanguageDef.startRule,
      TptpFofCnfNameAllocationLanguageDef.nilRule,
      TptpFofCnfNameAllocationLanguageDef.consRule,
      TptpFofCnfNameAllocationLanguageDef.mkRule,
      TptpFofCnfNameAllocationLanguageDef.congruence,
      request, allocateEntries, batchOutput, batchEntriesNil,
      batchEntriesCons, batchClauseEntry,
      TptpFofCnfNameAllocationLanguageDef.a,
      TptpFofCnfNameAllocationLanguageDef.v,
      TptpFofCnfAllocatedBatchLanguageDef.a,
      TptpFofCnfAllocatedBatchLanguageDef.allocationResult,
      TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput,
      TptpFofCnfAllocatedBatchLanguageDef.entriesNil,
      TptpFofCnfAllocatedBatchLanguageDef.entriesCons,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local macro "name_allocation_root_using_all" : tactic =>
  `(tactic|
    simp only [request, allocateEntries, batchOutput, batchEntriesNil,
      batchEntriesCons, batchClauseEntry,
      TptpFofCnfNameAllocationLanguageDef.a,
      TptpFofCnfAllocatedBatchLanguageDef.a,
      TptpFofCnfAllocatedBatchLanguageDef.allocationResult,
      TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput,
      TptpFofCnfAllocatedBatchLanguageDef.entriesNil,
      TptpFofCnfAllocatedBatchLanguageDef.entriesCons] at * <;>
    simp [*, rewriteAt,
      TptpFofCnfNameAllocationLanguageDef.language_rewrites,
      TptpFofCnfNameAllocationLanguageDef.rewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofCnfNameAllocationLanguageDef.startRule,
      TptpFofCnfNameAllocationLanguageDef.nilRule,
      TptpFofCnfNameAllocationLanguageDef.consRule,
      TptpFofCnfNameAllocationLanguageDef.mkRule,
      TptpFofCnfNameAllocationLanguageDef.congruence,
      request, allocateEntries, batchOutput, batchEntriesNil,
      batchEntriesCons, batchClauseEntry,
      TptpFofCnfNameAllocationLanguageDef.a,
      TptpFofCnfNameAllocationLanguageDef.v,
      TptpFofCnfAllocatedBatchLanguageDef.a,
      TptpFofCnfAllocatedBatchLanguageDef.allocationResult,
      TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput,
      TptpFofCnfAllocatedBatchLanguageDef.entriesNil,
      TptpFofCnfAllocatedBatchLanguageDef.entriesCons,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

inductive Derivation : Pattern → Pattern → Type
  | entriesNil (firstName : Pattern) :
      Derivation (allocateEntries batchEntriesNil firstName)
        (TptpFofCnfAllocatedBatchLanguageDef.allocationResult firstName
          TptpFofCnfAllocatedBatchLanguageDef.entriesNil)
  | entriesCons {identity clause rest firstName nextName allocatedRest : Pattern}
      (tail : Derivation
        (allocateEntries rest
          (a "tptp-fof-resolved:index-succ" [firstName]))
        (TptpFofCnfAllocatedBatchLanguageDef.allocationResult nextName
          allocatedRest)) :
      Derivation
        (allocateEntries
          (batchEntriesCons (batchClauseEntry identity clause) rest)
          firstName)
        (TptpFofCnfAllocatedBatchLanguageDef.allocationResult nextName
          (TptpFofCnfAllocatedBatchLanguageDef.entriesCons
            (a "tptp-fof-cnf-allocated:clause-entry" [
              identity, a "tptp-fof-cnf-allocated:name" [firstName], clause])
            allocatedRest))
  | allocateBatch
      {occurrence polarity skolem cnf entries firstName nextName allocated :
        Pattern}
      (entriesDerivation : Derivation
        (allocateEntries entries firstName)
        (TptpFofCnfAllocatedBatchLanguageDef.allocationResult nextName
          allocated)) :
      Derivation
        (request (batchOutput occurrence polarity skolem cnf entries)
          firstName)
        (TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput
          (batchOutput occurrence polarity skolem cnf entries)
          firstName nextName allocated)

def Derivation.height : {source target : Pattern} →
    Derivation source target → Nat
  | _, _, .entriesNil _ => 1
  | _, _, .entriesCons tail
  | _, _, .allocateBatch tail => tail.height + 1

theorem entriesNil_rewriteAt_exact (firstName : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language (fuel + 1)
      (allocateEntries batchEntriesNil firstName) =
      [TptpFofCnfAllocatedBatchLanguageDef.allocationResult firstName
        TptpFofCnfAllocatedBatchLanguageDef.entriesNil] := by
  name_allocation_root

theorem entriesCons_rewriteAt_exact
    (identity clause rest firstName nextName allocatedRest : Pattern)
    (fuel : Nat)
    (tailExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofCnfNameAllocationLanguageDef.language fuel
        (allocateEntries rest
          (a "tptp-fof-resolved:index-succ" [firstName])) =
        [TptpFofCnfAllocatedBatchLanguageDef.allocationResult nextName
          allocatedRest]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language (fuel + 1)
      (allocateEntries
        (batchEntriesCons (batchClauseEntry identity clause) rest)
        firstName) =
      [TptpFofCnfAllocatedBatchLanguageDef.allocationResult nextName
        (TptpFofCnfAllocatedBatchLanguageDef.entriesCons
          (a "tptp-fof-cnf-allocated:clause-entry" [
            identity, a "tptp-fof-cnf-allocated:name" [firstName], clause])
          allocatedRest)] := by
  name_allocation_root_using_all

theorem allocateBatch_rewriteAt_exact
    (occurrence polarity skolem cnf entries firstName nextName allocated :
      Pattern)
    (fuel : Nat)
    (entriesExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofCnfNameAllocationLanguageDef.language fuel
        (allocateEntries entries firstName) =
        [TptpFofCnfAllocatedBatchLanguageDef.allocationResult nextName
          allocated]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language (fuel + 1)
      (request (batchOutput occurrence polarity skolem cnf entries)
        firstName) =
      [TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput
        (batchOutput occurrence polarity skolem cnf entries)
        firstName nextName allocated] := by
  name_allocation_root_using_all

theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language fuel source = [target] := by
  induction derivation generalizing fuel with
  | entriesNil firstName =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            entriesNil_rewriteAt_exact firstName fuel
  | entriesCons tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          simpa [Nat.succ_eq_add_one] using
            entriesCons_rewriteAt_exact _ _ _ _ _ _ fuel childExact
  | allocateBatch entriesDerivation entriesHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : entriesDerivation.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := entriesHypothesis fuel childEnough
          simpa [Nat.succ_eq_add_one] using
            allocateBatch_rewriteAt_exact _ _ _ _ _ _ _ _ fuel childExact

theorem Derivation.no_invention {source expected target : Pattern}
    (derivation : Derivation source expected) (fuel : Nat)
    (enough : derivation.height ≤ fuel)
    (membership : target ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language fuel source) :
    target = expected := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

def entriesDerivation : (firstName : Nat) →
    (entries : List Allocated.EncodedClauseEntry) →
    Derivation
      (allocateEntries (Allocated.encodeSourceEntries entries)
        (TptpResolvedFofLanguageDef.encodeNatIndex firstName))
      (TptpFofCnfAllocatedBatchLanguageDef.allocationResult
        (TptpResolvedFofLanguageDef.encodeNatIndex
          (firstName + entries.length))
        (Allocated.encodeAllocatedEntries
          (Allocated.allocateFrom firstName entries)))
  | firstName, [] => .entriesNil _
  | firstName, entry :: rest => by
      have tail := entriesDerivation (firstName + 1) rest
      have nextNameExact :
          firstName + (entry :: rest).length =
            (firstName + 1) + rest.length := by
        simp only [List.length_cons]
        omega
      rw [nextNameExact]
      simpa only [Allocated.encodeSourceEntries,
        Allocated.allocateFrom,
        TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom,
        Allocated.encodeAllocatedEntries,
        TptpFofCnfAllocatedBatchLanguageDef.encodeAllocatedEntries,
        TptpFofCnfAllocatedBatchLanguageDef.allocatedClauseEntry,
        TptpFofCnfAllocatedBatchLanguageDef.allocatedName,
        TptpFofCnfAllocatedBatchLanguageDef.entriesCons,
        TptpFofCnfAllocatedBatchLanguageDef.a,
        TptpFofCnfNameAllocationLanguageDef.a,
        TptpResolvedFofLanguageDef.encodeNatIndex] using
        Derivation.entriesCons tail

theorem entries_rewriteAt_exact (firstName : Nat)
    (entries : List Allocated.EncodedClauseEntry) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language
      (entriesDerivation firstName entries).height
      (allocateEntries (Allocated.encodeSourceEntries entries)
        (TptpResolvedFofLanguageDef.encodeNatIndex firstName)) =
      [TptpFofCnfAllocatedBatchLanguageDef.allocationResult
        (TptpResolvedFofLanguageDef.encodeNatIndex
          (firstName + entries.length))
        (Allocated.encodeAllocatedEntries
          (Allocated.allocateFrom firstName entries))] := by
  exact (entriesDerivation firstName entries).rewriteAt_exact _ (by rfl)

def outputDerivation (occurrence polarity skolem cnf : Pattern)
    (firstName : Nat) (entries : List Allocated.EncodedClauseEntry) :
    Derivation
      (request
        (batchOutput occurrence polarity skolem cnf
          (Allocated.encodeSourceEntries entries))
        (TptpResolvedFofLanguageDef.encodeNatIndex firstName))
      (TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput
        (batchOutput occurrence polarity skolem cnf
          (Allocated.encodeSourceEntries entries))
        (TptpResolvedFofLanguageDef.encodeNatIndex firstName)
        (TptpResolvedFofLanguageDef.encodeNatIndex
          (firstName + entries.length))
        (Allocated.encodeAllocatedEntries
          (Allocated.allocateFrom firstName entries))) :=
  .allocateBatch (entriesDerivation firstName entries)

theorem output_rewriteAt_exact (occurrence polarity skolem cnf : Pattern)
    (firstName : Nat) (entries : List Allocated.EncodedClauseEntry) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofCnfNameAllocationLanguageDef.language
      (outputDerivation occurrence polarity skolem cnf firstName
        entries).height
      (request
        (batchOutput occurrence polarity skolem cnf
          (Allocated.encodeSourceEntries entries))
        (TptpResolvedFofLanguageDef.encodeNatIndex firstName)) =
      [TptpFofCnfAllocatedBatchLanguageDef.allocatedOutput
        (batchOutput occurrence polarity skolem cnf
          (Allocated.encodeSourceEntries entries))
        (TptpResolvedFofLanguageDef.encodeNatIndex firstName)
        (TptpResolvedFofLanguageDef.encodeNatIndex
          (firstName + entries.length))
        (Allocated.encodeAllocatedEntries
          (Allocated.allocateFrom firstName entries))] := by
  exact (outputDerivation occurrence polarity skolem cnf firstName
    entries).rewriteAt_exact _ (by rfl)

theorem allocated_names_nodup (firstName : Nat)
    (entries : List Allocated.EncodedClauseEntry) :
    ((Allocated.allocateFrom firstName entries).map fun entry =>
      TptpFofCnfAllocatedBatchLanguageDef.allocatedName
        entry.nameIndex).Nodup :=
  TptpFofCnfAllocatedBatchLanguageDef.allocated_names_nodup firstName entries

theorem identity_order_exact (firstName : Nat)
    (entries : List Allocated.EncodedClauseEntry) :
    (Allocated.allocateFrom firstName entries).map (·.identity) =
      entries.map (·.identity) :=
  TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom_identity_order
    firstName entries

theorem clause_order_exact (firstName : Nat)
    (entries : List Allocated.EncodedClauseEntry) :
    (Allocated.allocateFrom firstName entries).map (·.clause) =
      entries.map (·.clause) :=
  TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom_clause_order
    firstName entries

theorem separate_batches_agree (firstName : Nat)
    (left right : List Allocated.EncodedClauseEntry) :
    Allocated.allocateFrom firstName (left ++ right) =
      Allocated.allocateFrom firstName left ++
        Allocated.allocateFrom (firstName + left.length) right :=
  TptpFofCnfAllocatedBatchLanguageDef.allocateEncodedEntriesFrom_append
    firstName left right

namespace Canary

def first : Allocated.EncodedClauseEntry := ⟨a "source-0", a "clause-0"⟩
def second : Allocated.EncodedClauseEntry := ⟨a "source-1", a "clause-1"⟩

theorem two_rows_receive_distinct_names :
    (Allocated.allocateFrom 5 [first, second]).map (·.nameIndex) = [5, 6] := by
  rfl

theorem swapped_identity_order_is_rejected :
    (Allocated.allocateFrom 5 [first, second]).map (·.identity) ≠
      [second.identity, first.identity] := by
  decide

end Canary

#print axioms entriesNil_rewriteAt_exact
#print axioms entriesCons_rewriteAt_exact
#print axioms allocateBatch_rewriteAt_exact
#print axioms Derivation.rewriteAt_exact
#print axioms Derivation.no_invention
#print axioms entries_rewriteAt_exact
#print axioms output_rewriteAt_exact
#print axioms allocated_names_nodup
#print axioms identity_order_exact
#print axioms clause_order_exact
#print axioms separate_batches_agree
#print axioms Canary.two_rows_receive_distinct_names
#print axioms Canary.swapped_identity_order_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofCnfNameAllocationAgreement
